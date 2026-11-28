use super::primitives::*;
use super::reasoning::*;
use super::resource_tracker::cell_source::*;
use crate::kernel::{BitvectorUnaryOp, MachineCastSpelling, cast_term};
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{ExecutionFactSource, ExecutionValue};
use crate::kernel::{bits32_constant, int64_constant, native_constant, uint64_constant};
use std::collections::BTreeSet;

/// Results retained from the actual selected read query, never reconstructed
/// by the terminal renderer under a different arena or assumption context.
#[derive(Clone)]
pub(crate) struct ReadResolutionDiagnostic {
    pub read: OldMachineTerm,
    pub producer: SharedMemory,
    pub stopped_at: Option<SharedMemory>,
    pub reason: &'static str,
    pub recovered: Option<ProgramValue>,
    pub expected: OldMachineTerm,
    pub equal: bool,
}

thread_local! {
    static READ_RESOLUTION_DIAGNOSTICS: std::cell::RefCell<Option<Vec<ReadResolutionDiagnostic>>> = const { std::cell::RefCell::new(None) };
}

/// Capture only a written check's queries. Nesting and unwinding restore the
/// caller's collector; ordinary graph queries retain no diagnostic history.
pub(crate) fn capture_read_resolutions<T>(
    run: impl FnOnce() -> T,
) -> (T, Vec<ReadResolutionDiagnostic>) {
    struct Restore(Option<Vec<ReadResolutionDiagnostic>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            READ_RESOLUTION_DIAGNOSTICS.with(|slot| *slot.borrow_mut() = self.0.take());
        }
    }
    let _restore = Restore(READ_RESOLUTION_DIAGNOSTICS.with(|slot| slot.replace(Some(Vec::new()))));
    let result = run();
    let diagnostics =
        READ_RESOLUTION_DIAGNOSTICS.with(|slot| slot.borrow_mut().take().unwrap_or_default());
    (result, diagnostics)
}

/// A walk actually performed during an explicit transport check. These records
/// describe queries, not additional premises or a guess at a missing fact.
#[derive(Clone, Eq, PartialEq, Hash)]
pub(crate) struct TransportCellWalkDiagnostic {
    pub start: SharedMemory,
    pub pointer: Address,
    pub bytes: u32,
    pub stopped_at: SharedMemory,
    pub reason: &'static str,
    pub crossed: usize,
    pub extended: bool,
    pub explicit: bool,
}

#[derive(Default)]
struct TransportCellWalkDiagnostics {
    seen: std::collections::HashSet<TransportCellWalkDiagnostic>,
    walks: Vec<TransportCellWalkDiagnostic>,
    limit: Option<usize>,
}

thread_local! {
    static TRANSPORT_CELL_WALKS: std::cell::RefCell<Option<TransportCellWalkDiagnostics>> = const { std::cell::RefCell::new(None) };
}

pub(crate) fn with_transport_cell_walk_diagnostics<T>(run: impl FnOnce() -> T) -> T {
    struct Restore(Option<TransportCellWalkDiagnostics>);
    impl Drop for Restore {
        fn drop(&mut self) {
            TRANSPORT_CELL_WALKS.with(|slot| *slot.borrow_mut() = self.0.take());
        }
    }
    let _restore =
        Restore(TRANSPORT_CELL_WALKS.with(|slot| slot.replace(Some(Default::default()))));
    run()
}

/// Written smart checks retain a bounded sample without changing query behavior.
pub(crate) fn with_bounded_cell_walk_diagnostics<T>(run: impl FnOnce() -> T) -> T {
    with_transport_cell_walk_diagnostics(|| {
        TRANSPORT_CELL_WALKS.with(|slot| slot.borrow_mut().as_mut().unwrap().limit = Some(16));
        run()
    })
}

/// The cell walks `run` performs, up to `limit`, for a trace of one checked
/// step. An enclosing capture still receives them, within its own limit, as
/// if it had recorded them itself, so a written check's observations do not
/// change because a trace is on. Diagnostic only: no query changes.
pub(crate) fn capture_step_cell_walks<T>(
    limit: usize,
    run: impl FnOnce() -> T,
) -> (T, Vec<TransportCellWalkDiagnostic>) {
    let (result, walks) = with_transport_cell_walk_diagnostics(|| {
        TRANSPORT_CELL_WALKS.with(|slot| slot.borrow_mut().as_mut().unwrap().limit = Some(limit));
        let result = run();
        (result, take_transport_cell_walk_diagnostics())
    });
    TRANSPORT_CELL_WALKS.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(outer) = slot.as_mut() else {
            return;
        };
        for walk in &walks {
            if outer.limit.is_some_and(|limit| outer.walks.len() >= limit) {
                break;
            }
            if outer.seen.insert(walk.clone()) {
                outer.walks.push(walk.clone());
            }
        }
    });
    (result, walks)
}

pub(crate) fn take_transport_cell_walk_diagnostics() -> Vec<TransportCellWalkDiagnostic> {
    TRANSPORT_CELL_WALKS.with(|slot| {
        slot.borrow_mut()
            .take()
            .map(|capture| capture.walks)
            .unwrap_or_default()
    })
}

pub(in crate::kernel) fn record_transport_cell_walk(
    memory: &SharedMemory,
    pointer: &Address,
    bytes: u32,
    cell: &MemoryDagCell,
    stop: CellWalkStop,
    max_hops: Option<usize>,
) {
    TRANSPORT_CELL_WALKS.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else {
            return;
        };
        if capture
            .limit
            .is_some_and(|limit| capture.walks.len() >= limit)
        {
            return;
        }
        let crossed = match cell {
            MemoryDagCell::Stored { path, .. } | MemoryDagCell::Unwritten { path, .. } => {
                path.len()
            }
        };
        let reason = if max_hops.is_some_and(|limit| crossed >= limit) {
            "hop limit reached"
        } else {
            match stop {
                CellWalkStop::CommonState => "common state reached",
                CellWalkStop::RetainedValue => "retained typed value before cache forgetting",
                CellWalkStop::OldestRecorded => "oldest recorded state reached",
                CellWalkStop::Affected => "step affects the queried bytes",
                CellWalkStop::NotShownSeparate => "step not proved separate from the queried bytes",
            }
        };
        let diagnostic = TransportCellWalkDiagnostic {
            start: memory.clone(),
            pointer: pointer.clone(),
            bytes,
            stopped_at: cell.node().clone(),
            reason,
            crossed,
            extended: extended_dag_bridging_active(),
            explicit: explicit_dag_check_active(),
        };
        if capture.seen.insert(diagnostic.clone()) {
            capture.walks.push(diagnostic);
        }
    });
}

/// Resource indices are logical values. ADT indices can only be exchanged
/// using equality evidence of the same algebraic type; they are never cast
/// to C scalars or interpreted as memory authority.
pub(crate) fn resource_arguments_proven_equal(
    left: &AlgebraicValue,
    right: &AlgebraicValue,
    assumptions: &PureFactContext,
) -> bool {
    resource_field_values_proven_equal(left.into(), right.into(), assumptions)
}

pub(crate) fn resource_field_values_proven_equal(
    left: crate::kernel::ResourceFieldValue<'_>,
    right: crate::kernel::ResourceFieldValue<'_>,
    assumptions: &PureFactContext,
) -> bool {
    match (left, right) {
        (
            crate::kernel::ResourceFieldValue::Program(left),
            crate::kernel::ResourceFieldValue::Program(right),
        ) => {
            // A resource index observes an integer's numeric value. Matching
            // indices neither copies a C word nor transports its hidden record.
            program_values_proven_equal_for_memory_resolution(
                left.numeric_value(),
                right.numeric_value(),
                assumptions,
            )
        }
        (
            crate::kernel::ResourceFieldValue::Algebraic(left),
            crate::kernel::ResourceFieldValue::Algebraic(right),
        ) => {
            left.algebraic_type == right.algebraic_type
                && (left == right
                    || assumptions.proves_exact(&Proposition::Equal(
                        Term::Algebraic(left.clone().into()),
                        Term::Algebraic(right.clone().into()),
                    ))
                    || assumptions.proves_exact(&Proposition::Equal(
                        Term::Algebraic(right.clone().into()),
                        Term::Algebraic(left.clone().into()),
                    ))
                    || assumptions.decide(&OldConditionTerm::AlgebraicEqual(
                        Box::new(left.clone()),
                        Box::new(right.clone()),
                    )) == Some(true))
        }
        _ => false,
    }
}

/// [`resource_arguments_proven_equal`] for an argument of a declared
/// resource. Such a resource names the object a pointer argument designates
/// at its address. The view a cast selects bounds C accesses through that
/// pointer, which the resource's own clauses check when they are evaluated, so
/// it is not part of which instance this is. A kernel token whose identity is
/// itself bounds evidence, such as `allocation(p, n)`, keeps the complete
/// pointer comparison.
pub(crate) fn instance_field_values_proven_equal(
    left: crate::kernel::ResourceFieldValue<'_>,
    right: crate::kernel::ResourceFieldValue<'_>,
    assumptions: &PureFactContext,
) -> bool {
    if let (
        crate::kernel::ResourceFieldValue::Program(left),
        crate::kernel::ResourceFieldValue::Program(right),
    ) = (left, right)
        && let (ProgramValue::Pointer(left), ProgramValue::Pointer(right)) =
            (left.numeric_value(), right.numeric_value())
    {
        return (assumptions.pointer_provenance_match(left, right)
            || (assumptions.pointer_metadata_known_equal(left, right)
                && assumptions.provenance_equal(left.provenance(), right.provenance())))
            && crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
                left.address(),
                right.address(),
                assumptions,
            );
    }
    resource_field_values_proven_equal(left, right, assumptions)
}

pub(crate) fn canonical_program_memory_for_pointer_load(
    memory: &SymbolicMemory,
    pointer: &Address,
) -> SymbolicMemory {
    canonical_memory_for_pointer_load(memory, pointer)
}

/// Constructs the pointer-observable state used by atomic-load
/// canonicalization and retains the exact producer-known projection edge.
/// The edge is separate from the ordinary memory DAG because the interned
/// result may be shared by projections of several source states.
/// The memory a load of a value of `bytes` at `pointer`, an enum's or a
/// type parameter's, names: the
/// point the cell was last written, projected to the cell, as an integer
/// load's canonical form names its cell. Two loads of one unwritten cell at
/// different points are then one term.
pub(crate) fn canonical_value_load_memory(
    memory: &SharedMemory,
    pointer: &Address,
    bytes: impl Into<crate::kernel::AccessExtent>,
) -> SharedMemory {
    let bytes = bytes.into();
    let version = cell_version_point(memory, pointer, bytes);
    let named = canonical_projected_load_memory(version.as_ref().unwrap_or(memory), pointer);
    record_value_load_origin(memory, &named, pointer, bytes);
    named
}

pub(crate) fn canonical_projected_load_memory(
    source: &SharedMemory,
    pointer: &Address,
) -> SharedMemory {
    let projected =
        crate::kernel::intern_memory(canonical_program_memory_for_pointer_load(source, pointer));
    record_canonical_load_projection(source, &projected, pointer);
    projected
}

/// Checks whether two resource forms denote the same resource using only
/// exact facts and the bounded memory-resolution relation. This is intended
/// for certificate validation: it does not search for containment or separation.
pub(crate) fn resources_directly_match(
    left: &Resource,
    right: &Resource,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    let values_match = |left: &ProgramValue, right: &ProgramValue| match (left, right) {
        (ProgramValue::Void, ProgramValue::Void) => true,
        (ProgramValue::Int32(left), ProgramValue::Int32(right)) => {
            crate::instrumentation::measure_operation(
                "kernel",
                "resource context equality",
                "resource direct match: bitvector value",
                || int32_values_proven_equal_for_memory_resolution(left, right, assumptions),
            )
        }
        (ProgramValue::UInt8(left), ProgramValue::UInt8(right)) => {
            crate::instrumentation::measure_operation(
                "kernel",
                "resource context equality",
                "resource direct match: bitvector value",
                || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions),
            )
        }
        (ProgramValue::Int8(left), ProgramValue::Int8(right)) => {
            crate::instrumentation::measure_operation(
                "kernel",
                "resource context equality",
                "resource direct match: bitvector value",
                || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions),
            )
        }
        (ProgramValue::Int16(left), ProgramValue::Int16(right))
        | (ProgramValue::UInt16(left), ProgramValue::UInt16(right)) => {
            crate::instrumentation::measure_operation(
                "kernel",
                "resource context equality",
                "resource direct match: bitvector value",
                || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions),
            )
        }
        (ProgramValue::Pointer(left), ProgramValue::Pointer(right)) => {
            crate::instrumentation::measure_operation(
                "kernel",
                "resource context equality",
                "resource direct match: pointer value",
                || {
                    assumptions.pointer_provenance_match(left, right)
                        && pointers_match_for_resource_check(left, right, assumptions)
                },
            )
        }
        _ => false,
    };
    match (left, right) {
        (Resource::Memory(left), Resource::Memory(right)) => {
            left == right
                || (((!left.typed_carrier
                    || assumptions.access_provenance_matches_range(
                        left.access_provenance(),
                        left,
                        right,
                    ))
                    && (!right.typed_carrier
                        || assumptions.access_provenance_matches_range(
                            right.access_provenance(),
                            right,
                            left,
                        )))
                    && crate::instrumentation::measure_operation(
                        "kernel",
                        "resource context equality",
                        "resource memory match: width",
                        || left.element_width() == right.element_width(),
                    )
                    && match (left.wide_bounds(), right.wide_bounds()) {
                        // 64-bit bounds, such as a whole object of abstract
                        // size, `[0, sizeof(T))`, match as written.
                        (Some(left_bounds), Some(right_bounds)) => left_bounds == right_bounds,
                        (None, None) => {
                            left.int32_bounds().is_some()
                                && right.int32_bounds().is_some()
                                && crate::instrumentation::measure_operation(
                                    "kernel",
                                    "resource context equality",
                                    "resource memory match: start",
                                    || {
                                        bitvectors_match_for_resource_check(
                                            left.start(),
                                            right.start(),
                                            assumptions,
                                        )
                                    },
                                )
                                && crate::instrumentation::measure_operation(
                                    "kernel",
                                    "resource context equality",
                                    "resource memory match: end",
                                    || {
                                        bitvectors_match_for_resource_check(
                                            left.end(),
                                            right.end(),
                                            assumptions,
                                        )
                                    },
                                )
                        }
                        _ => false,
                    }
                    && crate::instrumentation::measure_operation(
                        "kernel",
                        "resource context equality",
                        "resource memory match: base",
                        || {
                            pointers_match_for_resource_check(
                                left.base(),
                                right.base(),
                                assumptions,
                            )
                        },
                    ))
        }
        (Resource::Instance(left), Resource::Instance(right)) => {
            left.identity() == right.identity()
                && left.name() == right.name()
                && left.schema() == right.schema()
                && left.resource_arguments() == right.resource_arguments()
                && left.arguments().len() == right.arguments().len()
                && left.fields().len() == right.fields().len()
                && left
                    .arguments()
                    .iter()
                    .chain(left.fields())
                    .zip(right.arguments().iter().chain(right.fields()))
                    .all(|(a, b)| resource_field_values_proven_equal(a, b, assumptions))
        }
        (
            Resource::Composite {
                name: left_name,
                arguments: left_arguments,
            },
            Resource::Composite {
                name: right_name,
                arguments: right_arguments,
            },
        )
        | (
            Resource::Token {
                name: left_name,
                arguments: left_arguments,
            },
            Resource::Token {
                name: right_name,
                arguments: right_arguments,
            },
        ) => {
            left_name == right_name
                && left_arguments.len() == right_arguments.len()
                && left_arguments
                    .iter()
                    .zip(right_arguments.iter())
                    .all(|(left, right)| match (left, right) {
                        (
                            crate::kernel::ResourceFieldValue::Program(left),
                            crate::kernel::ResourceFieldValue::Program(right),
                        ) => values_match(left, right),
                        _ => resource_field_values_proven_equal(left, right, assumptions),
                    })
        }
        _ => false,
    }
}

fn bitvectors_match_for_resource_check(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    // SymbolicMemory-range endpoints are int32 values. Their equality does not
    // identify byte offsets or grant access to either range.
    assumptions.int32_values_known_equal(left, right)
}

pub(in crate::kernel) fn pointer_offsets_match_from_memory_derivations(
    left: &AddressOffset,
    right: &AddressOffset,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left.view(), right.view()) {
        (OffsetView::Add(left_a, left_b), OffsetView::Add(right_a, right_b)) => {
            pointer_offsets_match_from_memory_derivations(left_a, right_a, assumptions)
                && pointer_offsets_match_from_memory_derivations(left_b, right_b, assumptions)
        }
        (
            OffsetView::Int32Scaled {
                index: left,
                byte_width: left_width,
            },
            OffsetView::Int32Scaled {
                index: right,
                byte_width: right_width,
            },
        ) => {
            left_width == right_width
                && (int32_operand_values_equal_for_memory_resolution(
                    left.operand_view(),
                    right.operand_view(),
                    assumptions,
                ) || explicit_atomic_equality_from_memory_derivations_views(
                    left.operand_view(),
                    right.operand_view(),
                    assumptions,
                ))
        }
        _ => false,
    }
}

fn pointer_offsets_match_for_resource_check(
    left: &AddressOffset,
    right: &AddressOffset,
    assumptions: &PureFactContext,
) -> bool {
    if crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource pointer offset: derivation edges",
        || pointer_offsets_match_from_memory_derivations(left, right, assumptions),
    ) {
        return true;
    }
    let transported_matches = |offset: &AddressOffset, target: &AddressOffset| {
        let mut memories = Vec::new();
        collect_pointer_offset_memories(target, &mut memories);
        memories.into_iter().any(|memory| {
            let transported = crate::instrumentation::measure_operation(
                "kernel",
                "resource context equality",
                "resource pointer offset transport: rewrite",
                || {
                    transport_framed_atomic_pointer_offset(
                        offset,
                        &ProgramPoint::unplaced(&memory),
                        Some((assumptions, false)),
                    )
                },
            );
            transported.is_some_and(|transported| {
                crate::instrumentation::measure_operation(
                    "kernel",
                    "resource context equality",
                    "resource pointer offset transport: compare",
                    || {
                        pointer_offsets_proven_equal_for_memory_resolution(
                            &transported,
                            target,
                            assumptions,
                        )
                    },
                )
            })
        })
    };
    if crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource pointer offset: framed transport",
        || transported_matches(left, right) || transported_matches(right, left),
    ) {
        return true;
    }
    crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource pointer offset: effect equality",
        || program_pointer_offsets_proven_equal_for_effect(left, right, assumptions),
    )
}

fn pointers_match_for_resource_check(
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    if left.base == right.base
        && pointer_offsets_match_for_resource_check(&left.offset, &right.offset, assumptions)
    {
        return true;
    }
    crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource pointer: general equality",
        || pointers_proven_equal_for_memory_resolution(left, right, assumptions),
    )
}

/// Assumption-free canonical form of a whole memory: every cell key and
/// value canonicalizes its embedded loads. Forms of the same memory
/// produced from different memory states compare equal when their
/// difference is representational.
pub(crate) fn canonical_memory_deep(memory: &SymbolicMemory) -> SymbolicMemory {
    // Assumption-free and deterministic; keyed by interned state identity.
    let key = crate::kernel::intern_memory_ref(memory);
    if let Some(hit) = DEEP_MEMORY_CACHE.with(|cache| cache.borrow().get(&key).cloned()) {
        return hit;
    }
    let result = canonical_memory_deep_uncached(memory);
    DEEP_MEMORY_CACHE.with(|cache| cache.borrow_mut().insert(key, result.clone()));
    result
}

fn canonical_memory_deep_uncached(memory: &SymbolicMemory) -> SymbolicMemory {
    let mut canonical = memory.clone();
    // A stored read is an immutable value, just as its former reserved name
    // was. Resolving it here would force every slot of a compact run to expand.
    let scalar = |term: &OldMachineTerm| {
        if matches!(term, OldMachineTerm::MemoryLoad(..)) {
            term.clone()
        } else {
            canonicalize_atomic_loads(term)
        }
    };
    let cells = canonical.cells.map_cells_preserving_runs(
        |pointer, value| {
            let key = canonicalize_pointer_loads(pointer);
            let value = match value {
                ProgramValue::PointerInteger(record) => {
                    ProgramValue::PointerInteger(PointerIntegerValue {
                        kind: record.kind.clone(),
                        numeric: Box::new(match record.numeric.as_ref() {
                            ProgramValue::Int64(t) => {
                                ProgramValue::Int64(canonicalize_atomic_loads(t))
                            }
                            ProgramValue::UInt64(t) => {
                                ProgramValue::UInt64(canonicalize_atomic_loads(t))
                            }
                            _ => unreachable!("LP64 representation"),
                        }),
                        pointer: Box::new(
                            record
                                .pointer
                                .map_addresses(canonicalize_pointer_loads, scalar),
                        ),
                    })
                }
                ProgramValue::Parameter(term) => ProgramValue::Parameter(term.clone()),
                ProgramValue::Void => ProgramValue::Void,
                ProgramValue::Bool(term) => ProgramValue::Bool(scalar(term)),
                ProgramValue::Int8(term) => ProgramValue::Int8(scalar(term)),
                ProgramValue::Int16(term) => ProgramValue::Int16(scalar(term)),
                ProgramValue::Int32(term) => ProgramValue::Int32(scalar(term)),
                ProgramValue::UInt8(term) => ProgramValue::UInt8(scalar(term)),
                ProgramValue::UInt16(term) => ProgramValue::UInt16(scalar(term)),
                ProgramValue::UInt32(term) => ProgramValue::UInt32(scalar(term)),
                ProgramValue::Int64(term) => ProgramValue::Int64(scalar(term)),
                ProgramValue::UInt64(term) => ProgramValue::UInt64(scalar(term)),
                ProgramValue::Int128(term) => ProgramValue::Int128(scalar(term)),
                ProgramValue::UInt128(term) => ProgramValue::UInt128(scalar(term)),
                ProgramValue::Float32(term) => ProgramValue::Float32(scalar(term)),
                ProgramValue::Float64(term) => ProgramValue::Float64(scalar(term)),
                ProgramValue::Pointer(pointer) => {
                    ProgramValue::Pointer(pointer.map_addresses(canonicalize_pointer_loads, scalar))
                }
            };
            (key, value)
        },
        |_| None,
        |run| {
            // Numeric Load/Copy slots retain structural reads. The cell-value
            // mapper above leaves those read values unchanged.
            // A canonical base plus a constant slot shift is canonical too:
            // slot_pointer and canonicalize_pointer_loads both use the same
            // folding AddressOffset::add constructor. Source cells and
            // derivation edges can vary across the run; neither is sampled.
            matches!(
                run.value_mode(),
                crate::kernel::primitives::RunValueMode::Load
                    | crate::kernel::primitives::RunValueMode::Copy { .. }
            ) && matches!(
                run.element_type(),
                ProgramType::Int8
                    | ProgramType::Int16
                    | ProgramType::Int32
                    | ProgramType::Int64
                    | ProgramType::Int128
                    | ProgramType::UInt8
                    | ProgramType::UInt16
                    | ProgramType::UInt32
                    | ProgramType::UInt64
                    | ProgramType::UInt128
                    | ProgramType::Float32
                    | ProgramType::Float64
            ) && canonicalize_pointer_loads(run.base()) == *run.base()
        },
    );
    canonical.cells = std::sync::Arc::new(cells);
    let union_cells = std::mem::take(&mut canonical.union_cells);
    for ((pointer, program_type), value) in union_cells.iter() {
        let key = canonicalize_pointer_loads(pointer);
        let mapped = match value.native() {
            ProgramValue::PointerInteger(record) => {
                ProgramValue::PointerInteger(PointerIntegerValue {
                    kind: record.kind.clone(),
                    numeric: Box::new(match record.numeric.as_ref() {
                        ProgramValue::Int64(t) => ProgramValue::Int64(canonicalize_atomic_loads(t)),
                        ProgramValue::UInt64(t) => {
                            ProgramValue::UInt64(canonicalize_atomic_loads(t))
                        }
                        _ => unreachable!("LP64 representation"),
                    }),
                    pointer: Box::new(
                        record
                            .pointer
                            .map_addresses(canonicalize_pointer_loads, canonicalize_atomic_loads),
                    ),
                })
            }
            ProgramValue::Parameter(term) => ProgramValue::Parameter(term.clone()),
            ProgramValue::Void => ProgramValue::Void,
            ProgramValue::Bool(term) => ProgramValue::Bool(canonicalize_atomic_loads(term)),
            ProgramValue::Int8(term) => ProgramValue::Int8(canonicalize_atomic_loads(term)),
            ProgramValue::Int16(term) => ProgramValue::Int16(canonicalize_atomic_loads(term)),
            ProgramValue::Int32(term) => ProgramValue::Int32(canonicalize_atomic_loads(term)),
            ProgramValue::UInt8(term) => ProgramValue::UInt8(canonicalize_atomic_loads(term)),
            ProgramValue::UInt16(term) => ProgramValue::UInt16(canonicalize_atomic_loads(term)),
            ProgramValue::UInt32(term) => ProgramValue::UInt32(canonicalize_atomic_loads(term)),
            ProgramValue::Int64(term) => ProgramValue::Int64(canonicalize_atomic_loads(term)),
            ProgramValue::UInt64(term) => ProgramValue::UInt64(canonicalize_atomic_loads(term)),
            ProgramValue::Int128(term) => ProgramValue::Int128(canonicalize_atomic_loads(term)),
            ProgramValue::UInt128(term) => ProgramValue::UInt128(canonicalize_atomic_loads(term)),
            ProgramValue::Float32(term) => ProgramValue::Float32(canonicalize_atomic_loads(term)),
            ProgramValue::Float64(term) => ProgramValue::Float64(canonicalize_atomic_loads(term)),
            ProgramValue::Pointer(pointer) => ProgramValue::Pointer(
                pointer.map_addresses(canonicalize_pointer_loads, canonicalize_atomic_loads),
            ),
        };
        std::sync::Arc::make_mut(&mut canonical.union_cells)
            .insert((key, *program_type), value.with_native_value(mapped));
    }
    canonical.record_diagnostic_transform(
        "canonicalize embedded reads",
        vec![memory.clone()],
        Vec::new(),
    );
    canonical
}

/// The program point a cell's load variable is named by, asked of the
/// resource tracker: the one place that decides which resources are the same
/// at which points (`crate::kernel::resource_tracker`).
#[track_caller]
fn cell_version_point(
    memory: &SharedMemory,
    pointer: &Address,
    bytes: impl Into<crate::kernel::AccessExtent>,
) -> Option<SharedMemory> {
    let bytes = bytes.into();
    crate::kernel::resource_tracker::last_same_version_memory(
        crate::kernel::resource_tracker::TrackedResource::Cell { pointer, bytes },
        memory,
    )
}

/// Deep-canonical memory equality; see [`canonical_memory_deep`].
pub(crate) fn memories_canonically_equal(left: &SymbolicMemory, right: &SymbolicMemory) -> bool {
    left == right || canonical_memory_deep(left) == canonical_memory_deep(right)
}

/// The exact successful result of resolving two loads through the memory
/// DAG. This is retained decision evidence, not yet a complete certificate:
/// each assumption-dependent hop still needs its own typed justification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MemoryDagLoadEqualityEvidence {
    pub(super) left: MemoryDagCell,
    pub(super) right: MemoryDagCell,
    pub(super) reason: MemoryDagLoadEqualityReason,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum MemoryDagLoadEqualityReason {
    CommonSource,
    EqualResolvedValue(ProgramValue),
    LeftRetainsRightRead,
    RightRetainsLeftRead,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum AtomicMemoryLoadEqualityEvidence {
    SameCell(MemoryDagLoadEqualityEvidence),
    /// One or both load endpoints are pointer-observable canonical
    /// projections. The projection edge is producer-known derivation; the
    /// ordinary DAG walk begins at its retained source.
    SameCellViaCanonicalProjection {
        equality: MemoryDagLoadEqualityEvidence,
        left_projection: Option<CanonicalLoadProjectionEvidence>,
        right_projection: Option<CanonicalLoadProjectionEvidence>,
    },
    LeftResolvesToRight {
        left: MemoryDagCell,
    },
    RightResolvesToLeft {
        right: MemoryDagCell,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CanonicalLoadProjectionEvidence {
    pub(super) source: SharedMemory,
    pub(super) projected: SharedMemory,
    pub(super) pointer: Address,
}

impl CanonicalLoadProjectionEvidence {
    fn for_endpoint(projected: &SharedMemory, pointer: &Address) -> Option<Self> {
        canonical_load_projection_source(projected, pointer).map(|source| Self {
            source,
            projected: projected.clone(),
            pointer: pointer.clone(),
        })
    }

    pub(super) fn checks(&self, projected: &SharedMemory, pointer: &Address) -> bool {
        &self.projected == projected
            && &self.pointer == pointer
            && canonical_load_projection_recorded(&self.source, projected, pointer)
    }
}

/// A load equality consumed by one checked operation, together with the
/// exact, locally checkable reason for that equality. The query is retained
/// alongside its evidence so a later checker cannot retarget the witness.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CheckedLoadEquality {
    left: OldMachineTerm,
    right: OldMachineTerm,
    evidence: CheckedLoadEqualityEvidence,
}

/// A bounded candidate path through aliases indexed under the endpoints.
/// Each retained edge is checked against its exact named premise on checking.
fn selected_pointer_alias_path(
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> Option<Vec<(Address, Address)>> {
    let equal = |first: &Address, second: &Address| {
        first == second
            || assumptions.proves_exact(&Proposition::condition_is(
                OldConditionTerm::address_equal(first.clone(), second.clone()),
                true,
            ))
            || assumptions.proves_exact(&Proposition::condition_is(
                OldConditionTerm::address_equal(second.clone(), first.clone()),
                true,
            ))
    };
    for middle in assumptions.exact_pointer_aliases(left).take(8) {
        if !equal(left, middle) {
            continue;
        }
        if equal(middle, right) {
            return Some(vec![
                (left.clone(), middle.clone()),
                (middle.clone(), right.clone()),
            ]);
        }
    }
    None
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum CheckedLoadEqualityEvidence {
    #[cfg(test)]
    OriginStoredValue {
        endpoint: OriginLoadEndpoint,
        cell: MemoryDagCell,
        offset: PointerOffsetCongruenceEvidence,
        reversed: bool,
    },
    /// Both terms have the same assumption-free canonical form. This is a
    /// structural check, not a lookup through ambient equality facts.
    Canonical,
    /// Both loads resolve to one cell by the execution-recorded memory DAG.
    MemoryDag(AtomicMemoryLoadEqualityEvidence),
    /// The two source-level load terms have congruent addresses, and their
    /// recorded origin states are structurally identical at that cell.
    /// Keeping both endpoints and the selected offset proof makes this a
    /// finite checked path rather than a request to rediscover pointer
    /// equality during proof-object validation.
    OriginDirectState {
        left: OriginLoadEndpoint,
        right: OriginLoadEndpoint,
        offset: PointerOffsetCongruenceEvidence,
    },
    /// Equal-width scalar reads at one execution or explicitly named state,
    /// with exact pointer equality retained as their address witness. The source load
    /// names remain distinct, so explicit proof rewrites keep their addresses.
    OriginAliasedState {
        left: OriginLoadEndpoint,
        right: OriginLoadEndpoint,
        alias: Box<Proposition>,
        alias_path: Option<Vec<(Address, Address)>>,
        retained_states: Option<Box<CheckedLoadEquality>>,
        /// Named endpoints use only a shared defining state, never a
        /// first-observed origin or a call-event correspondence.
        named_program_point: bool,
    },
    /// The two source-level load terms meet along the recorded memory DAG
    /// when viewed at their original execution states.
    OriginMemoryDag {
        left: OriginLoadEndpoint,
        right: OriginLoadEndpoint,
        equality: AtomicMemoryLoadEqualityEvidence,
    },
    /// One exact effect-summary fact connects the two original states,
    /// and each mutable range carries its selected local proof of
    /// disjointness from the loaded pointer.
    OriginEffectSummary {
        left: OriginLoadEndpoint,
        right: OriginLoadEndpoint,
        summary: Box<Proposition>,
        reversed: bool,
        ranges: Vec<RangeDisjointFromPointerEvidence>,
    },
    /// Both DAG walks stop at registered result views of one opaque call
    /// occurrence owned by the current execution proof.
    SameCheckedCallEvent(CheckedCallLoadEqualityEvidence),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct OriginLoadEndpoint {
    /// The read's origin memory, placed where the origin is; named, and
    /// compared, by its memory.
    point: ProgramPoint,
    pointer: Address,
    kind: LoadKind,
}

fn origin_load_width(term: &OldMachineTerm) -> Option<u32> {
    crate::kernel::eval::scalar_read_observation(crate::kernel::MachineOperandView::Old(term))
        .map(|read| read.bytes)
}

impl OriginLoadEndpoint {
    fn memory(&self) -> &SharedMemory {
        self.point.shared_memory()
    }

    #[cfg(test)]
    fn for_term(term: &OldMachineTerm) -> Option<Self> {
        if let OldMachineTerm::MemoryLoad(memory, pointer, kind) = term {
            return Some(Self {
                point: ProgramPoint::viewing(memory.shared_memory(), memory),
                pointer: pointer.as_ref().clone(),
                kind: *kind,
            });
        }
        Self::for_observed_term(term)
    }

    fn for_observed_term(term: &OldMachineTerm) -> Option<Self> {
        let read = crate::kernel::eval::scalar_read_observation(
            crate::kernel::MachineOperandView::Old(term),
        )?;
        Some(Self {
            point: read
                .origin
                .map(|origin| ProgramPoint::viewing(origin.shared_memory(), &origin))?,
            pointer: read.pointer,
            kind: read.kind,
        })
    }

    /// The exact selected state, independently of the observed origin.
    fn for_named_term(term: &OldMachineTerm) -> Option<Self> {
        let read = crate::kernel::eval::scalar_read_observation(
            crate::kernel::MachineOperandView::Old(term),
        )?;
        Some(Self {
            point: ProgramPoint::viewing(read.point.shared_memory(), &read.point),
            pointer: read.pointer,
            kind: read.kind,
        })
    }

    /// The access width a walk from this endpoint uses.
    #[cfg(test)]
    fn bytes(&self) -> u32 {
        crate::kernel::load_term_access_width(self.memory(), &self.pointer, self.kind)
    }

    #[cfg(test)]
    fn matches_term(&self, term: &OldMachineTerm) -> bool {
        Self::for_term(term).as_ref() == Some(self)
    }

    #[cfg(test)]
    fn matches_observed_term(&self, term: &OldMachineTerm) -> bool {
        Self::for_observed_term(term).as_ref() == Some(self)
    }

    fn as_term(&self) -> OldMachineTerm {
        crate::kernel::OldMachineTerm::read_named(
            self.point.clone(),
            self.pointer.clone(),
            self.kind,
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CheckedCallLoadEqualityEvidence {
    event: crate::kernel::proof::CheckedCallEvent,
    pointer: Address,
    left: MemoryDagCell,
    right: MemoryDagCell,
}

#[derive(Default)]
struct CheckedLoadEqualityCaptureFrame {
    equalities: Vec<CheckedLoadEquality>,
    call_events: crate::kernel::proof::CheckedCallEvents,
}

struct CheckedCallEventScopeFrame {
    events: crate::kernel::proof::CheckedCallEvents,
    allow_view_registration: bool,
}

thread_local! {
    /// Scoped sinks owned by checked consumers. Nested consumers retain only
    /// the equalities they themselves ask for; an outer sink resumes after
    /// the inner consumer finishes.
    static CHECKED_LOAD_EQUALITY_CAPTURES: std::cell::RefCell<Vec<CheckedLoadEqualityCaptureFrame>> =
        const { std::cell::RefCell::new(Vec::new()) };
    static CHECKED_CALL_EVENT_SCOPES: std::cell::RefCell<Vec<CheckedCallEventScopeFrame>> =
        const { std::cell::RefCell::new(Vec::new()) };
    static CHECKED_ORIGIN_LOAD_EQUALITIES_IN_PROGRESS: std::cell::RefCell<
        BTreeSet<(OldMachineTerm, OldMachineTerm)>,
    > = const { std::cell::RefCell::new(BTreeSet::new()) };
}

struct CheckedOriginLoadEqualityGuard {
    query: (OldMachineTerm, OldMachineTerm),
}

impl CheckedOriginLoadEqualityGuard {
    fn enter(left: &OldMachineTerm, right: &OldMachineTerm) -> Option<Self> {
        let query = if left <= right {
            (left.clone(), right.clone())
        } else {
            (right.clone(), left.clone())
        };
        CHECKED_ORIGIN_LOAD_EQUALITIES_IN_PROGRESS.with(|queries| {
            let inserted = queries.borrow_mut().insert(query.clone());
            inserted.then_some(Self { query })
        })
    }
}

impl Drop for CheckedOriginLoadEqualityGuard {
    fn drop(&mut self) {
        CHECKED_ORIGIN_LOAD_EQUALITIES_IN_PROGRESS.with(|queries| {
            queries.borrow_mut().remove(&self.query);
        });
    }
}

pub(crate) struct CheckedCallEventScope {
    active: bool,
}

impl CheckedCallEventScope {
    pub(crate) fn start(call_events: &crate::kernel::proof::CheckedCallEvents) -> Self {
        Self::start_with_registration(call_events, false)
    }

    #[cfg(test)]
    pub(crate) fn start_registering_views(
        call_events: &crate::kernel::proof::CheckedCallEvents,
    ) -> Self {
        Self::start_with_registration(call_events, true)
    }

    fn start_with_registration(
        call_events: &crate::kernel::proof::CheckedCallEvents,
        allow_view_registration: bool,
    ) -> Self {
        CHECKED_CALL_EVENT_SCOPES.with(|scopes| {
            scopes.borrow_mut().push(CheckedCallEventScopeFrame {
                events: call_events.clone(),
                allow_view_registration,
            })
        });
        Self { active: true }
    }
}

impl Drop for CheckedCallEventScope {
    fn drop(&mut self) {
        if self.active {
            CHECKED_CALL_EVENT_SCOPES.with(|scopes| {
                scopes.borrow_mut().pop();
            });
        }
    }
}

/// Captures the load equalities consumed while constructing one checked
/// object. Dropping an unfinished capture discards its partial evidence.
pub(crate) struct CheckedLoadEqualityCapture {
    active: bool,
}

impl CheckedLoadEqualityCapture {
    #[cfg(test)]
    pub(crate) fn start() -> Self {
        Self::start_with_call_events(&crate::kernel::proof::CheckedCallEvents::default())
    }

    pub(crate) fn start_with_call_events(
        call_events: &crate::kernel::proof::CheckedCallEvents,
    ) -> Self {
        CHECKED_LOAD_EQUALITY_CAPTURES.with(|captures| {
            captures.borrow_mut().push(CheckedLoadEqualityCaptureFrame {
                equalities: Vec::new(),
                call_events: call_events.clone(),
            });
        });
        Self { active: true }
    }

    pub(crate) fn finish(mut self) -> Vec<CheckedLoadEquality> {
        let captured = CHECKED_LOAD_EQUALITY_CAPTURES.with(|captures| {
            captures
                .borrow_mut()
                .pop()
                .expect("a checked load-equality capture is active")
                .equalities
        });
        self.active = false;
        captured
    }
}

impl Drop for CheckedLoadEqualityCapture {
    fn drop(&mut self) {
        if self.active {
            CHECKED_LOAD_EQUALITY_CAPTURES.with(|captures| {
                captures.borrow_mut().pop();
            });
        }
    }
}

fn retain_checked_load_equality(equality: CheckedLoadEquality) {
    CHECKED_LOAD_EQUALITY_CAPTURES.with(|captures| {
        if let Some(active) = captures.borrow_mut().last_mut() {
            active.equalities.push(equality);
        }
    });
}

fn active_checked_call_events() -> crate::kernel::proof::CheckedCallEvents {
    let captured = CHECKED_LOAD_EQUALITY_CAPTURES.with(|captures| {
        captures
            .borrow()
            .last()
            .map(|frame| frame.call_events.clone())
            .unwrap_or_default()
    });
    if !captured.is_empty() {
        return captured;
    }
    CHECKED_CALL_EVENT_SCOPES.with(|scopes| {
        scopes
            .borrow()
            .last()
            .map(|scope| scope.events.clone())
            .unwrap_or_default()
    })
}

fn active_scope_allows_call_view_registration() -> bool {
    CHECKED_CALL_EVENT_SCOPES.with(|scopes| {
        scopes
            .borrow()
            .last()
            .is_some_and(|scope| scope.allow_view_registration)
    })
}

fn checked_call_load_equality_evidence(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> Option<CheckedCallLoadEqualityEvidence> {
    let (
        OldMachineTerm::MemoryLoad(left_memory, left_pointer, left_kind),
        OldMachineTerm::MemoryLoad(right_memory, right_pointer, right_kind),
    ) = (left, right)
    else {
        return None;
    };
    if left_pointer.address() != right_pointer.address() || left_kind != right_kind {
        return None;
    }
    let left = memory_dag_cell_source(
        left_memory.shared_memory(),
        left_pointer,
        crate::kernel::load_term_access_width(
            left_memory.shared_memory(),
            left_pointer,
            *left_kind,
        ),
        assumptions,
        true,
    )?;
    let right = memory_dag_cell_source(
        right_memory.shared_memory(),
        right_pointer,
        crate::kernel::load_term_access_width(
            right_memory.shared_memory(),
            right_pointer,
            *right_kind,
        ),
        assumptions,
        true,
    )?;
    if !left.has_only_typed_hops()
        || !right.has_only_typed_hops()
        || !matches!(
            left.node().derivation().as_deref(),
            Some(MemoryDerivation::CallHavoc { .. })
        )
        || !matches!(
            right.node().derivation().as_deref(),
            Some(MemoryDerivation::CallHavoc { .. })
        )
    {
        return None;
    }
    let events = active_checked_call_events();
    if active_scope_allows_call_view_registration() {
        let left_derivation = left.node().derivation();
        let right_derivation = right.node().derivation();
        let shapes_match = matches!(
            (left_derivation.as_deref(), right_derivation.as_deref()),
            (
                Some(MemoryDerivation::CallHavoc {
                    variable: left_variable,
                    mutable_ranges: left_ranges,
                    ..
                }),
                Some(MemoryDerivation::CallHavoc {
                    variable: right_variable,
                    mutable_ranges: right_ranges,
                    ..
                })
            ) if left_variable == right_variable && left_ranges == right_ranges
        );
        if shapes_match {
            for event in events.events_for_view(left.node()) {
                if !events.contains_view(&event, right.node()) {
                    events.register_view(&event, right.node().clone());
                }
            }
            for event in events.events_for_view(right.node()) {
                if !events.contains_view(&event, left.node()) {
                    events.register_view(&event, left.node().clone());
                }
            }
        }
    }
    events
        .events_for_view(left.node())
        .into_iter()
        .find(|event| events.contains_view(event, right.node()))
        .map(|event| CheckedCallLoadEqualityEvidence {
            event,
            pointer: left_pointer.as_ref().clone(),
            left,
            right,
        })
}

#[cfg(test)]
pub(super) fn checked_call_event_load_equality_for_test(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    with_extended_dag_bridging(|| {
        checked_call_load_equality_evidence(left, right, assumptions).is_some()
    })
}

impl CheckedLoadEquality {
    fn new(
        left: &OldMachineTerm,
        right: &OldMachineTerm,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        Self::new_with_canonical_fallback(left, right, assumptions, true)
    }

    fn new_with_canonical_fallback(
        left: &OldMachineTerm,
        right: &OldMachineTerm,
        assumptions: &PureFactContext,
        allow_canonical_fallback: bool,
    ) -> Option<Self> {
        if !matches!(left, OldMachineTerm::MemoryLoad(_, _, _))
            || !matches!(right, OldMachineTerm::MemoryLoad(_, _, _))
        {
            return None;
        }
        // Prefer the named-memory DAG: its work is proportional to the two
        // selected derivation paths. Deep canonicalization is a complete
        // structural fallback, but can walk unrelated state cells.
        let previous = EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true));
        let dag_evidence = with_extended_dag_bridging(|| {
            atomic_memory_load_equality_evidence(left, right, assumptions)
                .filter(AtomicMemoryLoadEqualityEvidence::is_fully_typed)
                .or_else(|| {
                    typed_canonical_projection_load_equality_evidence(left, right, assumptions)
                })
        });
        let call_evidence = dag_evidence
            .is_none()
            .then(|| {
                with_extended_dag_bridging(|| {
                    checked_call_load_equality_evidence(left, right, assumptions)
                })
            })
            .flatten();
        EXPLICIT_DAG_CHECK.with(|flag| flag.set(previous));
        let evidence = if let Some(evidence) = dag_evidence {
            CheckedLoadEqualityEvidence::MemoryDag(evidence)
        } else if let Some(evidence) = call_evidence {
            CheckedLoadEqualityEvidence::SameCheckedCallEvent(evidence)
        } else if allow_canonical_fallback
            && crate::kernel::eval::canonical_term(left)
                == crate::kernel::eval::canonical_term(right)
            && !crate::kernel::reasoning::load_equality_lacks_recorded_evidence(
                left,
                right,
                assumptions,
            )
        {
            CheckedLoadEqualityEvidence::Canonical
        } else {
            return None;
        };
        Some(Self {
            left: left.clone(),
            right: right.clone(),
            evidence,
        })
    }

    #[cfg(test)]
    pub(crate) fn checks(&self, assumptions: &PureFactContext) -> bool {
        self.checks_with_call_events(
            assumptions,
            &crate::kernel::proof::CheckedCallEvents::default(),
        )
    }

    #[cfg(test)]
    pub(crate) fn checks_with_call_events(
        &self,
        assumptions: &PureFactContext,
        call_events: &crate::kernel::proof::CheckedCallEvents,
    ) -> bool {
        match &self.evidence {
            CheckedLoadEqualityEvidence::OriginStoredValue {
                endpoint,
                cell,
                offset,
                reversed,
            } => {
                let (value, load) = if *reversed {
                    (&self.right, &self.left)
                } else {
                    (&self.left, &self.right)
                };
                let Some(derivation) = cell.node().derivation() else {
                    return false;
                };
                let bytes = endpoint.bytes();
                let Some((pointer, written @ (ProgramValue::Int32(_) | ProgramValue::UInt32(_)))) =
                    stored_write_reaching(
                        derivation.as_ref(),
                        &endpoint.pointer,
                        bytes,
                        assumptions,
                    )
                else {
                    return false;
                };
                // The read returns the stored word at its own kind and σ of
                // it at the other signedness (R-mem); the address half is
                // `offset` below.
                let Some(ProgramValue::Int32(stored) | ProgramValue::UInt32(stored)) =
                    endpoint.kind.read_cell(&written)
                else {
                    return false;
                };
                let pointer = &pointer;
                endpoint.matches_term(load)
                    && cell.has_only_typed_hops()
                    && written.byte_width() == bytes
                    && cell.checks_walk_from(
                        endpoint.memory(),
                        &endpoint.pointer,
                        bytes,
                        assumptions,
                    )
                    && pointer.base == endpoint.pointer.base
                    && offset.checks(&pointer.offset, &endpoint.pointer.offset, assumptions)
                    && &stored == value
            }
            CheckedLoadEqualityEvidence::Canonical => {
                crate::kernel::eval::canonical_term(&self.left)
                    == crate::kernel::eval::canonical_term(&self.right)
            }
            CheckedLoadEqualityEvidence::MemoryDag(evidence) => evidence.checks(
                &Proposition::condition_is(
                    OldConditionTerm::equal(self.left.clone(), self.right.clone()),
                    true,
                ),
                assumptions,
            ),
            CheckedLoadEqualityEvidence::OriginDirectState {
                left,
                right,
                offset,
            } => {
                left.matches_observed_term(&self.left)
                    && right.matches_observed_term(&self.right)
                    && left.kind == right.kind
                    && left.pointer.base == right.pointer.base
                    && offset.checks(&left.pointer.offset, &right.pointer.offset, assumptions)
                    && memories_match_for_pointer_load(left.memory(), right.memory(), &left.pointer)
            }
            CheckedLoadEqualityEvidence::OriginMemoryDag {
                left,
                right,
                equality,
            } => {
                left.matches_observed_term(&self.left)
                    && right.matches_observed_term(&self.right)
                    && equality.checks(
                        &Proposition::condition_is(
                            OldConditionTerm::equal(left.as_term(), right.as_term()),
                            true,
                        ),
                        assumptions,
                    )
            }
            CheckedLoadEqualityEvidence::OriginAliasedState {
                left,
                right,
                alias,
                alias_path,
                retained_states,
                named_program_point,
            } => {
                let endpoints_match = if *named_program_point {
                    retained_states.is_none()
                        && OriginLoadEndpoint::for_named_term(&self.left).as_ref() == Some(left)
                        && OriginLoadEndpoint::for_named_term(&self.right).as_ref() == Some(right)
                } else {
                    left.matches_observed_term(&self.left)
                        && right.matches_observed_term(&self.right)
                };
                endpoints_match
                    && left.kind == right.kind
                    && match retained_states {
                        None => left.memory() == right.memory(),
                        Some(equality) => {
                            let OldMachineTerm::MemoryLoad(memory, pointer, kind) = &equality.left
                            else {
                                return false;
                            };
                            memory.shared_memory() == left.memory()
                                && *kind == left.kind
                                && (pointer.as_ref() == &left.pointer
                                    || pointer.as_ref() == &right.pointer)
                                && equality.right
                                    == OldMachineTerm::read_named(
                                        ProgramPoint::unplaced(right.memory()),
                                        pointer.clone(),
                                        right.kind,
                                    )
                                && equality.checks_with_call_events(assumptions, call_events)
                        }
                    }
                    && origin_load_width(&self.left) == Some(4)
                    && origin_load_width(&self.right) == Some(4)
                    && (alias.as_ref()
                        == &Proposition::condition_is(
                            OldConditionTerm::address_equal(
                                left.pointer.clone(),
                                right.pointer.clone(),
                            ),
                            true,
                        )
                        || alias.as_ref()
                            == &Proposition::condition_is(
                                OldConditionTerm::address_equal(
                                    right.pointer.clone(),
                                    left.pointer.clone(),
                                ),
                                true,
                            ))
                    && match alias_path {
                        None => assumptions.proves_exact(alias),
                        Some(path) => {
                            path.first().is_some_and(|step| step.0 == left.pointer)
                                && path.last().is_some_and(|step| step.1 == right.pointer)
                                && path.windows(2).all(|steps| steps[0].1 == steps[1].0)
                                && path.iter().all(|step| {
                                    assumptions.proves_exact(&Proposition::condition_is(
                                        OldConditionTerm::address_equal(
                                            step.0.clone(),
                                            step.1.clone(),
                                        ),
                                        true,
                                    )) || assumptions.proves_exact(&Proposition::condition_is(
                                        OldConditionTerm::address_equal(
                                            step.1.clone(),
                                            step.0.clone(),
                                        ),
                                        true,
                                    ))
                                })
                        }
                    }
            }
            CheckedLoadEqualityEvidence::OriginEffectSummary {
                left,
                right,
                summary,
                reversed,
                ranges,
            } => {
                let Proposition::MemoryEffectSummary {
                    before,
                    after,
                    mutable_ranges,
                    ..
                } = summary.as_ref()
                else {
                    return false;
                };
                let (expected_left, expected_right) = if *reversed {
                    (after, before)
                } else {
                    (before, after)
                };
                left.matches_observed_term(&self.left)
                    && right.matches_observed_term(&self.right)
                    && left.pointer == right.pointer
                    && left.kind == right.kind
                    && left.memory().memory() == expected_left
                    && right.memory().memory() == expected_right
                    && assumptions.contains_assumed_exact(summary)
                    && ranges.len() == mutable_ranges.len()
                    && ranges.iter().zip(mutable_ranges).all(|(evidence, range)| {
                        evidence.checks(range, &left.pointer, left.bytes(), assumptions)
                    })
            }
            CheckedLoadEqualityEvidence::SameCheckedCallEvent(evidence) => {
                let (
                    OldMachineTerm::MemoryLoad(left_memory, left_pointer, left_kind),
                    OldMachineTerm::MemoryLoad(right_memory, right_pointer, right_kind),
                ) = (&self.left, &self.right)
                else {
                    return false;
                };
                left_pointer.address() == right_pointer.address()
                    && left_kind == right_kind
                    && left_pointer.address() == &evidence.pointer
                    && call_events.contains(&evidence.event)
                    && call_events.contains_view(&evidence.event, evidence.left.node())
                    && call_events.contains_view(&evidence.event, evidence.right.node())
                    && matches!(
                        evidence.left.node().derivation().as_deref(),
                        Some(MemoryDerivation::CallHavoc { .. })
                    )
                    && matches!(
                        evidence.right.node().derivation().as_deref(),
                        Some(MemoryDerivation::CallHavoc { .. })
                    )
                    && evidence.left.checks_walk_from(
                        left_memory.shared_memory(),
                        left_pointer,
                        crate::kernel::load_term_access_width(
                            left_memory.shared_memory(),
                            left_pointer,
                            *left_kind,
                        ),
                        assumptions,
                    )
                    && evidence.right.checks_walk_from(
                        right_memory.shared_memory(),
                        right_pointer,
                        crate::kernel::load_term_access_width(
                            right_memory.shared_memory(),
                            right_pointer,
                            *right_kind,
                        ),
                        assumptions,
                    )
            }
        }
    }

    #[cfg(test)]
    pub(super) fn memory_dag_evidence_for_test(&self) -> Option<&AtomicMemoryLoadEqualityEvidence> {
        match &self.evidence {
            CheckedLoadEqualityEvidence::MemoryDag(evidence) => Some(evidence),
            CheckedLoadEqualityEvidence::Canonical
            | CheckedLoadEqualityEvidence::OriginStoredValue { .. }
            | CheckedLoadEqualityEvidence::OriginDirectState { .. }
            | CheckedLoadEqualityEvidence::OriginAliasedState { .. }
            | CheckedLoadEqualityEvidence::OriginMemoryDag { .. }
            | CheckedLoadEqualityEvidence::OriginEffectSummary { .. }
            | CheckedLoadEqualityEvidence::SameCheckedCallEvent(_) => None,
        }
    }

    #[cfg(test)]
    pub(super) fn is_same_checked_call_event_for_test(&self) -> bool {
        matches!(
            self.evidence,
            CheckedLoadEqualityEvidence::SameCheckedCallEvent(_)
        )
    }

    #[cfg(test)]
    pub(super) fn checks_retargeted_for_test(
        &self,
        left: OldMachineTerm,
        right: OldMachineTerm,
        assumptions: &PureFactContext,
        call_events: &crate::kernel::proof::CheckedCallEvents,
    ) -> bool {
        let mut retargeted = self.clone();
        retargeted.left = left;
        retargeted.right = right;
        retargeted.checks_with_call_events(assumptions, call_events)
    }
}

/// Check one selected atomic load equality and retain its typed witness in
/// the active checked consumer, when there is one.
pub(crate) fn checked_atomic_load_equality(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    let Some(equality) = CheckedLoadEquality::new(left, right, assumptions) else {
        return false;
    };
    retain_checked_load_equality(equality);
    true
}

/// The recorded-edge subset used by broad fact matching. Canonicalizing an
/// arbitrary failed term pair here would turn a local lookup back into
/// speculative whole-term work; origin matching below owns its direct
/// structural state rule separately.
pub(crate) fn checked_recorded_atomic_load_equality(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    let Some(equality) =
        CheckedLoadEquality::new_with_canonical_fallback(left, right, assumptions, false)
    else {
        return false;
    };
    retain_checked_load_equality(equality);
    true
}

/// Retain a selected stored-value path for a rewritten load representation.
#[cfg(test)]
pub(crate) fn checked_stored_origin_equality(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    checked_stored_origin_operand_equality(
        crate::kernel::MachineOperandView::Old(left),
        crate::kernel::MachineOperandView::Old(right),
        assumptions,
    )
}

/// Compare a selected shared value to the native value held by its source
/// store. The finite evidence owns that stored value, not an exported DAG.
#[cfg(test)]
fn checked_stored_origin_operand_equality(
    left: crate::kernel::MachineOperandView<'_>,
    right: crate::kernel::MachineOperandView<'_>,
    assumptions: &PureFactContext,
) -> bool {
    use crate::kernel::MachineOperandView as V;
    for (value, load, reversed) in [(left, right, false), (right, left, true)] {
        let Some(load) = load.read_source() else {
            continue;
        };
        let Some(endpoint) = OriginLoadEndpoint::for_term(&load) else {
            continue;
        };
        let previous = EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true));
        let cell = with_extended_dag_bridging(|| {
            memory_dag_cell_source(
                endpoint.memory(),
                &endpoint.pointer,
                endpoint.bytes(),
                assumptions,
                true,
            )
        });
        EXPLICIT_DAG_CHECK.with(|flag| flag.set(previous));
        let Some(cell) = cell else {
            continue;
        };
        if !cell.has_only_typed_hops() {
            continue;
        }
        let Some(derivation) = cell.node().derivation() else {
            continue;
        };
        let previous = EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true));
        let written = with_extended_dag_bridging(|| {
            stored_write_reaching(
                derivation.as_ref(),
                &endpoint.pointer,
                endpoint.bytes(),
                assumptions,
            )
        });
        EXPLICIT_DAG_CHECK.with(|flag| flag.set(previous));
        let Some((pointer, written @ (ProgramValue::Int32(_) | ProgramValue::UInt32(_)))) = written
        else {
            continue;
        };
        // The read's value of the store, σ of the stored word at the other
        // signedness (R-mem), as wide as the walk, as `write_supplies_read`
        // asks of every stored value; the address half is the offset
        // congruence below.
        let Some(ProgramValue::Int32(stored) | ProgramValue::UInt32(stored)) =
            endpoint.kind.read_cell(&written)
        else {
            continue;
        };
        let pointer = &pointer;
        let bytes = endpoint.bytes();
        let matches = match value {
            V::Old(value) => &stored == value,
            V::Shared(value) => {
                crate::kernel::proof::machine_source_match::MachineSourceMatcher::new(V::Old(
                    &stored,
                ))
                .matches(MachineIntegerType::Int32, value)
                    == Some(true)
            }
        };
        if !matches || pointer.base != endpoint.pointer.base || written.byte_width() != bytes {
            continue;
        }
        let Some(offset) = assumptions
            .pointer_offset_congruence_evidence(&pointer.offset, &endpoint.pointer.offset)
        else {
            continue;
        };
        let selected_value = match value {
            V::Old(value) => value.clone(),
            V::Shared(_) => stored,
        };
        let (left, right) = if reversed {
            (load.into_owned(), selected_value)
        } else {
            (selected_value, load.into_owned())
        };
        let equality = CheckedLoadEquality {
            left,
            right,
            evidence: CheckedLoadEqualityEvidence::OriginStoredValue {
                endpoint,
                cell,
                offset,
                reversed,
            },
        };
        if !equality.checks_with_call_events(
            assumptions,
            &crate::kernel::proof::CheckedCallEvents::default(),
        ) {
            continue;
        }
        retain_checked_load_equality(equality);
        return true;
    }
    false
}

/// Select a finite equality witness for two loads at the states where the
/// execution first observed them. This is the evidence-producing replacement
/// for the former recursive origin fallback in `memory_loads_proven_equal`.
pub(crate) fn checked_origin_load_equality(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    let Some(_query) = CheckedOriginLoadEqualityGuard::enter(left, right) else {
        return false;
    };
    // Equal names are definitionally one state. Address congruence at
    // that state does not require connecting first-observed origins,
    // which may belong to disconnected execution arms.
    let named_endpoints = OriginLoadEndpoint::for_named_term(left)
        .zip(OriginLoadEndpoint::for_named_term(right))
        .filter(|(left, right)| {
            left.memory() == right.memory() && left.pointer.base != right.pointer.base
        });
    let named_program_point = named_endpoints.is_some();
    let Some((left_endpoint, right_endpoint)) = named_endpoints.or_else(|| {
        OriginLoadEndpoint::for_observed_term(left)
            .zip(OriginLoadEndpoint::for_observed_term(right))
    }) else {
        return false;
    };
    if left_endpoint.kind != right_endpoint.kind {
        return false;
    }
    if left_endpoint.pointer.base != right_endpoint.pointer.base {
        if origin_load_width(left) == Some(4) && origin_load_width(right) == Some(4) {
            for (first, second) in [
                (&left_endpoint.pointer, &right_endpoint.pointer),
                (&right_endpoint.pointer, &left_endpoint.pointer),
            ] {
                let alias = Proposition::condition_is(
                    OldConditionTerm::address_equal(first.clone(), second.clone()),
                    true,
                );
                let alias_path = if assumptions.proves_exact(&alias) {
                    None
                } else {
                    if first != &left_endpoint.pointer {
                        continue;
                    }
                    let Some(path) = selected_pointer_alias_path(first, second, assumptions) else {
                        continue;
                    };
                    Some(path)
                };
                {
                    let retained_states = if left_endpoint.memory() == right_endpoint.memory() {
                        None
                    } else {
                        let mut selected = None;
                        for pointer in [&left_endpoint.pointer, &right_endpoint.pointer] {
                            let first = crate::kernel::OldMachineTerm::read_named(
                                left_endpoint.point.clone(),
                                pointer.clone(),
                                left_endpoint.kind,
                            );
                            let second = crate::kernel::OldMachineTerm::read_named(
                                right_endpoint.point.clone(),
                                pointer.clone(),
                                right_endpoint.kind,
                            );
                            let capture = CheckedLoadEqualityCapture::start_with_call_events(
                                &active_checked_call_events(),
                            );
                            let equal = checked_origin_load_equality(&first, &second, assumptions);
                            let mut evidence = capture.finish();
                            if equal && evidence.len() == 1 {
                                selected = evidence.pop().map(Box::new);
                                break;
                            }
                        }
                        let Some(selected) = selected else {
                            continue;
                        };
                        Some(selected)
                    };
                    retain_checked_load_equality(CheckedLoadEquality {
                        left: left.clone(),
                        right: right.clone(),
                        evidence: CheckedLoadEqualityEvidence::OriginAliasedState {
                            left: left_endpoint.clone(),
                            right: right_endpoint.clone(),
                            alias: Box::new(alias),
                            alias_path,
                            retained_states,
                            named_program_point,
                        },
                    });
                    return true;
                }
            }
        }
        return false;
    }
    // The arms below compare the two origin states' cell maps, and a cell
    // map does not record the stores it dropped. Ask the history about the
    // endpoints this comparison is about to take as equal.
    if left_endpoint.pointer == right_endpoint.pointer
        && crate::kernel::reasoning::loads_lack_recorded_equality(
            left_endpoint.memory(),
            right_endpoint.memory(),
            &left_endpoint.pointer,
            left_endpoint.kind,
            assumptions,
        )
    {
        return false;
    }

    let direct = assumptions
        .pointer_offset_congruence_evidence(
            &left_endpoint.pointer.offset,
            &right_endpoint.pointer.offset,
        )
        .filter(|_| {
            memories_match_for_pointer_load(
                left_endpoint.memory(),
                right_endpoint.memory(),
                &left_endpoint.pointer,
            )
        })
        .map(|offset| CheckedLoadEqualityEvidence::OriginDirectState {
            left: left_endpoint.clone(),
            right: right_endpoint.clone(),
            offset,
        });

    let dag = direct.is_none().then(|| {
        if left_endpoint.pointer != right_endpoint.pointer {
            return None;
        }
        let previous = EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true));
        let evidence = with_extended_dag_bridging(|| {
            atomic_memory_load_equality_evidence(
                &left_endpoint.as_term(),
                &right_endpoint.as_term(),
                assumptions,
            )
            .filter(AtomicMemoryLoadEqualityEvidence::is_fully_typed)
            .or_else(|| {
                typed_canonical_projection_load_equality_evidence(
                    &left_endpoint.as_term(),
                    &right_endpoint.as_term(),
                    assumptions,
                )
            })
        });
        EXPLICIT_DAG_CHECK.with(|flag| flag.set(previous));
        evidence.map(|equality| CheckedLoadEqualityEvidence::OriginMemoryDag {
            left: left_endpoint.clone(),
            right: right_endpoint.clone(),
            equality,
        })
    });

    let effect_summary = (direct.is_none() && dag.as_ref().is_none_or(Option::is_none))
        .then(|| {
            assumptions
                .memory_effect_facts_naming(left_endpoint.memory().memory())
                .find_map(|summary| {
                    let Proposition::MemoryEffectSummary {
                        before,
                        after,
                        mutable_ranges,
                        ..
                    } = summary
                    else {
                        return None;
                    };
                    let reversed = if before == left_endpoint.memory().memory()
                        && after == right_endpoint.memory().memory()
                    {
                        false
                    } else if after == left_endpoint.memory().memory()
                        && before == right_endpoint.memory().memory()
                    {
                        true
                    } else {
                        return None;
                    };
                    (left_endpoint.pointer == right_endpoint.pointer)
                        .then(|| {
                            typed_ranges_disjoint_from_pointer_evidence(
                                mutable_ranges,
                                &left_endpoint.pointer,
                                crate::kernel::load_access_width_or_widest(
                                    left_endpoint.memory(),
                                    &left_endpoint.pointer,
                                ),
                                assumptions,
                            )
                        })
                        .flatten()
                        .map(|ranges| CheckedLoadEqualityEvidence::OriginEffectSummary {
                            left: left_endpoint.clone(),
                            right: right_endpoint.clone(),
                            summary: Box::new(summary.clone()),
                            reversed,
                            ranges,
                        })
                })
        })
        .flatten();

    let Some(evidence) = direct.or_else(|| dag.flatten()).or(effect_summary) else {
        return false;
    };
    retain_checked_load_equality(CheckedLoadEquality {
        left: left.clone(),
        right: right.clone(),
        evidence,
    });
    true
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum AddressOffsetEqualityEvidence {
    Exact,
    Add {
        first: Box<AddressOffsetEqualityEvidence>,
        second: Box<AddressOffsetEqualityEvidence>,
        swapped: bool,
    },
    Int32Scaled {
        byte_width: i64,
        values: AtomicMemoryLoadEqualityEvidence,
    },
}

pub(super) fn address_offset_equality_evidence(
    left: &AddressOffset,
    right: &AddressOffset,
    assumptions: &PureFactContext,
) -> Option<AddressOffsetEqualityEvidence> {
    if left == right {
        return Some(AddressOffsetEqualityEvidence::Exact);
    }
    match (left.view(), right.view()) {
        (OffsetView::Add(left_a, left_b), OffsetView::Add(right_a, right_b)) => {
            if let Some((first, second)) =
                address_offset_equality_evidence(left_a, right_a, assumptions).zip(
                    address_offset_equality_evidence(left_b, right_b, assumptions),
                )
            {
                return Some(AddressOffsetEqualityEvidence::Add {
                    first: Box::new(first),
                    second: Box::new(second),
                    swapped: false,
                });
            }
            let (first, second) =
                address_offset_equality_evidence(left_a, right_b, assumptions).zip(
                    address_offset_equality_evidence(left_b, right_a, assumptions),
                )?;
            Some(AddressOffsetEqualityEvidence::Add {
                first: Box::new(first),
                second: Box::new(second),
                swapped: true,
            })
        }
        (
            OffsetView::Int32Scaled {
                index: left,
                byte_width: left_width,
            },
            OffsetView::Int32Scaled {
                index: right,
                byte_width: right_width,
            },
        ) if left_width == right_width => {
            let left = left.operand_view().read_source()?;
            let right = right.operand_view().read_source()?;
            let values = atomic_memory_load_equality_evidence(&left, &right, assumptions)?;
            values
                .is_fully_typed()
                .then_some(AddressOffsetEqualityEvidence::Int32Scaled {
                    byte_width: left_width,
                    values,
                })
        }
        _ => None,
    }
}

impl AddressOffsetEqualityEvidence {
    pub(super) fn checks(
        &self,
        left: &AddressOffset,
        right: &AddressOffset,
        assumptions: &PureFactContext,
    ) -> bool {
        match self {
            Self::Exact => left == right,
            Self::Add {
                first,
                second,
                swapped,
            } => {
                let (OffsetView::Add(left_a, left_b), OffsetView::Add(right_a, right_b)) =
                    (left.view(), right.view())
                else {
                    return false;
                };
                let (right_first, right_second) = if *swapped {
                    (right_b, right_a)
                } else {
                    (right_a, right_b)
                };
                first.checks(left_a, right_first, assumptions)
                    && second.checks(left_b, right_second, assumptions)
            }
            Self::Int32Scaled { byte_width, values } => {
                let (
                    OffsetView::Int32Scaled {
                        index: left,
                        byte_width: left_width,
                    },
                    OffsetView::Int32Scaled {
                        index: right,
                        byte_width: right_width,
                    },
                ) = (left.view(), right.view())
                else {
                    return false;
                };
                if left_width != *byte_width || right_width != *byte_width {
                    return false;
                }
                let (Some(left), Some(right)) = (
                    left.operand_view().read_source(),
                    right.operand_view().read_source(),
                ) else {
                    return false;
                };
                values.checks(
                    &Proposition::condition_is(
                        OldConditionTerm::equal(left.into_owned(), right.into_owned()),
                        true,
                    ),
                    assumptions,
                )
            }
        }
    }
}

impl AtomicMemoryLoadEqualityEvidence {
    /// Whether this evidence uses only rule families whose local structural
    /// checker is implemented. This inspects the already-built object; it
    /// does not walk the memory DAG or consult assumptions again.
    pub(super) fn is_fully_typed(&self) -> bool {
        let equality = match self {
            Self::SameCell(equality) | Self::SameCellViaCanonicalProjection { equality, .. } => {
                equality
            }
            Self::LeftResolvesToRight { .. } | Self::RightResolvesToLeft { .. } => return false,
        };
        matches!(
            equality,
            MemoryDagLoadEqualityEvidence {
                left,
                right,
                reason: MemoryDagLoadEqualityReason::CommonSource
                    | MemoryDagLoadEqualityReason::LeftRetainsRightRead
                    | MemoryDagLoadEqualityReason::RightRetainsLeftRead,
            } if left.has_only_typed_hops() && right.has_only_typed_hops()
        )
    }

    /// Check the currently completed typed subset of retained DAG equality
    /// evidence. Unsupported terminal-value and assumption-dependent edge
    /// proofs return false instead of invoking a solver.
    pub(super) fn checks(&self, proposition: &Proposition, assumptions: &PureFactContext) -> bool {
        // Both equality widths, because what this evidence proves is
        // width-independent: that the two states hold one version of the
        // cell at one address. How many bytes the C access reads is the
        // walk's own input, taken from the load registry on both the
        // construction and the checking side, not something the goal's
        // carrier decides.
        let Some((
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            }
            | OldConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            true,
        )) = proposition.old_condition()
        else {
            return false;
        };
        let (equality, left_projection, right_projection) = match self {
            Self::SameCell(equality) => (equality, None, None),
            Self::SameCellViaCanonicalProjection {
                equality,
                left_projection,
                right_projection,
            } => (
                equality,
                left_projection.as_ref(),
                right_projection.as_ref(),
            ),
            Self::LeftResolvesToRight { .. } | Self::RightResolvesToLeft { .. } => return false,
        };
        let MemoryDagLoadEqualityEvidence {
            left: left_evidence,
            right: right_evidence,
            reason,
        } = equality;
        let (
            OldMachineTerm::MemoryLoad(left_memory, left_pointer, left_kind),
            OldMachineTerm::MemoryLoad(right_memory, right_pointer, right_kind),
        ) = (left.as_ref(), right.as_ref())
        else {
            return false;
        };
        let left_start = match left_projection {
            Some(projection) if projection.checks(left_memory.shared_memory(), left_pointer) => {
                &projection.source
            }
            Some(_) => return false,
            None => left_memory.shared_memory(),
        };
        let right_start = match right_projection {
            Some(projection) if projection.checks(right_memory.shared_memory(), right_pointer) => {
                &projection.source
            }
            Some(_) => return false,
            None => right_memory.shared_memory(),
        };
        left_pointer.address() == right_pointer.address()
            && left_kind == right_kind
            && match reason {
                MemoryDagLoadEqualityReason::CommonSource => {
                    left_evidence.node() == right_evidence.node()
                }
                MemoryDagLoadEqualityReason::LeftRetainsRightRead => {
                    retained_cell_names_load(left_evidence, right_start, left_pointer, *left_kind)
                }
                MemoryDagLoadEqualityReason::RightRetainsLeftRead => {
                    retained_cell_names_load(right_evidence, left_start, left_pointer, *left_kind)
                }
                MemoryDagLoadEqualityReason::EqualResolvedValue(_) => false,
            }
            && left_evidence.checks_walk_from(
                left_start,
                left_pointer,
                crate::kernel::load_term_access_width(left_start, left_pointer, *left_kind),
                assumptions,
            )
            && right_evidence.checks_walk_from(
                right_start,
                right_pointer,
                crate::kernel::load_term_access_width(right_start, right_pointer, *right_kind),
                assumptions,
            )
    }
}

/// Connect pointer-observable canonical projections back to one exact source
/// before asking the ordinary memory DAG for a common cell. There are only
/// three additional combinations, so evidence construction stays bounded;
/// checking the selected result performs exact registry lookups and the two
/// retained DAG walks only.
fn typed_canonical_projection_load_equality_evidence(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> Option<AtomicMemoryLoadEqualityEvidence> {
    let (
        OldMachineTerm::MemoryLoad(left_memory, left_pointer, left_kind),
        OldMachineTerm::MemoryLoad(right_memory, right_pointer, right_kind),
    ) = (left, right)
    else {
        return None;
    };
    if left_pointer.address() != right_pointer.address() || left_kind != right_kind {
        return None;
    }
    let left_projection =
        CanonicalLoadProjectionEvidence::for_endpoint(left_memory.shared_memory(), left_pointer);
    let right_projection =
        CanonicalLoadProjectionEvidence::for_endpoint(right_memory.shared_memory(), right_pointer);
    let candidates = [
        (left_projection.as_ref(), None),
        (None, right_projection.as_ref()),
        (left_projection.as_ref(), right_projection.as_ref()),
    ];
    for (left_selected, right_selected) in candidates {
        if left_selected.is_none() && right_selected.is_none() {
            continue;
        }
        let left_start = left_selected
            .map(|projection| &projection.source)
            .unwrap_or(left_memory.shared_memory());
        let right_start = right_selected
            .map(|projection| &projection.source)
            .unwrap_or(right_memory.shared_memory());
        let Some(equality) = memory_load_equality_evidence_at(
            left_start,
            right_start,
            left_pointer,
            *left_kind,
            assumptions,
        ) else {
            continue;
        };
        let evidence = AtomicMemoryLoadEqualityEvidence::SameCellViaCanonicalProjection {
            equality,
            left_projection: left_selected.cloned(),
            right_projection: right_selected.cloned(),
        };
        if evidence.is_fully_typed() {
            return Some(evidence);
        }
    }
    None
}

// The extended DAG bridging (crossing block-declaration and cell-forgetting
// edges, range-certificate store hops, stored-value pinning, and the
// order-path load matching in assumptions.rs) runs ONLY inside the loadable
// prover. Everywhere else — execution pruning, load canonicalization, solve
// planning — behavior must stay byte-identical to the pre-arc path, because
// certified forms and case-split structure check against it. The flag
// is scoped, not global, so generation and check of the same query always
// agree.
thread_local! {
    static EXTENDED_DAG_BRIDGING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static EXPLICIT_DAG_CHECK: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(super) fn extended_dag_bridging_active() -> bool {
    EXTENDED_DAG_BRIDGING.with(std::cell::Cell::get)
}

/// True while explicit certificate validation widens the DAG walk (see
/// `explicit_atomic_equality_from_memory_derivations`); resolution answers
/// computed in that mode must not be shared with the planner-facing arms.
pub(super) fn explicit_dag_check_active() -> bool {
    EXPLICIT_DAG_CHECK.with(std::cell::Cell::get)
}

struct ExplicitReadScope(bool);
impl Drop for ExplicitReadScope {
    fn drop(&mut self) {
        EXPLICIT_DAG_CHECK.with(|flag| flag.set(self.0));
    }
}

/// Runs `body` with the extended DAG bridging enabled (see above).
pub(super) fn with_extended_dag_bridging<T>(body: impl FnOnce() -> T) -> T {
    let previous = EXTENDED_DAG_BRIDGING.with(|flag| flag.replace(true));
    let result = body();
    EXTENDED_DAG_BRIDGING.with(|flag| flag.set(previous));
    result
}

pub(in crate::kernel) fn forward_range_offset_from_pointer(
    range: &MemoryRange,
    pointer: &Address,
) -> Option<SharedMachineIntegerTerm> {
    if range.base.base != pointer.base {
        return None;
    }
    let OffsetView::Add(left, right) = range.base.offset.view() else {
        return None;
    };
    if pointer.offset == *left {
        shared_element_index_from_offset(right, range.element_width())
    } else if pointer.offset == *right {
        shared_element_index_from_offset(left, range.element_width())
    } else {
        None
    }
}

/// The whole-element index of `pointer` in a range based at `base` whose
/// elements are `element_width` bytes wide.
///
/// Two units meet here and are easy to confuse: the byte distance this
/// computes between two addresses, and the element counts a range's bounds
/// are written in. Dividing the bytes by anything but the range's own
/// element width answers in a unit the bounds are not written in, so a
/// `uint8` range's bounds would be read as `int32` indices and a pointer
/// range's element one would be its own byte four.
///
/// An address part-way into an element has no element index at all. Byte four
/// of an eight-byte element is *inside* element zero, not element one, and a
/// caller asking "is this outside the range" must not be handed "element one"
/// for it. `None` is the honest answer, and it declines the ladder.
pub(in crate::kernel) fn direct_constant_element_index(
    pointer: &Address,
    base: &Address,
    element_width: u32,
) -> Option<i64> {
    let element_width = i64::from(element_width);
    if element_width <= 0 {
        return None;
    }
    let bytes = crate::kernel::assumptions::signed_index_constant(
        shared_pointer_byte_offset_from_base(pointer, base)?.operand_view(),
    )?;
    (bytes % element_width == 0).then_some(bytes / element_width)
}

/// How many of a range's elements a `bytes`-wide access covers, rounded up: an
/// access is only outside the range when *every* element it touches is.
pub(in crate::kernel) fn access_element_span(bytes: u32, element_width: u32) -> Option<i64> {
    (element_width > 0).then(|| i64::from(bytes.div_ceil(element_width).max(1)))
}

// Probe the original indexed spelling as well as one exact concrete alias.
// Aliases only choose buckets; retained membership still authenticates the
// original address and every byte of the access.
fn separation_index_blocks(pointer: &Address, assumptions: &PureFactContext) -> Vec<AddressBase> {
    let mut blocks = vec![pointer.base.clone()];
    if let Some(alias) = assumptions.exact_pointer_aliases(pointer).find(|alias| {
        !matches!(
            alias.base,
            AddressBase::Symbolic(_) | AddressBase::FunctionSymbolic(_)
        )
    }) && alias.base != pointer.base
    {
        blocks.push(alias.base.clone());
    }
    blocks
}

/// Whether the `bytes` bytes at `pointer` can be shown to miss every byte of
/// `range`.
///
/// `bytes` is the access width, and it is not decoration: a range is a byte
/// footprint, and an access wider than one element reaches past the element
/// its address names. Each route below therefore has to clear the whole
/// access, not just its first byte.
pub(in crate::kernel) fn typed_range_disjoint_from_pointer_evidence(
    range: &MemoryRange,
    pointer: &Address,
    bytes: u32,
    assumptions: &PureFactContext,
) -> Option<RangeDisjointFromPointerEvidence> {
    let (start, end) = range.bound_terms();
    if start == end {
        crate::instrumentation::record_deterministic_work(1);
        return Some(RangeDisjointFromPointerEvidence::Empty);
    }
    if range.base.blocks_proven_distinct(pointer) {
        return Some(RangeDisjointFromPointerEvidence::DistinctBlocks);
    }
    // The checked borrowed descriptor and backing owner are indexed by the
    // two selected addresses. Retain their complete bounds, just as the
    // single-store frame does, before considering ambient separation facts.
    if let Some((resources, range_member, access_member)) = assumptions
        .borrow_partition_separated_members(
            range.base(),
            pointer,
            |member| {
                crate::kernel::assumptions::memory_range_shallowly_contained_with_facts(
                    range,
                    member,
                    assumptions,
                )
            },
            |member| {
                AccessInRangeEvidence::for_access(pointer, bytes, member, assumptions).is_some()
            },
        )
        && !assumptions.memory_ranges_overlap_after_base_equality(range_member, access_member)
    {
        let membership =
            AccessInRangeEvidence::for_access(pointer, bytes, access_member, assumptions)?;
        crate::kernel::record_implicit_consulted_premises(
            assumptions,
            &Proposition::ResourceComposition(resources.clone()),
        );
        return Some(RangeDisjointFromPointerEvidence::BorrowPartition(Box::new(
            BorrowPartitionRangeEvidence {
                resources: resources.clone(),
                range_member: range_member.clone(),
                access_member: access_member.clone(),
                membership,
            },
        )));
    }
    let range_blocks = separation_index_blocks(range.base(), assumptions);
    let access_blocks = separation_index_blocks(pointer, assumptions);
    for (fact, left, right) in range_blocks.iter().flat_map(|range_block| {
        access_blocks.iter().flat_map(move |access_block| {
            assumptions.memory_separation_candidates(range_block, access_block)
        })
    }) {
        if fact.memory_separation().is_none()
            || assumptions.memory_ranges_overlap_after_base_equality(left, right)
        {
            continue;
        }
        crate::instrumentation::record_deterministic_work(1);
        for (range_member, access_member) in [(left, right), (right, left)] {
            if !crate::kernel::assumptions::memory_range_shallowly_contained_with_facts(
                range,
                range_member,
                assumptions,
            ) {
                continue;
            }
            let Some(membership) =
                AccessInRangeEvidence::for_access(pointer, bytes, access_member, assumptions)
            else {
                continue;
            };
            crate::kernel::record_implicit_consulted_premises(assumptions, fact);
            return Some(RangeDisjointFromPointerEvidence::ExactSeparationFact(
                Box::new(SeparatedRangeEvidence {
                    fact: fact.clone(),
                    range_member: range_member.clone(),
                    access_member: access_member.clone(),
                    membership,
                }),
            ));
        }
    }
    // Native footprints need native separation evidence, never a signed
    // forward-offset certificate. Distinct blocks and exact facts above
    // already retain their complete typed spans.
    if range.wide_bounds().is_some() {
        return None;
    }
    let element_width = range.element_width();
    if let (Some(index), Some(span), Some(start), Some(end)) = (
        direct_constant_element_index(pointer, range.base(), element_width),
        access_element_span(bytes, element_width),
        range.signed_constant_start(),
        range.signed_constant_end(),
    ) && (index.checked_add(span).is_some_and(|last| last <= start) || end <= index)
    {
        return Some(RangeDisjointFromPointerEvidence::DirectConstantOutside {
            index,
            bytes,
            start,
            end,
        });
    }
    // The forward-offset route proves the range begins strictly after this
    // address, which is a gap of one element. That clears an access only as
    // wide as an element; anything wider reaches into the range's first one.
    if bytes > element_width {
        return None;
    }
    let offset = forward_range_offset_from_pointer(range, pointer)?;
    let range_start = crate::kernel::assumptions::index_binary(
        MachineBinaryOp::Add,
        offset.operand_view(),
        MachineOperandView::Old(range.start()),
    );
    let positive = PositiveTermEvidence::for_view(range_start.operand_view(), assumptions)?;
    Some(RangeDisjointFromPointerEvidence::ForwardOffset { offset, positive })
}

/// Shared cheap byte-separation rule for cache retention and read-over-store.
/// Numeric address geometry is consulted before separation authority: a known
/// partial overlap invalidates an old partition just as an equal base does.
/// Stated authority is indexed by the two anchors, not their shared C block.
pub(in crate::kernel) fn indexed_store_byte_separation_evidence(
    write: &Address,
    write_bytes: u32,
    pointer: &Address,
    load_bytes: u32,
    assumptions: &PureFactContext,
) -> Option<MemoryDagHopJustification> {
    use crate::kernel::reasoning::AccessByteOverlap;
    let numeric = assumptions.numeric_access_byte_overlap(write, write_bytes, pointer, load_bytes);
    match numeric {
        Some(AccessByteOverlap::Overlaps) => return None,
        Some(AccessByteOverlap::Separate) => {
            return Some(MemoryDagHopJustification::StoreAddressByteSeparation);
        }
        _ => {}
    }
    if write.base == pointer.base
        && crate::kernel::reasoning::exact_access_byte_overlap(
            write,
            write_bytes,
            pointer,
            load_bytes,
        ) == Some(AccessByteOverlap::Separate)
    {
        return Some(MemoryDagHopJustification::StoreAddressByteSeparation);
    }
    if assumptions.pointers_proven_equal_ignoring_memory_separation(write, pointer) {
        return None;
    }
    let check_stated = |proposition: &Proposition| {
        crate::instrumentation::record_deterministic_work(1);
        let (left, right) = proposition.memory_separation()?;
        let (orientation, write_membership, load_membership) = if let (Some(w), Some(r)) = (
            AccessInRangeEvidence::for_access(write, write_bytes, left, assumptions),
            AccessInRangeEvidence::for_access(pointer, load_bytes, right, assumptions),
        ) {
            (StoreSeparatedRangeOrientation::WriteLeftLoadRight, w, r)
        } else if let (Some(w), Some(r)) = (
            AccessInRangeEvidence::for_access(write, write_bytes, right, assumptions),
            AccessInRangeEvidence::for_access(pointer, load_bytes, left, assumptions),
        ) {
            (StoreSeparatedRangeOrientation::WriteRightLoadLeft, w, r)
        } else {
            return None;
        };
        if assumptions.memory_ranges_overlap_after_base_equality(left, right) {
            return None;
        }
        crate::kernel::record_implicit_consulted_premises(assumptions, proposition);
        Some(MemoryDagHopJustification::StoreSeparatedRanges {
            authority: StoreSeparatedRangesAuthority::ExactProposition(proposition.clone()),
            left: left.clone(),
            right: right.clone(),
            orientation,
            write_membership,
            load_membership,
        })
    };
    assumptions
        .anchored_memory_separation_candidates(write, pointer)
        .find_map(check_stated)
        .or_else(|| {
            assumptions
                .separated_address_classes
                .candidates(write, pointer, &assumptions.equality_graph)
                .iter()
                .find_map(check_stated)
        })
        .or_else(|| {
            owned_composition_store_separated_evidence_impl(
                write,
                write_bytes,
                pointer,
                load_bytes.into(),
                assumptions,
                true,
            )
        })
}

pub(in crate::kernel) fn typed_store_separated_ranges_evidence(
    write: &Address,
    write_bytes: impl Into<crate::kernel::AccessExtent>,
    pointer: &Address,
    load_bytes: impl Into<crate::kernel::AccessExtent>,
    assumptions: &PureFactContext,
) -> Option<MemoryDagHopJustification> {
    let (write_bytes, load_bytes) = (write_bytes.into(), load_bytes.into());
    if crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
        write,
        pointer,
        assumptions,
    ) {
        return None;
    }
    // A single stated equality can give an opaque read the spelling used by
    // the range index. Membership retains and checks that equality; this
    // lookup grants neither a separation nor memory access on its own.
    let resolved_write = assumptions
        .exact_pointer_aliases(write)
        .find(|alias| {
            !matches!(
                alias.base,
                AddressBase::Symbolic(_) | AddressBase::FunctionSymbolic(_)
            )
        })
        .unwrap_or(write);
    let resolved_load = assumptions
        .exact_pointer_aliases(pointer)
        .find(|alias| {
            !matches!(
                alias.base,
                AddressBase::Symbolic(_) | AddressBase::FunctionSymbolic(_)
            )
        })
        .unwrap_or(pointer);
    let stated = assumptions
        .memory_separation_candidates(&resolved_write.base, &resolved_load.base)
        .find_map(|(proposition, left, right)| {
            proposition.memory_separation()?;
            let (orientation, write_membership, load_membership) =
                if let (Some(write_membership), Some(load_membership)) = (
                    AccessInRangeEvidence::for_access(write, write_bytes, left, assumptions),
                    AccessInRangeEvidence::for_access(pointer, load_bytes, right, assumptions),
                ) {
                    (
                        StoreSeparatedRangeOrientation::WriteLeftLoadRight,
                        write_membership,
                        load_membership,
                    )
                } else if let (Some(write_membership), Some(load_membership)) = (
                    AccessInRangeEvidence::for_access(write, write_bytes, right, assumptions),
                    AccessInRangeEvidence::for_access(pointer, load_bytes, left, assumptions),
                ) {
                    (
                        StoreSeparatedRangeOrientation::WriteRightLoadLeft,
                        write_membership,
                        load_membership,
                    )
                } else {
                    return None;
                };
            if assumptions.memory_ranges_overlap_after_base_equality(left, right) {
                return None;
            }
            crate::kernel::record_implicit_consulted_premises(assumptions, proposition);
            Some(MemoryDagHopJustification::StoreSeparatedRanges {
                authority: StoreSeparatedRangesAuthority::ExactProposition(proposition.clone()),
                left: left.clone(),
                right: right.clone(),
                orientation,
                write_membership,
                load_membership,
            })
        });
    if stated.is_some() {
        return stated;
    }
    // A checked borrowed projection remains separate from current ownership.
    // Query only address-keyed exposed members; no recursive expansion or
    // pairwise separation facts are constructed.
    if let Some((resources, left, right)) = assumptions.borrow_partition_separated_members(
        resolved_write,
        resolved_load,
        |range| AccessInRangeEvidence::for_access(write, write_bytes, range, assumptions).is_some(),
        |range| {
            AccessInRangeEvidence::for_access(pointer, load_bytes, range, assumptions).is_some()
        },
    ) {
        let write_membership =
            AccessInRangeEvidence::for_access(write, write_bytes, left, assumptions)?;
        let load_membership =
            AccessInRangeEvidence::for_access(pointer, load_bytes, right, assumptions)?;
        return Some(MemoryDagHopJustification::StoreSeparatedRanges {
            authority: StoreSeparatedRangesAuthority::BorrowPartition(resources.clone()),
            left: left.clone(),
            right: right.clone(),
            orientation: StoreSeparatedRangeOrientation::WriteLeftLoadRight,
            write_membership,
            load_membership,
        });
    }
    // The composition law asked on demand: an owned member holding the
    // written address and a different one holding the read.
    let (resources, left, right) = assumptions.composition_separated_members(
        write,
        pointer,
        |range| AccessInRangeEvidence::for_access(write, write_bytes, range, assumptions).is_some(),
        |range| {
            AccessInRangeEvidence::for_access(pointer, load_bytes, range, assumptions).is_some()
        },
        |left, right| !assumptions.memory_ranges_overlap_after_base_equality(left, right),
    )?;
    let write_membership =
        AccessInRangeEvidence::for_access(write, write_bytes, left, assumptions)?;
    let load_membership =
        AccessInRangeEvidence::for_access(pointer, load_bytes, right, assumptions)?;
    crate::kernel::record_implicit_consulted_premises(
        assumptions,
        &Proposition::ResourceComposition(resources.clone()),
    );
    Some(MemoryDagHopJustification::StoreSeparatedRanges {
        authority: StoreSeparatedRangesAuthority::ResourceComposition(resources.clone()),
        left: left.clone(),
        right: right.clone(),
        orientation: StoreSeparatedRangeOrientation::WriteLeftLoadRight,
        write_membership,
        load_membership,
    })
}

/// Whether one separating resource composition in the context tells a store
/// apart from a load, and the evidence that says so.
///
/// **The rule.** A store is separate from a load when some valid composition
/// in the context owns both addresses through *different* members. Two owned
/// memory facts of one composition hold disjoint bytes — that is the
/// partition invariant, enforced at every insertion by
/// `MemoryResourceAlgebra::pair_validity_error`, whose
/// `OverlappingOwnedMemoryResources` is the error a context violating it
/// raises, and stated as a law by `observable_facts_assuming_valid`: "two
/// owned members are pairwise separate". `owns value[0..1]` beside
/// `owns Cell(result)` is the shape that needs it: `value` is an
/// `ExternalArgument` address and `result` is a pointer a callback returned,
/// so `proven_distinct` separates them from nothing and no offset relates
/// them. Ownership is the only thing that does.
///
/// **Why a composition fact survives the step it is used across.** What the
/// two members yield is a claim about *addresses*, and an address is a value.
/// The ranges are spelled with pointer terms whose loads carry their own
/// state, so each denotes one fixed address however far the proof has
/// moved on; a store cannot move the bytes a range named, and consuming,
/// transferring or freeing a resource does not make two address ranges that
/// were disjoint coincide. The composition is therefore not being read as a
/// statement about the state at the point of use — which is the reading that
/// would need the resource to still be held — but as a statement about two
/// addresses, which is as true afterwards as it was when it was recorded.
///
/// **Where it may be spent.** Only on the fact-consulting route, exactly
/// where a typed `separate(..)` is spent today: composition facts are path
/// facts, and the two naming walks must not read one, because their answers
/// are embedded in a term's name and memoized across every path that reaches
/// the same interned state. Both walks pass `PureFactContext::new()`
/// (`resource_tracker::cell_source_for_naming` and the block-version walk in
/// `resource_tracker::mod`), so an empty composition set is what this
/// function is handed there and it can decide nothing; on the querying route
/// the answer is re-derived per query and keyed by the context
/// (`resolution_query_memo_id`), never stored on an interned edge.
///
/// **Cost.** Exact bases and their indexed one-hop aliases are tried first,
/// followed by the existing interior block-bucket lookup. There is no expansion:
/// a composite that is still folded simply does not answer. This runs as the
/// last disjunct of a load-framing ladder, after every cheaper check has failed.
pub(in crate::kernel) fn owned_composition_store_separated_evidence(
    write: &Address,
    write_bytes: u32,
    pointer: &Address,
    load_bytes: impl Into<crate::kernel::AccessExtent>,
    assumptions: &PureFactContext,
) -> Option<MemoryDagHopJustification> {
    owned_composition_store_separated_evidence_impl(
        write,
        write_bytes,
        pointer,
        load_bytes.into(),
        assumptions,
        false,
    )
}

#[cfg(test)]
thread_local! {
    static COMPOSITION_STORE_ALIAS_QUERIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn count_composition_store_alias_queries<R>(
    operation: impl FnOnce() -> R,
) -> (R, usize) {
    let before = COMPOSITION_STORE_ALIAS_QUERIES.with(std::cell::Cell::get);
    let result = operation();
    let after = COMPOSITION_STORE_ALIAS_QUERIES.with(std::cell::Cell::get);
    (result, after - before)
}

fn owned_composition_store_separated_evidence_impl(
    write: &Address,
    write_bytes: u32,
    pointer: &Address,
    load_bytes: crate::kernel::AccessExtent,
    assumptions: &PureFactContext,
    indexed_only: bool,
) -> Option<MemoryDagHopJustification> {
    let same_pointer = || {
        #[cfg(test)]
        COMPOSITION_STORE_ALIAS_QUERIES.with(|count| count.set(count.get() + 1));
        crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
            write,
            pointer,
            assumptions,
        )
    };
    if assumptions.resource_compositions.is_empty() {
        return None;
    }
    let alias_equal = std::cell::OnceCell::new();
    crate::instrumentation::measure_operation(
        "kernel",
        "general pointer distinctness",
        "composition-owned store separation",
        || {
            let write_bases = store_member_probe_bases(write, assumptions);
            let load_bases = store_member_probe_bases(pointer, assumptions);
            let compositions: Box<dyn Iterator<Item = &ResourceContext>> =
                match assumptions.store_owners() {
                    Some(owners) => Box::new(owners.iter()),
                    // Only a composition listed under a key of both objects'
                    // members can hold the pair (`CompositionMemberIndex`).
                    None => Box::new(
                        assumptions
                            .composition_members
                            .listed_under(
                                write_bases.iter().chain(&load_bases),
                                [&write.base, &pointer.base]
                                    .into_iter()
                                    .filter(|_| !indexed_only),
                            )
                            .into_iter(),
                    ),
                };
            compositions.into_iter().find_map(|resources| {
                crate::instrumentation::record_deterministic_work(1);
                if !resources.has_multiple_owned_memory_members() {
                    return None;
                }
                let member = |pointer: &Address, bases: &[Address]| {
                    bases
                        .iter()
                        .find_map(|candidate| {
                            resources.owned_memory_members_with_base(candidate).find(
                                |(_, range)| {
                                    PointerInRangeEvidence::for_pointer(pointer, range, assumptions)
                                        .is_some()
                                },
                            )
                        })
                        .or_else(|| {
                            (!indexed_only)
                                .then(|| resources.owned_memory_member_containing_pointer(pointer))
                                .flatten()
                        })
                };
                let (write_entry, left) = member(write, &write_bases)?;
                let (load_entry, right) = member(pointer, &load_bases)?;
                if write_entry == load_entry {
                    return None;
                }
                let (left, right) = (left.clone(), right.clone());
                let write_membership =
                    AccessInRangeEvidence::for_access(write, write_bytes, &left, assumptions)?;
                let load_membership =
                    AccessInRangeEvidence::for_access(pointer, load_bytes, &right, assumptions)?;
                // Only a viable pair needs the alias veto. Reuse that one
                // answer if another composition supplies the same question.
                if *alias_equal.get_or_init(&same_pointer) {
                    return None;
                }
                if assumptions.memory_ranges_overlap_after_base_equality(&left, &right) {
                    return None;
                }
                crate::kernel::record_implicit_consulted_premises(
                    assumptions,
                    &Proposition::ResourceComposition(resources.clone()),
                );
                Some(MemoryDagHopJustification::StoreSeparatedRanges {
                    authority: StoreSeparatedRangesAuthority::ResourceComposition(
                        resources.clone(),
                    ),
                    left,
                    right,
                    orientation: StoreSeparatedRangeOrientation::WriteLeftLoadRight,
                    write_membership,
                    load_membership,
                })
            })
        },
    )
}

/// The bases a store-separation member lookup probes for `pointer`, in
/// order: each syntactic base prefix followed by its exact aliases. A
/// reconstructed resource may use a proof pointer for the same object that C
/// names through a parameter; every hit still needs checked membership.
fn store_member_probe_bases(pointer: &Address, assumptions: &PureFactContext) -> Vec<Address> {
    let mut bases = Vec::new();
    let mut base = pointer.clone();
    loop {
        bases.push(base.clone());
        bases.extend(assumptions.exact_pointer_aliases(&base).cloned());
        let next = match base.offset.view() {
            OffsetView::Add(left, _) => left.clone(),
            OffsetView::Constant(value) if value != 0 => AddressOffset::constant(0),
            // A loaded pointer's displacement is all of its offset: the
            // read itself, at displacement zero, is the object's base.
            OffsetView::Int32Scaled { .. } | OffsetView::Int64Scaled { .. }
                if matches!(base.base, AddressBase::Load(_) | AddressBase::SliceData(_)) =>
            {
                AddressOffset::constant(0)
            }
            _ => break,
        };
        base.set_offset(next);
    }
    bases
}

pub(in crate::kernel) fn typed_ranges_disjoint_from_pointer_evidence(
    ranges: &[MemoryRange],
    pointer: &Address,
    bytes: u32,
    assumptions: &PureFactContext,
) -> Option<Vec<RangeDisjointFromPointerEvidence>> {
    ranges
        .iter()
        .map(|range| {
            // Even an immediate distinct-block hit visits one write range.
            // Charge lazily so a refusal pays only for the visited prefix.
            crate::instrumentation::record_deterministic_work(1);
            typed_range_disjoint_from_pointer_evidence(range, pointer, bytes, assumptions)
        })
        .collect()
}

/// A typed pointer read may recover a stored pointer in a different block.
/// Compare the complete stored value, never just its offset.
pub(crate) fn pointer_read_has_stored_value(
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> bool {
    pointer_read_stored_value(left, assumptions, None).is_some_and(|stored| {
        stored.address() == right || assumptions.pointers_known_equal(stored.address(), right)
    })
}

/// Canonical load projections retain all potentially observable scalar bytes
/// (up to MAX_SCALAR_ACCESS_BYTES). Reuse the producer's retained source for
/// a complete pointer read, whose eight bytes fit that projection, so its
/// selected memory history is available without rebuilding either state.
fn complete_pointer_read_source(read: &LoadedPointerView) -> SharedMemory {
    canonical_load_projection_source(&read.defining_memory, &read.defining_address)
        .unwrap_or_else(|| read.defining_memory.clone())
}

/// Whether two reads at addresses the caller proved equal see the bytes of
/// one cell source. Reads of one state are one read. Each may also be a
/// projection of a different state, which it agrees with at its own cell.
/// Compare their retained sources using only immediate checked transitions;
/// longer preservation arguments must be supplied as explicit equalities.
pub(in crate::kernel) fn pointer_reads_see_one_cell_source(
    left: &LoadedPointerView,
    right: &LoadedPointerView,
    assumptions: &PureFactContext,
) -> bool {
    if left.defining_memory == right.defining_memory {
        return true;
    }
    let left_memory = complete_pointer_read_source(left);
    let right_memory = complete_pointer_read_source(right);
    left_memory == right_memory
        || typed_reads_share_memory_source(
            &left_memory,
            &right_memory,
            &left.defining_address,
            crate::kernel::C_POINTER_BYTE_WIDTH,
            assumptions,
        )
}

/// Storage identity is numeric: two complete reads of the same bytes carry
/// the same pointer value even when their access pointers have distinct bounds.
/// This query is confined to actual read origins, never access authority.
fn pointer_read_addresses_equal(
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> bool {
    if crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
        left,
        right,
        assumptions,
    ) {
        return true;
    }
    assumptions.equality_graph.are_uint64_equal(
        &OldMachineTerm::integer_address(left.clone()),
        &OldMachineTerm::integer_address(right.clone()),
    )
}

/// Equal complete read applications across a frame denote equal numeric
/// addresses too. This rule is used only when comparing complete C pointers;
/// ordinary scalar load variables cannot acquire a typed read from it.
pub(in crate::kernel) fn complete_pointer_reads_equal_across_frame(
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> bool {
    // A symbolic read identity denotes a complete read only when its typed
    // producer retained this exact definition. Never infer one from a scalar
    // load variable, matching arithmetic, or a different pointee stride.
    let read = |value: &Address| {
        value.as_loaded_value().or_else(|| {
            let OldMachineTerm::MemoryLoad(memory, address, LoadKind::Int32) =
                crate::kernel::equality_graph::logical_pointer_read_term(value)?
            else {
                return None;
            };
            Address::loaded_value_at(&memory, &address).as_loaded_value()
        })
    };
    let (Some(a), Some(b)) = (read(left), read(right)) else {
        return false;
    };
    if !crate::kernel::reasoning::pointer_offsets_proven_equal_for_memory_resolution(
        &a.displacement,
        &b.displacement,
        assumptions,
    ) || !pointer_read_addresses_equal(&a.defining_address, &b.defining_address, assumptions)
    {
        return false;
    }
    let a_memory = complete_pointer_read_source(&a);
    let b_memory = complete_pointer_read_source(&b);
    if typed_reads_share_memory_source(
        &a_memory,
        &b_memory,
        &a.defining_address,
        crate::kernel::C_POINTER_BYTE_WIDTH,
        assumptions,
    ) {
        return true;
    }
    // A seeded pointer cell can name a read from an earlier source rather
    // than the seed edge's immediate parent. Follow the existing typed cell
    // source evidence for the two explicitly compared reads; cached values
    // alone do not establish agreement across writes.
    let _scope = ExplicitReadScope(EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true)));
    with_extended_dag_bridging(|| {
        let left = memory_dag_cell_source(
            &a_memory,
            &a.defining_address,
            crate::kernel::C_POINTER_BYTE_WIDTH,
            assumptions,
            true,
        );
        let right = memory_dag_cell_source(
            &b_memory,
            &a.defining_address,
            crate::kernel::C_POINTER_BYTE_WIDTH,
            assumptions,
            true,
        );
        let (Some(left), Some(right)) = (left, right) else {
            return false;
        };
        let stores_read = |cell: &MemoryDagCell, read: &LoadedPointerView| {
            matches!(cell, MemoryDagCell::Stored { value, .. }
                if matches!(value.native(), ProgramValue::Pointer(value)
                    if value.address() == &Address::loaded_value_at(&read.point, &read.defining_address)))
        };
        left.node() == right.node() || stores_read(&left, &b) || stores_read(&right, &a)
    })
}

pub(in crate::kernel) fn pointer_read_provenance_equal(
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> bool {
    pointer_read_domains_equal(left, right, assumptions, false)
}

pub(in crate::kernel) fn pointer_read_bounds_equal(
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> bool {
    pointer_read_domains_equal(left, right, assumptions, true)
}

fn pointer_read_domains_equal(
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
    bounds: bool,
) -> bool {
    let left_origin = left;
    let right_origin = right;
    let (Some(left), Some(right)) = (left.as_loaded_value(), right.as_loaded_value()) else {
        return false;
    };
    if !pointer_read_addresses_equal(&left.defining_address, &right.defining_address, assumptions) {
        return false;
    }
    if pointer_reads_see_one_cell_source(&left, &right, assumptions) {
        return true;
    }
    let left_memory = complete_pointer_read_source(&left);
    let right_memory = complete_pointer_read_source(&right);
    let Some((a, _)) = memory_dag_cell_source_with_stop(
        &left_memory,
        &left.defining_address,
        crate::kernel::C_POINTER_BYTE_WIDTH,
        assumptions,
        true,
    ) else {
        return false;
    };
    let Some((b, _)) = memory_dag_cell_source_with_stop(
        &right_memory,
        &left.defining_address,
        crate::kernel::C_POINTER_BYTE_WIDTH,
        assumptions,
        true,
    ) else {
        return false;
    };
    if a.node() == b.node() {
        return true;
    }
    let a_value = a.resolved_value(&left.defining_address, LoadKind::Int32);
    let b_value = b.resolved_value(&left.defining_address, LoadKind::Int32);
    if matches!(&a_value, Some(ProgramValue::Pointer(stored)) if if bounds { stored.bounds().is_none() && !stored.bounds_are_known() && stored.bounds_owner() == Some(right_origin) } else { stored.provenance() == right_origin })
        || matches!(&b_value, Some(ProgramValue::Pointer(stored)) if if bounds { stored.bounds().is_none() && !stored.bounds_are_known() && stored.bounds_owner() == Some(left_origin) } else { stored.provenance() == left_origin })
    {
        return true;
    }
    matches!((a_value, b_value),
        (Some(ProgramValue::Pointer(a)), Some(ProgramValue::Pointer(b))) if a == b)
}

/// Recover only an actual complete pointer stored at this read's source.
/// Numeric scalar values and address equalities supply no pointer metadata.
pub(in crate::kernel) fn complete_pointer_read_value(
    origin: &Address,
    assumptions: &PureFactContext,
) -> Option<Pointer> {
    let ProgramValue::Pointer(value) = complete_pointer_carrier_read_value(origin, assumptions)?
    else {
        return None;
    };
    Some(value)
}

pub(in crate::kernel) fn complete_pointer_read_retained_value(
    origin: &Address,
    assumptions: &PureFactContext,
) -> Option<ExecutionValue> {
    complete_pointer_carrier_read_retained_value(origin, assumptions)
        .filter(|value| value.program_type().is_pointer())
}

/// Recover an actual complete pointer or pointer-carrying integer store.
/// Numeric scalar bytes never manufacture a representation record.
pub(in crate::kernel) fn complete_pointer_carrier_read_value(
    origin: &Address,
    assumptions: &PureFactContext,
) -> Option<ProgramValue> {
    complete_pointer_carrier_read_retained_value(origin, assumptions)
        .map(ExecutionValue::into_native)
}

pub(in crate::kernel) fn complete_pointer_carrier_read_retained_value(
    origin: &Address,
    assumptions: &PureFactContext,
) -> Option<ExecutionValue> {
    let read = origin.as_loaded_value()?;
    if let Some(stored) = read.point.indexed_stored_value() {
        return (!stored_slice(stored.native())).then(|| stored.value().clone());
    }
    // A copied value uses the same whole-byte frame premises as a read
    // retained in place. In particular, an explicit separation of the
    // enclosing header can protect this complete pointer field.
    let _scope = ExplicitReadScope(EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true)));
    let cell = with_extended_dag_bridging(|| {
        memory_dag_cell_source(
            &complete_pointer_read_source(&read),
            &read.defining_address,
            crate::kernel::C_POINTER_BYTE_WIDTH,
            assumptions,
            true,
        )
    })?;
    // At the hop limit, the endpoint can itself be the exact whole-value
    // store. Inspect that one endpoint's record without crossing another
    // edge. Its cache alone is insufficient: a partial store can leave an
    // older overlapping cache entry behind.
    let value = match cell {
        MemoryDagCell::Stored { value, .. } => value,
        MemoryDagCell::Unwritten { node, .. } => {
            let derivation = node.derivation()?;
            let MemoryDerivation::Store { pointer, value, .. } = derivation.as_ref() else {
                return None;
            };
            if pointer != &read.defining_address || value.byte_width() != C_POINTER_BYTE_WIDTH {
                return None;
            }
            value.clone()
        }
    };
    let native = value.native();
    (matches!(
        native,
        ProgramValue::Pointer(_) | ProgramValue::PointerInteger(_)
    ) && !stored_slice(native))
    .then(|| value.into_value())
}

/// Whether a stored value is a slice: a two-word cell that carries no single
/// pointer, so no thin pointer read recovers it (`design/rust-slice-values.md`,
/// step 2b-ii-a). Reads the value in place.
fn stored_slice(value: &ProgramValue) -> bool {
    matches!(value, ProgramValue::Pointer(pointer) if pointer.is_wide())
}

/// Explicit pointer read-value normalization follows at most 64 recorded
/// edges and compares the entire pointer using only the cited conditions.
/// A different block with the same offset is not the stored pointer.
pub(crate) fn pointer_read_has_recorded_value(
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> bool {
    if pointer_reads_share_recorded_cell(left, right, assumptions) {
        return true;
    }
    [(left, right), (right, left)]
        .into_iter()
        .any(|(read, value)| {
            pointer_read_stored_value(read, assumptions, Some(64)).is_some_and(|stored| {
                stored.address() == value
                    || assumptions.pointers_known_equal(stored.address(), value)
            })
        })
}

/// Compare complete typed reads in one producer-retained state using only
/// the selected address equality. This adds neither memory transport nor
/// permission to read the cell.
fn pointer_reads_share_recorded_cell(
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> bool {
    let read = |value: &Address| {
        if let Some(observation) = crate::kernel::eval::latest_pointer_read_observation(value) {
            return Some((observation.0, Box::new(observation.1)));
        }
        let OldMachineTerm::MemoryLoad(memory, address, kind) =
            crate::kernel::equality_graph::logical_pointer_read_term(value)?
        else {
            return None;
        };
        (crate::kernel::load_term_access_width(memory.shared_memory(), &address, kind)
            == crate::kernel::C_POINTER_BYTE_WIDTH)
            .then_some((
                ProgramPoint::from(memory).into_shared_memory(),
                address.into(),
            ))
    };
    let (Some((left_memory, left_address)), Some((right_memory, right_address))) =
        (read(left), read(right))
    else {
        return false;
    };
    left_memory == right_memory
        && crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
            &left_address,
            &right_address,
            assumptions,
        )
}

/// Select one exact complete pointer read's checked endpoint for address-index
/// discovery. The result carries no object provenance or access authority.
/// The caller must keep any numeric union local to its resource query.
pub(in crate::kernel) fn checked_pointer_read_endpoint(
    read: &Address,
    assumptions: &PureFactContext,
) -> Option<Address> {
    checked_pointer_read_endpoint_and_kind(read, assumptions).map(|(endpoint, _)| endpoint)
}

/// [`checked_pointer_read_endpoint`] when the checked walk ends at a stored
/// complete pointer, rather than at an older state's read of the cell.
pub(in crate::kernel) fn checked_pointer_read_stored_value(
    read: &Address,
    assumptions: &PureFactContext,
) -> Option<Address> {
    checked_pointer_read_endpoint_and_kind(read, assumptions)
        .and_then(|(endpoint, stored)| stored.then_some(endpoint))
}

/// The checked endpoint, and whether it is a stored complete pointer.
fn checked_pointer_read_endpoint_and_kind(
    read: &Address,
    assumptions: &PureFactContext,
) -> Option<(Address, bool)> {
    let OldMachineTerm::MemoryLoad(memory, address, kind) =
        crate::kernel::equality_graph::logical_pointer_read_term(read).or_else(|| {
            let application = assumptions.retained_pointer_read_application(read)?;
            let definition = application.as_loaded_value()?;
            Some(crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::viewing(&definition.defining_memory, &definition.point),
                definition.defining_address,
                LoadKind::of_type(ProgramType::Int32Pointer)?,
            ))
        })?
    else {
        return None;
    };
    if crate::kernel::load_term_access_width(memory.shared_memory(), &address, kind)
        != crate::kernel::C_POINTER_BYTE_WIDTH
    {
        return None;
    }
    let source = canonical_load_projection_source(memory.shared_memory(), &address)
        .unwrap_or_else(|| memory.shared_memory().clone());
    // Ask the existing explicit checker to produce typed frame evidence;
    // planner-only separation answers cannot certify a query-local union.
    let _scope = ExplicitReadScope(EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true)));
    with_extended_dag_bridging(|| {
        let cell = memory_dag_cell_source_with_hop_limit(
            &source,
            &address,
            crate::kernel::C_POINTER_BYTE_WIDTH,
            assumptions,
            64,
        )?;
        if !cell.checks_walk_from(
            &source,
            &address,
            crate::kernel::C_POINTER_BYTE_WIDTH,
            assumptions,
        ) {
            return None;
        }
        match &cell {
            MemoryDagCell::Stored { value, .. } => match kind.read_cell(value.native()) {
                Some(ProgramValue::Pointer(stored)) => Some((stored.into_pointer(), true)),
                _ => None,
            },
            // A walk can stop at an unproved or affecting edge. Its cached
            // cell map is not a certificate for a value across that edge.
            MemoryDagCell::Unwritten { .. } => {
                // The read made at `memory`, of the state the walk found
                // its bytes unchanged from.
                Some((
                    Address::loaded_value_read_at(cell.node(), Some(&memory), &address),
                    false,
                ))
            }
        }
    })
}

/// Resolve a selected recorded read from its producer's exact source, not
/// the cell cache its canonical projection happens to retain. Bookkeeping
/// edges write no program bytes; every actual write still uses the existing
/// typed access classifier. The hop bound applies to the selected source path.
fn bounded_recorded_cell_source(
    memory: &SharedMemory,
    address: &Address,
    bytes: u32,
    assumptions: &PureFactContext,
    limit: usize,
) -> Option<MemoryDagCell> {
    bounded_recorded_cell_resolution(memory, address, bytes, assumptions, limit)
        .1
        .map(|(cell, _)| cell)
}

fn bounded_recorded_cell_resolution(
    memory: &SharedMemory,
    address: &Address,
    bytes: u32,
    assumptions: &PureFactContext,
    limit: usize,
) -> (SharedMemory, Option<(MemoryDagCell, CellWalkStop)>) {
    crate::instrumentation::record_deterministic_work(1);
    let source =
        canonical_load_projection_source(memory, address).unwrap_or_else(|| memory.clone());
    let result = with_extended_dag_bridging(|| {
        memory_dag_cell_source_with_hop_limit_and_stop(&source, address, bytes, assumptions, limit)
    });
    (source, result)
}

pub(in crate::kernel) fn pointer_read_stored_value(
    read: &Address,
    assumptions: &PureFactContext,
    max_hops: Option<usize>,
) -> Option<Pointer> {
    let OldMachineTerm::MemoryLoad(memory, address, kind) =
        crate::kernel::equality_graph::logical_pointer_read_term(read)?
    else {
        return None;
    };
    let bytes = crate::kernel::load_term_access_width(memory.shared_memory(), &address, kind);
    if bytes != crate::kernel::C_POINTER_BYTE_WIDTH {
        return None;
    }
    let cell = match max_hops {
        Some(limit) => bounded_recorded_cell_source(
            memory.shared_memory(),
            &address,
            bytes,
            assumptions,
            limit,
        ),
        None => memory_dag_cell_source(memory.shared_memory(), &address, bytes, assumptions, true),
    }?;
    if let Some(value) = cell.resolved_value(&address, kind) {
        return match value {
            ProgramValue::Pointer(stored) => Some(stored),
            _ => None,
        };
    }
    // Only the bounded explicit query asks the full pointer matcher about
    // this one endpoint. The ambient decision walk keeps its cheap rule.
    max_hops?;
    pointer_value_at_stopping_store(&cell, &address, kind, bytes, assumptions)
}

/// Recover only the complete typed value at the selected stopping store.
/// A recorded pointer-load identity can require the full address matcher,
/// beyond the cheap history classifier's graph equality. Never search older
/// stores here, and never infer a pointer from scalar or partial bytes.
fn pointer_value_at_stopping_store(
    cell: &MemoryDagCell,
    address: &Address,
    kind: LoadKind,
    bytes: u32,
    assumptions: &PureFactContext,
) -> Option<Pointer> {
    let step = cell.node().derivation()?;
    let MemoryDerivation::Store {
        pointer: write,
        value,
        ..
    } = step.as_ref()
    else {
        return None;
    };
    let ProgramValue::Pointer(stored) = value.native() else {
        return None;
    };
    (bytes == crate::kernel::C_POINTER_BYTE_WIDTH
        && value.byte_width() == bytes
        && kind.reads_value(value.native())
        && crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
            write,
            address,
            assumptions,
        ))
    .then(|| stored.clone())
}

/// Whether a pointer-valued load resolves through the recorded memory DAG to
/// a stored pointer whose offset is `right`. This is the pointer counterpart
/// of the integer load-equality transport: pointer offsets are represented as
/// `AddressOffset`s, so they cannot use the int32 load-equality API even
/// though the same checked store/call-frame walk supplies their value.
pub(crate) fn pointer_load_offset_proven_equal(
    left: &AddressOffset,
    right: &AddressOffset,
    assumptions: &PureFactContext,
) -> bool {
    let OffsetView::Int32Scaled { index: value, .. } = left.view() else {
        return false;
    };
    let Some(source) = value.operand_view().read_source() else {
        return false;
    };
    let load = match source.as_ref() {
        load @ OldMachineTerm::MemoryLoad(_, _, _) => Some(load.clone()),
        OldMachineTerm::Variable(variable) => {
            crate::kernel::eval::registered_load_origin_term_for_variable(variable)
        }
        _ => None,
    };
    let Some(OldMachineTerm::MemoryLoad(memory, pointer, kind)) = load else {
        return false;
    };
    let bytes = crate::kernel::load_term_access_width(memory.shared_memory(), &pointer, kind);
    let Some(cell) =
        memory_dag_cell_source(memory.shared_memory(), &pointer, bytes, assumptions, true)
    else {
        return false;
    };
    let Some(ProgramValue::Pointer(stored)) = cell.resolved_value(&pointer, kind) else {
        return false;
    };
    crate::kernel::reasoning::pointer_offsets_proven_equal_for_memory_resolution(
        &stored.address().offset,
        right,
        assumptions,
    )
}

/// The write a walk stopped at: the store's pointer and value, for a `Store`
/// edge, and for a `CellsSeeded` edge the one store of the run that writes
/// the cell at `pointer`, asked exactly as the walk asked it.
#[cfg(test)]
fn stored_write_reaching(
    derivation: &MemoryDerivation,
    pointer: &Address,
    bytes: u32,
    assumptions: &PureFactContext,
) -> Option<(Address, ProgramValue)> {
    match derivation {
        MemoryDerivation::Store {
            pointer: written,
            value,
            ..
        } => Some((written.clone(), value.native().clone())),
        MemoryDerivation::CellsSeeded { .. } => {
            match crate::kernel::resource_tracker::step_effect::seeded_cell_effect(
                derivation,
                pointer,
                bytes,
                &crate::kernel::resource_tracker::step_effect::Evidence {
                    assumptions,
                    cross_loop_havoc: true,
                },
            ) {
                crate::kernel::resource_tracker::step_effect::SeededCellEffect::Written(
                    written,
                    value,
                ) => Some((written, value)),
                _ => None,
            }
        }
        _ => None,
    }
}

pub(super) fn heap_allocation_proven_separate_from_pointer(
    allocation_base: &Address,
    bytes: &AllocationSize,
    pointer: &Address,
    assumptions: &PureFactContext,
) -> bool {
    // Only the allocation's *memory* can be separate from a cell by address.
    // The allocation token is a separate resource from every memory range,
    // including the one it covers: a composite holding `allocation(p, n)`
    // and `owns p[0..k]` states the two members separate, and reading that as
    // "the freed bytes miss `p[0]`" framed a load of freed memory across its
    // own `free`.
    let cell = Resource::Memory(MemoryRange::new(
        pointer.clone(),
        OldMachineTerm::constant(0),
        OldMachineTerm::constant(1),
    ));
    // The allocation's memory in its own index kind, read through the
    // size's element count as the heap reads its blocks.
    bytes.element_count(4).is_some_and(|count| {
        let allocation_memory = Resource::Memory(bytes.range(allocation_base.clone(), count, 4));
        assumptions.proves_resource_separate(&allocation_memory, &cell)
    })
}

/// Produces checked evidence that two loads are equal from the memory DAG: both sides are
/// resolved to their source cell by [`memory_dag_cell_source`], and the loads
/// are equal when the two lookups land on the same node or pin down the same
/// value.
///
/// This is stage 4 of `docs/internals/memory-dag.md`, and it is
/// wired in *ahead* of the canonicalizing comparisons rather than beside
/// them. Where those take two embedded states, deep-canonicalize both and
/// compare the results structurally, this follows named edges and compares
/// arena ids, so the common case — two forms of one cell separated only
/// by stores that provably missed it — costs a short walk instead of a deep
/// term rewrite.
///
/// A missing result means "the DAG did not answer". Derivations are not
/// guaranteed to connect every pair of states, so callers may try another
/// exact evidence source.
pub(super) fn memory_load_equality_evidence_at(
    left_memory: &SharedMemory,
    right_memory: &SharedMemory,
    pointer: &Address,
    kind: LoadKind,
    assumptions: &PureFactContext,
) -> Option<MemoryDagLoadEqualityEvidence> {
    if let Some(common) = one_state_equality_evidence(left_memory, right_memory) {
        return Some(common);
    }
    let walks = LoadCellWalks::run(left_memory, right_memory, pointer, kind, assumptions)?;
    let reason = walks.equality_reason(pointer).or_else(|| {
        if !extended_dag_bridging_active() {
            return None;
        }
        if retained_cell_names_load(&walks.left, right_memory, pointer, kind) {
            Some(MemoryDagLoadEqualityReason::LeftRetainsRightRead)
        } else if retained_cell_names_load(&walks.right, left_memory, pointer, kind) {
            Some(MemoryDagLoadEqualityReason::RightRetainsLeftRead)
        } else {
            None
        }
    })?;
    Some(MemoryDagLoadEqualityEvidence {
        left: walks.left,
        right: walks.right,
        reason,
    })
}

/// A retained scalar observation names exactly the other typed read. The
/// load registry canonicalizes that one named endpoint; facts and aliases do
/// not choose its value. Pointer representations are deliberately excluded.
fn retained_cell_names_load(
    cell: &MemoryDagCell,
    memory: &SharedMemory,
    pointer: &Address,
    kind: LoadKind,
) -> bool {
    let Some(crate::kernel::integer32_c_value!(value)) = cell
        .node()
        .cells
        .concrete()
        .get(pointer)
        .and_then(|value| kind.read_cell(value.native()))
    else {
        return false;
    };
    value == crate::kernel::canonical_form_of_load(memory.clone(), pointer.clone(), kind)
}

/// The equality two identical states have without walking anything.
fn one_state_equality_evidence(
    left_memory: &SharedMemory,
    right_memory: &SharedMemory,
) -> Option<MemoryDagLoadEqualityEvidence> {
    (left_memory == right_memory).then(|| {
        let cell = MemoryDagCell::Unwritten {
            node: left_memory.clone(),
            path: Vec::new(),
        };
        MemoryDagLoadEqualityEvidence {
            left: cell.clone(),
            right: cell,
            reason: MemoryDagLoadEqualityReason::CommonSource,
        }
    })
}

/// The one pair of cell-source walks every question about two loads of one
/// cell is answered from.
///
/// Both halves of the answer come off the same traversal. The nodes the walks
/// reached say whether the two states hold *one* version of the cell; the
/// reasons they stopped say whether they hold two *different* versions. A
/// caller that wanted only the first used to walk twice over — once here and
/// once for the stored-value arm beside it — and the history's refutation was
/// thrown away with the stop reason.
struct LoadCellWalks {
    left: MemoryDagCell,
    right: MemoryDagCell,
    left_stop: CellWalkStop,
    right_stop: CellWalkStop,
    /// The kind of the read both loads are, which is the only kind a walk's
    /// resolved value may answer for.
    kind: LoadKind,
}

impl LoadCellWalks {
    fn run(
        left_memory: &SharedMemory,
        right_memory: &SharedMemory,
        pointer: &Address,
        kind: LoadKind,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        let left_bytes = crate::kernel::load_term_access_width(left_memory, pointer, kind);
        let right_bytes = crate::kernel::load_term_access_width(right_memory, pointer, kind);
        // A shared state already fixes one version of the cell. Reuse the
        // typed two-sided frame walk so a cold query never follows history
        // older than both endpoints. Writes and unresolved steps retain the
        // existing source/value and refutation routes below.
        if left_bytes == right_bytes
            && let Some((left, right)) = join_read_agreement(
                left_memory,
                right_memory,
                pointer,
                left_bytes,
                &crate::kernel::resource_tracker::step_effect::Evidence {
                    assumptions,
                    cross_loop_havoc: true,
                },
            )
        {
            for (memory, cell) in [(left_memory, &left), (right_memory, &right)] {
                record_transport_cell_walk(
                    memory,
                    pointer,
                    left_bytes,
                    cell,
                    CellWalkStop::CommonState,
                    None,
                );
            }
            return Some(Self {
                left,
                right,
                left_stop: CellWalkStop::CommonState,
                right_stop: CellWalkStop::CommonState,
                kind,
            });
        }

        let (left, left_stop) =
            memory_dag_cell_source_with_stop(left_memory, pointer, left_bytes, assumptions, true)?;
        let (right, right_stop) = memory_dag_cell_source_with_stop(
            right_memory,
            pointer,
            right_bytes,
            assumptions,
            true,
        )?;
        Some(Self {
            left,
            right,
            left_stop,
            right_stop,
            kind,
        })
    }

    /// Why the two walks make the loads equal, when they do: they stopped at
    /// one node, or they pinned down one value.
    fn equality_reason(&self, pointer: &Address) -> Option<MemoryDagLoadEqualityReason> {
        if self.left.node() == self.right.node() {
            return Some(MemoryDagLoadEqualityReason::CommonSource);
        }
        match (
            self.left.resolved_value(pointer, self.kind),
            self.right.resolved_value(pointer, self.kind),
        ) {
            (Some(left_value), Some(right_value)) if left_value == right_value => {
                Some(MemoryDagLoadEqualityReason::EqualResolvedValue(left_value))
            }
            _ => None,
        }
    }

    /// The equality the two walks establish between the loads themselves,
    /// with both retained walks as its evidence.
    fn equality(self, pointer: &Address) -> Option<MemoryDagLoadEqualityEvidence> {
        let reason = self.equality_reason(pointer)?;
        Some(MemoryDagLoadEqualityEvidence {
            left: self.left,
            right: self.right,
            reason,
        })
    }

    /// Whether a recorded step that provably acts on this access's bytes
    /// stands between the two states.
    ///
    /// A walk stops on such a step having proved something, not having given
    /// up: the cell one step older is a different *version* of this cell. Two
    /// loads separated by one of those are not one value by any structural
    /// route, whatever the states' cell maps happen to have kept. The
    /// exhaustion and unclassified stops prove nothing and leave every other
    /// route to speak. A common-state stop instead establishes equality.
    fn cross_an_affecting_step(&self) -> bool {
        self.left_stop == CellWalkStop::Affected || self.right_stop == CellWalkStop::Affected
    }

    /// [`Self::equality`], and then, where stored-value pinning is in scope,
    /// the arm that reads one side's walk as pinning the *other side's whole
    /// load term*.
    ///
    /// One side's walk may land on a `Store` whose recorded value IS the
    /// other side verbatim — the common case for a load-caching store
    /// (`cells[p] := load(older, p)`): the newer state's cell literally
    /// pins the older form. That is still a pure history answer (the value
    /// comes off a derivation edge, compared structurally), so it stays
    /// inside the exact-facts-plus-edges determinism boundary.
    fn equality_or_resolved_endpoint(
        self,
        left_memory: &SharedMemory,
        right_memory: &SharedMemory,
        pointer: &Address,
        pinning: bool,
    ) -> Option<AtomicMemoryLoadEqualityEvidence> {
        if self.equality_reason(pointer).is_some() || !pinning {
            return self
                .equality(pointer)
                .map(AtomicMemoryLoadEqualityEvidence::SameCell);
        }
        let reason = if retained_cell_names_load(&self.left, right_memory, pointer, self.kind) {
            Some(MemoryDagLoadEqualityReason::LeftRetainsRightRead)
        } else if retained_cell_names_load(&self.right, left_memory, pointer, self.kind) {
            Some(MemoryDagLoadEqualityReason::RightRetainsLeftRead)
        } else {
            None
        };
        if let Some(reason) = reason {
            return Some(AtomicMemoryLoadEqualityEvidence::SameCell(
                MemoryDagLoadEqualityEvidence {
                    left: self.left,
                    right: self.right,
                    reason,
                },
            ));
        }
        let kind = self.kind;
        let pins = |cell: &MemoryDagCell, other: &SharedMemory| {
            matches!(cell, MemoryDagCell::Stored { .. })
                && matches!(
                    cell.resolved_value(pointer, kind),
                    Some(
                        crate::kernel::integer32_c_value!(value)
                    ) if value.is_memory_named_read_of(other, pointer, kind)
                )
        };
        if pins(&self.left, right_memory) {
            Some(AtomicMemoryLoadEqualityEvidence::LeftResolvesToRight { left: self.left })
        } else if pins(&self.right, left_memory) {
            Some(AtomicMemoryLoadEqualityEvidence::RightResolvesToLeft { right: self.right })
        } else {
            None
        }
    }
}

/// Compare exact sources or one checked predecessor per named endpoint.
/// Longer preservation chains require explicit equalities; this operation
/// must not discover intermediate states by following memory history.
fn typed_reads_share_memory_source(
    left: &SharedMemory,
    right: &SharedMemory,
    pointer: &Address,
    bytes: u32,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    let _scope = ExplicitReadScope(EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true)));
    with_extended_dag_bridging(|| {
        let evidence = crate::kernel::resource_tracker::step_effect::Evidence {
            assumptions,
            cross_loop_havoc: true,
        };
        let predecessor = |node: &SharedMemory| {
            crate::instrumentation::record_deterministic_work(1);
            let step = node.derivation()?;
            matches!(
                crate::kernel::resource_tracker::step_effect::affects(
                    &step,
                    node,
                    crate::kernel::resource_tracker::TrackedResource::Cell {
                        pointer,
                        bytes: bytes.into()
                    },
                    &evidence,
                ),
                crate::kernel::resource_tracker::step_effect::StepEffect::Separate(
                    crate::kernel::resource_tracker::step_effect::Separation::Cell(_)
                )
            )
            .then(|| {
                // Observations preserve bytes and retain their source directly.
                // The read producer may name that earlier source, rather than
                // the checked transition's immediate observation-only base.
                step.base().unchanged_bytes_source()
            })
        };
        let left_base = predecessor(left);
        if left_base.as_ref() == Some(right) {
            return true;
        }
        let right_base = predecessor(right);
        right_base.as_ref() == Some(left) || left_base.is_some() && left_base == right_base
    })
}

/// Initialization can cross only checked no-write edges for this typed range.
/// Reaching equal stored values at different sources is insufficient: value
/// equality grants no authority to read an initialized object.
pub(super) fn typed_read_has_same_memory_source(
    before: &SymbolicMemory,
    after: &SymbolicMemory,
    pointer: &Address,
    bytes: u32,
    assumptions: &PureFactContext,
) -> bool {
    // Complete pointer identity needs the explicit, whole-byte separation
    // premises too, rather than only the planner's address-distinctness rungs.
    let _scope = ExplicitReadScope(EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true)));
    with_extended_dag_bridging(|| {
        let before = intern_memory_ref(before);
        let current = intern_memory_ref(after);
        crate::instrumentation::record_deterministic_work(1);
        if current == before {
            return true;
        }
        let Some(step) = current.derivation() else {
            return false;
        };
        // Only the named adjacent transition is implicit. Longer arguments
        // must provide explicit intermediate read-validity facts.
        if step.base() != &before {
            return false;
        }
        let evidence = crate::kernel::resource_tracker::step_effect::Evidence {
            assumptions,
            cross_loop_havoc: true,
        };
        matches!(
            crate::kernel::resource_tracker::step_effect::affects(
                &step,
                &current,
                crate::kernel::resource_tracker::TrackedResource::Cell {
                    pointer,
                    bytes: bytes.into()
                },
                &evidence,
            ),
            crate::kernel::resource_tracker::step_effect::StepEffect::Separate(
                crate::kernel::resource_tracker::step_effect::Separation::Cell(_)
            )
        )
    })
}

/// The memory-DAG equality arm as a term-level test:
/// true only when both sides are atomic loads the DAG resolves alike.
///
/// Beyond the node-identity comparison, one side's walk may land on a
/// `Store` whose recorded value IS the other side verbatim — the common case
/// for a load-caching store (`cells[p] := load(older, p)`): the newer
/// state's cell literally pins the older form. That is still a pure
/// DAG answer (the value comes off a derivation edge, compared structurally),
/// so it stays inside the exact-facts-plus-edges determinism boundary.
pub(crate) fn atomic_loads_equal_along_memory_derivations(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    atomic_memory_load_equality_evidence(left, right, assumptions).is_some()
}

/// Evidence-producing form of
/// [`atomic_loads_equal_along_memory_derivations`]. Positive memo entries
/// retain this evidence instead of caching only the boolean answer.
pub(super) fn atomic_memory_load_equality_evidence(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> Option<AtomicMemoryLoadEqualityEvidence> {
    let (
        OldMachineTerm::MemoryLoad(left_memory, left_pointer, left_kind),
        OldMachineTerm::MemoryLoad(right_memory, right_pointer, right_kind),
    ) = (left, right)
    else {
        return None;
    };
    if left_pointer.address() != right_pointer.address() || left_kind != right_kind {
        return None;
    }
    match recorded_load_history(
        left_memory.shared_memory(),
        right_memory.shared_memory(),
        left_pointer,
        *left_kind,
        assumptions,
    ) {
        LoadHistory::OneVersion(evidence) => Some(evidence),
        LoadHistory::DifferentVersions | LoadHistory::Undecided => None,
    }
}

/// What the recorded history says about two loads of one cell at one address.
///
/// The three answers are the three a history can give, and the middle one is
/// the one a state comparison cannot reconstruct. A cell map records what
/// is *known* at a state, not what *happened* to it: a store drops the
/// cell it partly overwrites, and the naming projection discards what it
/// leaves behind, so two states a store separates can be cell-identical.
/// Absence of a differing cell is therefore never evidence that no store
/// happened. The history has the store either way.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum LoadHistory {
    /// The two states hold one version of the cell, with this evidence.
    OneVersion(AtomicMemoryLoadEqualityEvidence),
    /// A recorded step that provably acts on this access's bytes stands
    /// between the two states, so they hold two different versions of it.
    /// No structural route may call the two loads equal; a stated or assumed
    /// equality fact still can, and is consulted before this ever is.
    DifferentVersions,
    /// The bounded history query decides neither. Explicit facts can still
    /// establish equality; matching state representations cannot.
    Undecided,
}

/// The one memoized question every consumer of the load history asks.
///
/// Both halves of the answer come from one pair of cell-source walks, so
/// asking for the refutation after asking for the equality costs a memo
/// lookup rather than a second traversal.
pub(in crate::kernel) fn recorded_load_history(
    left_memory: &SharedMemory,
    right_memory: &SharedMemory,
    pointer: &Address,
    kind: LoadKind,
    assumptions: &PureFactContext,
) -> LoadHistory {
    // The same (state, state, pointer) triple is asked thousands of
    // times per proof. A proven equality stays true as new first-wins DAG
    // edges are recorded: the edges only add faithful derivations of already
    // existing states. Cache those positive answers independently of the
    // derivation generation. The other two answers only mean "not connected
    // yet" and "not separated yet": a new edge can extend a walk that had run
    // out of history, so both remain generation-scoped and are retried after
    // any new edge. Only top-level answers participate: a nested lookup may
    // meet an in-progress cell and its weaker answer must not shadow the full
    // one.
    let memo_key = memory_dag_cell_lookup_depth_is_zero()
        .then(|| super::assumptions::dag_memo_assumptions_id(assumptions))
        .map(|assumptions_id| DagLoadEqualityMemoKey {
            assumptions_id,
            bridging: extended_dag_bridging_active(),
            explicit: explicit_dag_check_active(),
            left_memory: left_memory.arena_id(),
            right_memory: right_memory.arena_id(),
            pointer: pointer.clone(),
            kind,
        });
    if let Some(key) = &memo_key
        && let Some(evidence) =
            DAG_LOAD_EQUALITY_POSITIVE_MEMO.with(|memo| memo.borrow().get(key).cloned())
    {
        return LoadHistory::OneVersion(evidence);
    }
    let derivation_generation = memory_derivation_generation();
    // A completed refusal concerns the unordered pair of states. Keep
    // positive witnesses oriented, but share the negative history question
    // when another route asks it in the opposite direction.
    let unproven_key = memo_key.as_ref().map(|key| {
        let mut key = key.clone();
        if key.left_memory > key.right_memory {
            std::mem::swap(&mut key.left_memory, &mut key.right_memory);
        }
        (derivation_generation, key)
    });
    if let Some(key) = &unproven_key
        && let Some(answer) =
            DAG_LOAD_EQUALITY_UNPROVEN_MEMO.with(|memo| memo.borrow().get(key).copied())
    {
        return if answer {
            LoadHistory::DifferentVersions
        } else {
            LoadHistory::Undecided
        };
    }
    let incomplete_before = super::assumptions::incomplete_reasoning_epoch();
    let result =
        recorded_load_history_uncached(left_memory, right_memory, pointer, kind, assumptions);
    if let Some(key) = memo_key {
        match &result {
            LoadHistory::OneVersion(evidence) => {
                DAG_LOAD_EQUALITY_POSITIVE_MEMO.with(|memo| {
                    let mut memo = memo.borrow_mut();
                    if memo.len() >= DAG_LOAD_EQUALITY_MEMO_LIMIT {
                        memo.clear();
                    }
                    memo.insert(key, evidence.clone());
                });
            }
            LoadHistory::DifferentVersions | LoadHistory::Undecided
                if super::assumptions::incomplete_reasoning_epoch() == incomplete_before
                    && !super::assumptions::reasoning_interrupted() =>
            {
                let separated = matches!(result, LoadHistory::DifferentVersions);
                DAG_LOAD_EQUALITY_UNPROVEN_MEMO.with(|memo| {
                    let mut memo = memo.borrow_mut();
                    if memo.len() >= DAG_LOAD_EQUALITY_MEMO_LIMIT {
                        memo.clear();
                    }
                    if let Some(key) = unproven_key {
                        memo.insert(key, separated);
                    }
                });
            }
            LoadHistory::DifferentVersions | LoadHistory::Undecided => {}
        }
    }
    result
}

fn recorded_load_history_uncached(
    left_memory: &SharedMemory,
    right_memory: &SharedMemory,
    pointer: &Address,
    kind: LoadKind,
    assumptions: &PureFactContext,
) -> LoadHistory {
    if let Some(common) = one_state_equality_evidence(left_memory, right_memory) {
        return LoadHistory::OneVersion(AtomicMemoryLoadEqualityEvidence::SameCell(common));
    }
    let Some(walks) = LoadCellWalks::run(left_memory, right_memory, pointer, kind, assumptions)
    else {
        return LoadHistory::Undecided;
    };
    let separated = walks.cross_an_affecting_step();
    // Outside the loadable prover the equality half keeps its pre-arc
    // behavior — node-identity comparison only, no value pinning — because
    // certified forms and case-split structure check against it. The
    // refutation half is uniform: it withholds equalities rather than adding
    // any, and a veto that fired in one scope and not another would leave the
    // routes disagreeing about the same store.
    let pinning = extended_dag_bridging_active();
    let evidence = walks
        .equality_or_resolved_endpoint(left_memory, right_memory, pointer, pinning)
        .map(LoadHistory::OneVersion);
    evidence.unwrap_or(if separated {
        LoadHistory::DifferentVersions
    } else {
        LoadHistory::Undecided
    })
}

/// Resolves an equality from the execution-recorded memory DAG for explicit
/// certificate validation. Unlike the planner-facing DAG arm, this may cross
/// no-op block declarations and stores whose distinctness follows from the
/// certificate's separation facts; every crossed edge remains justified by
/// exact facts and the bounded DAG walk.
/// The form this context decides for one load: the integer a store or
/// state cell provides, or else the load of the oldest state the walk
/// proves the cell unchanged from, named by the assumption-free naming walk
/// so that facts spelled with that older name apply exactly.
pub(crate) fn resolve_load_along_memory_derivations(
    origin: &ProgramPoint,
    pointer: &Address,
    kind: LoadKind,
    assumptions: &PureFactContext,
) -> Option<OldMachineTerm> {
    let memory = origin.shared_memory();
    let _assumptions_id_scope = assumptions.enter_id_scope();
    let previous = EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true));
    let result = with_extended_dag_bridging(|| {
        let bytes = crate::kernel::load_term_access_width(memory, pointer, kind);
        let cell = memory_dag_cell_source(memory, pointer, bytes, assumptions, true)?;
        if let Some(value) = cell.resolved_value(pointer, kind) {
            return match value {
                crate::kernel::integer32_c_value!(value) => Some(value),
                _ => None,
            };
        }
        match cell {
            MemoryDagCell::Stored { .. } => None,
            // The node is an earlier memory the history walk reached
            // from the origin; it is placed only as walked from there.
            MemoryDagCell::Unwritten { node, .. } => {
                Some(crate::kernel::canonical_form_of_load_at(
                    &ProgramPoint::walked(&node, origin),
                    pointer.clone(),
                    kind,
                ))
            }
        }
    });
    EXPLICIT_DAG_CHECK.with(|flag| flag.set(previous));
    result
}

/// Rewrites `proposition` with each registered load variable replaced by the
/// form [`resolve_load_along_memory_derivations`] decides for it from its
/// origin state under `assumptions`. Returns `None` when nothing changes.
/// Work is one bounded DAG query per load variable of the proposition;
/// nothing else is visited.
pub(crate) fn resolve_prerequisite_loads_along_memory_derivations(
    proposition: &Proposition,
    assumptions: &PureFactContext,
) -> Option<Proposition> {
    let mut resolved = proposition.clone();
    let mut changed = false;
    for variable in crate::kernel::proposition_variables(proposition) {
        if !crate::kernel::is_load_variable(&variable) {
            continue;
        }
        let Some(OldMachineTerm::MemoryLoad(origin, pointer, kind)) =
            crate::kernel::registered_load_origin_term_for_variable(&variable)
        else {
            continue;
        };
        let Some(form) =
            resolve_load_along_memory_derivations(&origin, &pointer, kind, assumptions)
        else {
            continue;
        };
        if form == OldMachineTerm::Variable(variable) {
            continue;
        }
        resolved = crate::kernel::reasoning::substitute_bitvector_variable_in_proposition(
            &resolved, variable, &form,
        );
        changed = true;
    }
    changed.then_some(resolved)
}

pub(crate) fn explicit_atomic_equality_from_memory_derivations(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    explicit_atomic_equality_from_memory_derivations_views(
        crate::kernel::MachineOperandView::Old(left),
        crate::kernel::MachineOperandView::Old(right),
        assumptions,
    )
}

pub(in crate::kernel) fn explicit_atomic_equality_from_memory_derivations_views(
    left: crate::kernel::MachineOperandView<'_>,
    right: crate::kernel::MachineOperandView<'_>,
    assumptions: &PureFactContext,
) -> bool {
    let _assumptions_id_scope = assumptions.enter_id_scope();
    let previous = EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true));
    let result = with_extended_dag_bridging(|| {
        if left
            .read_source()
            .zip(right.read_source())
            .is_some_and(|(left, right)| {
                atomic_loads_equal_along_memory_derivations(&left, &right, assumptions)
            })
        {
            return true;
        }
        let resolves_to = |load: crate::kernel::MachineOperandView<'_>,
                           value: crate::kernel::MachineOperandView<'_>| {
            let Some((memory, pointer, kind)) = load.read() else {
                return false;
            };
            let bytes = crate::kernel::load_term_access_width(memory, pointer, kind);
            matches!(
                memory_dag_cell_source(memory, pointer, bytes, assumptions, true)
                    .and_then(|cell| cell.resolved_value(pointer, kind)),
                Some(crate::kernel::integer32_c_value!(resolved))
                    if crate::kernel::MachineOperandView::Old(&resolved).retain(MachineIntegerType::Int32) == value.retain(MachineIntegerType::Int32)
            )
        };
        resolves_to(left, right) || resolves_to(right, left)
    });
    EXPLICIT_DAG_CHECK.with(|flag| flag.set(previous));
    result
}

#[derive(Clone, Eq, Hash, PartialEq)]
struct DagLoadEqualityMemoKey {
    assumptions_id: u64,
    /// The two scopes that decide which recorded edges a walk may cross, and
    /// so which answers it can reach. They are part of the question, not
    /// ambient state the answer is independent of: explicit certificate
    /// validation crosses store hops justified by the certificate's own
    /// separation ranges, and the pre-arc scope crosses no bookkeeping edge
    /// at all. Before the history's refutation was read off these walks, the
    /// pre-arc scope simply bypassed the memo and the explicit scope shared
    /// the ordinary one, which let a weaker answer stand in for a stronger.
    bridging: bool,
    explicit: bool,
    left_memory: (u32, u32),
    right_memory: (u32, u32),
    pointer: Address,
    kind: LoadKind,
}

thread_local! {
    static DAG_LOAD_EQUALITY_POSITIVE_MEMO: std::cell::RefCell<
        std::collections::HashMap<DagLoadEqualityMemoKey, AtomicMemoryLoadEqualityEvidence>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    /// The two answers that are not an equality, keyed by derivation
    /// generation: `true` is a store between the states, `false` is a
    /// history that decides nothing.
    static DAG_LOAD_EQUALITY_UNPROVEN_MEMO: std::cell::RefCell<
        std::collections::HashMap<(u64, DagLoadEqualityMemoKey), bool>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

const DAG_LOAD_EQUALITY_MEMO_LIMIT: usize = 200_000;

/// The writes the memory history records on every path from one point to a
/// later one: what a region did to memory, read from its steps.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct RecordedWrites {
    /// Each store's destination and extent.
    pub(crate) accesses: BTreeSet<(Address, AccessExtent)>,
    /// Each call's or loop's write ranges, with the memory it started from.
    pub(crate) ranges: Vec<(MemoryRange, SharedMemory)>,
    /// The blocks the region declared or allocated: storage it created.
    pub(crate) created: BTreeSet<AddressBase>,
    /// Whether a loop between the points records no checked footprint: its
    /// iterations' writes are not on this history.
    pub(crate) unbounded_loop: bool,
}

impl RecordedWrites {
    /// The writes between `before` and `after`, visiting each step once.
    /// `None` when some path into `after` does not start at `before`.
    pub(crate) fn between(
        before: &crate::kernel::program_point::PathLink,
        after: &crate::kernel::program_point::PathLink,
    ) -> Option<Self> {
        let mut writes = Self::default();
        // A loop head with no checked footprint is answered by its exit's
        // record of the iterations, when one is on the path.
        let mut unbounded_heads = BTreeSet::new();
        let mut recorded_heads = BTreeSet::new();
        let mut iteration_writes = Vec::new();
        after.visit_region_steps_since(
            before,
            |point, step| {
                if let Some((pointer, extent)) = step.single_write_extent() {
                    writes.accesses.insert((pointer.clone(), extent));
                }
                match step {
                    // A seeded run writes its slots: one range for the run,
                    // whatever its length. Caching bytes the base already
                    // holds writes nothing.
                    MemoryDerivation::CellsSeeded { base, run }
                        if !crate::kernel::resource_tracker::step_effect::seeded_loads_preserve_base(
                            step,
                        ) =>
                    {
                        writes.ranges.push((
                            MemoryRange::new_with_element_width(
                                run.base().clone(),
                                0u32.into(),
                                run.count().into(),
                                run.element_width(),
                            ),
                            base.clone(),
                        ));
                    }
                    MemoryDerivation::CallHavoc {
                        base,
                        mutable_ranges,
                        ..
                    } => writes.ranges.extend(
                        mutable_ranges
                            .iter()
                            .map(|range| (range.clone(), base.clone())),
                    ),
                    MemoryDerivation::LoopHavoc {
                        base,
                        mutable_ranges,
                        ..
                    } => match mutable_ranges {
                        Some(ranges) => writes
                            .ranges
                            .extend(ranges.iter().map(|range| (range.clone(), base.clone()))),
                        None => {
                            unbounded_heads.insert(point);
                        }
                    },
                    MemoryDerivation::BlockDeclared { block, .. }
                    | MemoryDerivation::HeapAllocated { block, .. } => {
                        writes.created.insert(block.clone());
                    }
                    _ => {}
                }
            },
            |iterations| {
                iteration_writes.push((iterations.head, iterations.writes().cloned()));
            },
        )?;
        // An exit records the iterations of every head its loop rule checked;
        // only the heads this region passed through wrote on it.
        for (head, recorded) in iteration_writes {
            if !unbounded_heads.contains(&head) {
                continue;
            }
            recorded_heads.insert(head);
            match recorded {
                Some(recorded) => writes.merge(&recorded),
                None => writes.unbounded_loop = true,
            }
        }
        writes.unbounded_loop |= !unbounded_heads.is_subset(&recorded_heads);
        Some(writes)
    }

    /// Add `other`'s writes to these.
    pub(crate) fn merge(&mut self, other: &Self) {
        self.accesses.extend(other.accesses.iter().cloned());
        self.ranges.extend(other.ranges.iter().cloned());
        self.created.extend(other.created.iter().cloned());
        self.unbounded_loop |= other.unbounded_loop;
    }
}

/// The memory history's liveness query: whether storage in `block` that is
/// live at one of `left` and `right` is live at the other. One point must be
/// reached from the other through single predecessors, and no step between
/// them may end a lifetime that could be `block`'s: a free, a local
/// lifetime's end, a contract allocation's retirement, or an effect that
/// does not say which claims it changes. `None` when neither point is
/// reached from the other.
pub(crate) fn liveness_preserved_between_points(
    left: &crate::kernel::program_point::PathLink,
    right: &crate::kernel::program_point::PathLink,
    block: &AddressBase,
) -> Option<bool> {
    let distinct = |other: &AddressBase| other != block && !block.observable_by_load(other);
    let preserves = |step: &MemoryDerivation| match step {
        MemoryDerivation::HeapFreed {
            allocation_base, ..
        }
        | MemoryDerivation::ContractAllocationRetired {
            allocation_base, ..
        } => distinct(&allocation_base.base),
        MemoryDerivation::LocalLifetimeEnded { block: ended, .. } => distinct(ended),
        MemoryDerivation::HeapAllocationFailed { .. }
        | MemoryDerivation::ContractAllocationClaimsChanged { .. }
        | MemoryDerivation::BranchJoin { .. }
        | MemoryDerivation::LoopHavoc {
            mutable_ranges: None,
            ..
        } => false,
        _ => true,
    };
    right
        .visit_steps_since(left, preserves)
        .or_else(|| left.visit_steps_since(right, preserves))
}

/// Address inequality frames a load only when the two typed accesses fit
/// inside the gap it proves. Keep explicit range separation available even
/// when an address-only comparison cannot establish that gap.
pub(crate) fn write_access_is_disjoint_from_load(
    write: &Address,
    write_bytes: impl Into<crate::kernel::AccessExtent>,
    read: &Address,
    read_bytes: impl Into<crate::kernel::AccessExtent>,
    assumptions: &PureFactContext,
) -> bool {
    let (write_extent, read_extent) = (write_bytes.into(), read_bytes.into());
    let empty = crate::kernel::AccessExtent::Bytes(0);
    if write_extent == empty || read_extent == empty {
        return false;
    }
    if write.blocks_proven_distinct(read) {
        return true;
    }
    use crate::kernel::reasoning::{AccessByteOverlap, access_byte_overlap};
    let overlap = access_byte_overlap(write, write_extent, read, read_extent, assumptions);
    if overlap == AccessByteOverlap::Overlaps {
        return false;
    }
    // An object of abstract size is placed by the layout rule or a stated
    // separation of its range, which the overlap answer above already read.
    let (Some(write_bytes), Some(read_bytes)) = (write_extent.bytes(), read_extent.bytes()) else {
        return overlap == AccessByteOverlap::Separate
            || assumptions
                .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                    &MemoryRange::of_access(write, write_extent),
                    &MemoryRange::of_access(read, read_extent),
                );
    };
    (overlap == AccessByteOverlap::Separate
        && pointers_proven_distinct_for_memory_resolution(write, read, assumptions))
        || assumptions.ranges_directly_disjoint_from_access(
            &[MemoryRange::new_with_element_width(
                write.clone(),
                OldMachineTerm::constant(0),
                OldMachineTerm::constant(1),
                write_bytes,
            )],
            read,
            read_bytes,
        )
}

#[cfg(test)]
thread_local! {
    /// The loadable facts the carried-loadability route of
    /// `proves_atomic_without_search` examined.
    pub(crate) static CARRIED_LOADABLE_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
thread_local! {
    /// The effect facts `memory_load_is_directly_unchanged` examined.
    static DIRECT_UNCHANGED_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

fn memory_load_is_directly_unchanged(
    before: &SymbolicMemory,
    after: &SymbolicMemory,
    pointer: &Address,
    kind: LoadKind,
    assumptions: &PureFactContext,
) -> bool {
    if crate::kernel::assumptions::reasoning_interrupted() {
        return false;
    }
    if memories_directly_match_for_pointer_load(before, after, pointer, assumptions) {
        return true;
    }
    // An effect that starts at `before` itself: those filed under it, not
    // every proposition fact. Its other end may still be any state that
    // directly matches `after` for this load.
    assumptions
        .memory_effect_facts_naming(before)
        .any(|proposition| {
            if crate::kernel::assumptions::reasoning_interrupted() {
                return false;
            }
            #[cfg(test)]
            DIRECT_UNCHANGED_VISITS.with(|visits| visits.set(visits.get() + 1));
            let proved = match proposition {
                Proposition::MemoryMutatesOnly {
                    before: effect_before,
                    after: effect_after,
                    writes,
                    ..
                } => {
                    effect_before == before
                        && (effect_after == after
                            || directly_matched_effect_endpoint(
                                effect_after,
                                after,
                                pointer,
                                assumptions,
                            ))
                        && writes.iter().all(|(write, bytes)| {
                            write_access_is_disjoint_from_load(
                                write,
                                *bytes,
                                pointer,
                                crate::kernel::eval::load_access_extent(pointer, kind),
                                assumptions,
                            )
                        })
                }
                Proposition::MemoryEffectSummary {
                    before: effect_before,
                    after: effect_after,
                    mutable_ranges,
                    ..
                } => {
                    // The direct check decides most disjointness
                    // structurally; the remaining route reads indexed
                    // separation facts and exposed composition members.
                    effect_before == before
                        && memories_directly_match_for_pointer_load(
                            effect_after,
                            after,
                            pointer,
                            assumptions,
                        )
                        && (assumptions
                            .ranges_directly_disjoint_from_pointer(mutable_ranges, pointer)
                            || assumptions
                                .ranges_proven_disjoint_from_pointer(mutable_ranges, pointer))
                }
                Proposition::HeapAllocationFreed {
                    before: effect_before,
                    after: effect_after,
                    blocks,
                    mutable_ranges,
                    ..
                } => {
                    effect_before == before
                        && memories_directly_match_for_pointer_load(
                            effect_after,
                            after,
                            pointer,
                            assumptions,
                        )
                        && blocks.iter().all(|(base, bytes)| {
                            heap_allocation_proven_separate_from_pointer(
                                base,
                                bytes,
                                pointer,
                                assumptions,
                            )
                        })
                        && (mutable_ranges.is_empty()
                            || assumptions
                                .ranges_directly_disjoint_from_pointer(mutable_ranges, pointer)
                            || assumptions
                                .ranges_proven_disjoint_from_pointer(mutable_ranges, pointer))
                }
                _ => false,
            };
            if proved {
                crate::kernel::record_implicit_consulted_premises(assumptions, proposition);
            }
            proved
        })
}

pub(in crate::kernel) fn memories_directly_match_for_pointer_load(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    pointer: &Address,
    assumptions: &PureFactContext,
) -> bool {
    if memories_match_for_pointer_load(left, right, pointer) {
        return true;
    }
    // Two states that name the cell by one version hold the same
    // cell: every hop the naming walk crossed is a write proven (without
    // assumptions) to miss the cell. This is how a fact carried unchanged
    // through earlier steps, and so still named at its mint version, meets an
    // effect summary whose `before` is the later live state.
    if !pointer.base.is_local_block()
        && let (Some(left_version), Some(right_version)) = (
            cell_version_point(
                &crate::kernel::intern_memory(left.clone()),
                pointer,
                crate::kernel::load_access_width_or_widest(
                    &crate::kernel::intern_memory(left.clone()),
                    pointer,
                ),
            ),
            cell_version_point(
                &crate::kernel::intern_memory(right.clone()),
                pointer,
                crate::kernel::load_access_width_or_widest(
                    &crate::kernel::intern_memory(right.clone()),
                    pointer,
                ),
            ),
        )
        && left_version == right_version
    {
        return true;
    }
    if pointer.base.is_local_block()
        || !left
            .blocks
            .iter()
            .filter(|(block, _)| block.is_havoc_block() || block.is_call_havoc_block())
            .eq(right
                .blocks
                .iter()
                .filter(|(block, _)| block.is_havoc_block() || block.is_call_havoc_block()))
        || left.blocks.get(&pointer.base) != right.blocks.get(&pointer.base)
    {
        return false;
    }
    // Every arm below decides whether the cell's *address* is a different
    // address from the load's, and that is not the question this function
    // asks: it is deciding whether the two states hold one value for this
    // load, and a cell at `p + 1` holding one byte is a different address
    // from `p` while being the second byte a four-byte read there returns.
    // `1a3b2701` put the byte question in front of the three sibling
    // comparisons; this is the fourth, and the constant-offset arm —
    // `shared_pointer_byte_offset_from_base(...) != 0` — is the plainest statement of
    // the confusion, calling a cell four bytes into an eight-byte read
    // separate from it.
    let load_bytes = crate::kernel::load_access_width_or_widest(
        &crate::kernel::intern_memory(left.clone()),
        pointer,
    );
    differing_cell_pointers_possibly_aliasing(left, right, &pointer.base)
        .into_iter()
        .all(|cell| {
            differing_cell_bytes_miss_the_load(left, right, &cell, pointer, load_bytes, assumptions)
                && (cell.blocks_proven_distinct(pointer)
                || pointer_offsets_with_common_base_proven_distinct(&cell, pointer, assumptions)
                || pointers_proven_distinct_for_memory_resolution(&cell, pointer, assumptions)
                || shared_pointer_byte_offset_from_base(&cell, pointer)
                    .and_then(|offset| offset.operand_view().word32_constant())
                    .is_some_and(|offset| offset != 0)
                || assumptions.ranges_directly_disjoint_from_pointer(
                    &[MemoryRange::new(
                        cell.clone(),
                        OldMachineTerm::constant(0),
                        OldMachineTerm::constant(1),
                    )],
                    pointer,
                )
                // Last: the same composition rule the mutates-only arm above
                // and the tracker's `Store` arm spend, so the three agree.
                || owned_composition_store_separated_evidence(&cell, differing_cell_byte_width(left, right, &cell), pointer, load_bytes, assumptions).is_some())
        })
}

/// The cells the two states disagree about that a load in `block` could be
/// reading: its own block, and every other block not proven distinct from it.
/// A differently spelled block is not a different object, so the caller must
/// still discharge each of these cells by offset or by separation evidence.
fn differing_cell_pointers_possibly_aliasing(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    block: &AddressBase,
) -> BTreeSet<Address> {
    left.cells
        .keys()
        .chain(right.cells.keys())
        .filter(|pointer| pointer.base.observable_by_load(block))
        .filter(|pointer| left.cells.get(pointer) != right.cells.get(pointer))
        .cloned()
        .collect()
}

/// Whether `materialized` holds, at `pointer`, exactly the `kind` read of
/// `pointer` that `symbolic` holds: a cell whose value is that read, taken
/// from a state that agrees with `symbolic` there.
///
/// The cell answers for the read only when it is the read: the value is of
/// the read's kind and is itself a load of that kind. A cell of another width
/// holds other bytes than the read returns, and one of the other signedness
/// holds another number.
fn memory_materializes_atomic_load(
    materialized: &SymbolicMemory,
    symbolic: &SymbolicMemory,
    pointer: &Address,
    kind: LoadKind,
) -> bool {
    let Some(value) = materialized.known_value(pointer) else {
        return false;
    };
    kind.reads_value(&value)
        && matches!(
            value,
            ProgramValue::Int8(OldMachineTerm::MemoryLoad(source, source_pointer, source_kind))
                | ProgramValue::Int16(OldMachineTerm::MemoryLoad(source, source_pointer, source_kind))
                | ProgramValue::Int32(OldMachineTerm::MemoryLoad(source, source_pointer, source_kind))
                | ProgramValue::UInt8(OldMachineTerm::MemoryLoad(source, source_pointer, source_kind))
                | ProgramValue::UInt16(OldMachineTerm::MemoryLoad(source, source_pointer, source_kind))
                | ProgramValue::UInt32(OldMachineTerm::MemoryLoad(source, source_pointer, source_kind))
                if source_pointer.as_ref() == pointer
                    && source_kind == kind
                    && memories_match_for_pointer_load(source.memory(), symbolic, pointer)
        )
}

/// Certifies the narrow frame rule used by execution proofs for ordinary C
/// conditions. Address-dependent loads are transported from the inside out;
/// other proposition forms must be re-established explicitly.
pub(crate) fn prove_program_condition_fact_transport(
    fact: &Proposition,
    after: &ProgramPoint,
    assumptions: &PureFactContext,
) -> Option<Theorem> {
    prove_program_condition_fact_transport_with_assumptions(fact, after, Some((assumptions, false)))
}

#[cfg(test)]
pub(crate) fn prove_program_condition_fact_direct_transport(
    fact: &Proposition,
    after: &ProgramPoint,
    assumptions: &PureFactContext,
) -> Option<Theorem> {
    prove_program_condition_fact_transport_with_assumptions(fact, after, Some((assumptions, true)))
}

/// Constructs condition-transport authority from the exact contextual facts
/// consumed by its bounded check. The explicit source remains the innermost
/// premise so consumers can distinguish it from frame or equality evidence.
pub(crate) fn program_condition_fact_transport_theorem(
    source: &Proposition,
    target: Proposition,
    premises: impl IntoIterator<Item = Proposition>,
) -> Theorem {
    let transport = Proposition::Implies(Box::new(source.clone()), Box::new(target));
    let premises = premises
        .into_iter()
        .filter(|premise| premise != source)
        .collect::<BTreeSet<_>>();
    Theorem::new(premises.into_iter().rev().fold(transport, |body, premise| {
        Proposition::Implies(Box::new(premise), Box::new(body))
    }))
}

/// Parses the retained-premise representation of a condition transport.
/// Returns the exact contextual premises followed by the transported target;
/// arbitrary implication theorems and malformed source placement are rejected.
pub(crate) fn program_condition_fact_transport_parts<'a>(
    theorem: &'a Theorem,
    source: &Proposition,
) -> Option<(Vec<&'a Proposition>, &'a Proposition)> {
    let mut proposition = theorem.proposition();
    let mut premises = Vec::new();
    loop {
        let Proposition::Implies(premise, body) = proposition else {
            return None;
        };
        if premise.as_ref() == source {
            return matches!(body.as_ref(), Proposition::ConditionIs(_, _))
                .then_some((premises, body.as_ref()));
        }
        premises.push(premise.as_ref());
        proposition = body.as_ref();
    }
}

/// Applies condition-transport evidence only when every retained contextual
/// premise is an exact fact of the supplied context. The explicit source is
/// supplied separately because callers already hold its proof when applying
/// the innermost implication.
pub(crate) fn program_condition_fact_transport_target_in_context<'a>(
    theorem: &'a Theorem,
    source: &Proposition,
    assumptions: &PureFactContext,
) -> Option<&'a Proposition> {
    let (premises, target) = program_condition_fact_transport_parts(theorem, source)?;
    premises
        .into_iter()
        .all(|premise| assumptions.proves_exact(premise))
        .then_some(target)
}

fn prove_program_condition_fact_transport_with_assumptions(
    fact: &Proposition,
    after: &ProgramPoint,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<Theorem> {
    #[cfg(test)]
    crate::kernel::search::record_discovery("condition fact transport");
    if crate::instrumentation::replay_forbids_discovery("condition fact transport") {
        return None;
    }
    // Per-arm returns, no shared conclusion local: this function sits in
    // transport recursion, and a by-value `Proposition` local overflows the
    // expansion stack.
    match fact {
        Proposition::ConditionIs(condition, value) => {
            let (transported, premises) = crate::kernel::collect_consulted_premises(|| {
                crate::kernel::capture_implicit_consulted_premises(|| {
                    transport_framed_atomic_condition(condition.old_form(), after, assumptions)
                })
            });
            let transported = transported?;
            if &transported == condition.old_form() {
                return None;
            }
            // As with target-directed transport, the recorded derivation is a candidate
            // dependency list, not proof authority. Re-run the exact rewrite
            // using only those facts (and the explicit source premise) before
            // placing the list in a theorem.
            if let Some((_, direct)) = assumptions {
                let restricted = premises
                    .iter()
                    .cloned()
                    .fold(PureFactContext::new(), |context, premise| {
                        context.assume_proposition(premise)
                    })
                    .assume_proposition(fact.clone());
                if transport_framed_atomic_condition(
                    condition.old_form(),
                    after,
                    Some((&restricted, direct)),
                ) != Some(transported.clone())
                {
                    return None;
                }
            }
            Some(program_condition_fact_transport_theorem(
                fact,
                Proposition::condition_is(transported, *value),
                premises,
            ))
        }
        _ => None,
    }
}

/// Canonicalizes every load in a term for structural comparison: cached
/// cells resolve to their values and remaining loads use the canonical
/// memory for their pointer.
pub(crate) fn canonicalize_atomic_loads(term: &OldMachineTerm) -> OldMachineTerm {
    let cacheable = term_is_shallow_structural_cache_key(term);
    if cacheable
        && let Some(hit) = ATOMIC_LOADS_CACHE.with(|cache| cache.borrow().get(term).cloned())
    {
        return hit;
    }
    let result = crate::instrumentation::measure_operation(
        "kernel",
        "canonical form",
        "canonicalize atomic loads: miss",
        || canonicalize_atomic_loads_deep(term),
    );
    if cacheable {
        ATOMIC_LOADS_CACHE.with(|cache| cache.borrow_mut().insert(term.clone(), result.clone()));
    }
    result
}

thread_local! {
    static DEEP_MEMORY_CACHE: std::cell::RefCell<
        std::collections::HashMap<crate::kernel::SharedMemory, SymbolicMemory>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    static ATOMIC_LOADS_CACHE: std::cell::RefCell<
        std::collections::HashMap<OldMachineTerm, OldMachineTerm>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    #[cfg(test)]
    static ATOMIC_CANONICALIZATION_TERM_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_atomic_canonicalization_term_visits() {
    ATOMIC_CANONICALIZATION_TERM_VISITS.with(|visits| visits.set(0));
}

#[cfg(test)]
pub(crate) fn atomic_canonicalization_term_visits() -> usize {
    ATOMIC_CANONICALIZATION_TERM_VISITS.with(std::cell::Cell::get)
}

pub(crate) fn clear_load_equality_memos() {
    DAG_LOAD_EQUALITY_POSITIVE_MEMO.with(|memo| memo.borrow_mut().clear());
    DAG_LOAD_EQUALITY_UNPROVEN_MEMO.with(|memo| memo.borrow_mut().clear());
}

pub(crate) fn clear_canonical_form_caches() {
    DEEP_MEMORY_CACHE.with(|cache| cache.borrow_mut().clear());
    ATOMIC_LOADS_CACHE.with(|cache| cache.borrow_mut().clear());
    // The resource tracker's per-state version memos are canonical-form
    // caches too: they answer which point a term's name embeds.
    crate::kernel::resource_tracker::clear_version_memos();
}

/// Recursive `Hash` and `Eq` implementations make a whole-term cache key
/// unsafe at arbitrary depth. This iterative preflight controls only whether
/// memoization is used. Shared address indices are retained children whose
/// keys hash by identity; this preflight does not reopen their expressions.
/// The remaining explicit native term and offset structure determines depth.
pub(crate) fn term_is_shallow_structural_cache_key(term: &OldMachineTerm) -> bool {
    const MAX_RECURSIVE_KEY_DEPTH: usize = 256;
    enum Node<'a> {
        Term(&'a OldMachineTerm, usize),
        Condition(&'a OldConditionTerm, usize),
        Offset(&'a AddressOffset, usize),
    }
    let mut pending = vec![Node::Term(term, 1)];
    while let Some(node) = pending.pop() {
        let depth = match node {
            Node::Term(_, depth) | Node::Condition(_, depth) | Node::Offset(_, depth) => depth,
        };
        if depth > MAX_RECURSIVE_KEY_DEPTH {
            return false;
        }
        match node {
            Node::Term(term, depth) => match term {
                OldMachineTerm::ThreadHandle(_) => {}
                bits32_constant!(_)
                | OldMachineTerm::Variable(_)
                | int64_constant!(_)
                | uint64_constant!(_)
                | native_constant!(_, _) => {}
                OldMachineTerm::MemoryLoad(_, pointer, _) => {
                    pending.push(Node::Offset(&pointer.offset, depth + 1));
                }
                OldMachineTerm::IntegerAddress(pointer, _) => {
                    pending.push(Node::Offset(&pointer.offset, depth + 1));
                }
                crate::kernel::binary_machine_term!(left, right) => {
                    pending.push(Node::Term(right, depth + 1));
                    pending.push(Node::Term(left, depth + 1));
                }
                OldMachineTerm::Float32Binary { left, right, .. }
                | OldMachineTerm::Float64Binary { left, right, .. } => {
                    pending.push(Node::Term(right, depth + 1));
                    pending.push(Node::Term(left, depth + 1));
                }
                crate::kernel::unary_machine_term!(value) => {
                    pending.push(Node::Term(value, depth + 1));
                }
                OldMachineTerm::BoolCast { value, .. } => {
                    pending.push(Node::Condition(value, depth + 1));
                }
                OldMachineTerm::If {
                    condition,
                    then_term,
                    else_term,
                } => {
                    pending.push(Node::Term(else_term, depth + 1));
                    pending.push(Node::Term(then_term, depth + 1));
                    pending.push(Node::Condition(condition, depth + 1));
                }
                OldMachineTerm::RangeFold {
                    start,
                    end,
                    initial,
                    body,
                    ..
                } => {
                    pending.push(Node::Term(body, depth + 1));
                    pending.push(Node::Term(initial, depth + 1));
                    pending.push(Node::Term(end, depth + 1));
                    pending.push(Node::Term(start, depth + 1));
                }
                OldMachineTerm::PureFunctionApplication { arguments, .. } => {
                    pending.extend(
                        arguments
                            .iter()
                            .map(|argument| Node::Term(argument, depth + 1)),
                    );
                }
                OldMachineTerm::ClickFunctionApplication { .. }
                | OldMachineTerm::PureApplicationCount(_)
                | OldMachineTerm::AlgebraicMatch { .. }
                | OldMachineTerm::IntegerToMachine { .. } => {}
            },
            Node::Condition(condition, depth) => match condition {
                OldConditionTerm::PointerEqual(_, _) => return false,

                OldConditionTerm::AlgebraicEqual(_, _) => return false,
                OldConditionTerm::Constant(_) | OldConditionTerm::Variable(_) => {}
                crate::kernel::integer_comparison_condition!(_, _) => return false,
                crate::kernel::binary_bitvector_condition!(left, right) => {
                    pending.push(Node::Term(right, depth + 1));
                    pending.push(Node::Term(left, depth + 1));
                }
                OldConditionTerm::Float32(float_condition)
                | OldConditionTerm::Float64(float_condition) => match float_condition {
                    FloatCondition::Comparison { left, right, .. } => {
                        pending.push(Node::Term(right, depth + 1));
                        pending.push(Node::Term(left, depth + 1));
                    }
                    FloatCondition::Classification { value, .. } => {
                        pending.push(Node::Term(value, depth + 1));
                    }
                },
                OldConditionTerm::AddressOffsetEqual(left, right) => {
                    pending.push(Node::Offset(right, depth + 1));
                    pending.push(Node::Offset(left, depth + 1));
                }
                OldConditionTerm::AddressEqual(left, right) => {
                    pending.push(Node::Offset(&right.offset, depth + 1));
                    pending.push(Node::Offset(&left.offset, depth + 1));
                }
                // As a word-valued Click application, whose arguments are
                // keyed by the application's interned identity.
                OldConditionTerm::BoolApplication(_) => {}
                OldConditionTerm::BoolIf {
                    condition,
                    then_condition,
                    else_condition,
                } => {
                    pending.push(Node::Condition(else_condition, depth + 1));
                    pending.push(Node::Condition(then_condition, depth + 1));
                    pending.push(Node::Condition(condition, depth + 1));
                }
                OldConditionTerm::BoolEqual(left, right) => {
                    pending.push(Node::Condition(right, depth + 1));
                    pending.push(Node::Condition(left, depth + 1));
                }
            },
            Node::Offset(offset, depth) => match offset.view() {
                OffsetView::Constant(_) | OffsetView::Variable(_) => {}
                OffsetView::Add(left, right) => {
                    pending.push(Node::Offset(right, depth + 1));
                    pending.push(Node::Offset(left, depth + 1));
                }
                // Scaled indices hash by retained identity, including legacy
                // operands; they add no recursive native-key depth.
                OffsetView::Int32Scaled { .. } | OffsetView::Int64Scaled { .. } => {}
            },
        }
    }
    true
}

enum AtomicCanonicalizationTask<'a> {
    Visit(&'a OldMachineTerm),
    VisitCondition(&'a OldConditionTerm),
    VisitOffset(&'a AddressOffset),
    RebuildBinary(BitvectorBinaryOp),
    RebuildUnary(BitvectorUnaryOp),
    RebuildConditionBinary(BitvectorComparisonOp),
    RebuildFloatCondition {
        is_float64: bool,
        condition: FloatCondition,
        term_count: usize,
    },
    RebuildAddressOffsetEqual,
    RebuildAddressEqual {
        left_block: AddressBase,
        right_block: AddressBase,
    },
    RebuildOffsetAdd,
    RebuildIf,
    RebuildRangeFold {
        accumulator: Variable,
        item: Variable,
    },
    RebuildPureFunction {
        name: String,
        argument_count: usize,
    },
}

/// The integer a state's own cell at `pointer` gives a `kind` read there,
/// when the cell is exactly that read and holds something other than `load`
/// itself. A cell of another kind holds other bytes or another number than
/// the read returns, so it answers nothing.
fn cell_integer_for_read(
    memory: &SymbolicMemory,
    pointer: &Address,
    kind: LoadKind,
    load: &OldMachineTerm,
) -> Option<OldMachineTerm> {
    let ExpressionOutcome::Value(cell) = memory.load(pointer) else {
        return None;
    };
    // A character read of a one-byte cell of the other signedness reads
    // the same bits (`LoadKind::read_cell`).
    let cell = kind.read_cell(&cell)?;
    match cell {
        crate::kernel::integer64_c_value!(value) if &value != load => Some(value),
        _ => None,
    }
}

/// Compare only the two named wide reads, retaining their kind and recorded
/// history. Do not route wide arithmetic through the int32 equality graph.
pub(crate) fn wide_loads_have_same_canonical_value(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    let origin = |term: &OldMachineTerm| match term {
        OldMachineTerm::Variable(variable) => {
            crate::kernel::eval::registered_load_origin_term_for_variable(variable)
        }
        OldMachineTerm::MemoryLoad(..) => Some(term.clone()),
        _ => None,
    };
    let (Some(left), Some(right)) = (origin(left), origin(right)) else {
        return false;
    };
    if !matches!(
        (&left, &right),
        (
            OldMachineTerm::MemoryLoad(_, _, LoadKind::Bits64),
            OldMachineTerm::MemoryLoad(_, _, LoadKind::Bits64)
        )
    ) {
        return false;
    }
    crate::kernel::canonical_term(&left) == crate::kernel::canonical_term(&right)
        && !crate::kernel::reasoning::load_equality_lacks_recorded_evidence(
            &left,
            &right,
            assumptions,
        )
}

/// Check a wide read against its recorded value under explicitly selected
/// premises. The typed memory walk must preserve the complete eight-byte
/// access across every effect; it cannot infer a value from a partial store.
pub(crate) fn wide_read_has_recorded_value(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    let origin = |term: &OldMachineTerm| match term {
        OldMachineTerm::Variable(variable) => {
            crate::kernel::eval::registered_load_origin_term_for_variable(variable)
        }
        OldMachineTerm::MemoryLoad(..) => crate::kernel::eval::scalar_read_observation(
            crate::kernel::MachineOperandView::Old(term),
        )
        .map(|read| {
            crate::kernel::OldMachineTerm::read_named(
                read.origin.unwrap_or(read.point).for_legacy_read(),
                read.pointer,
                read.kind,
            )
        }),
        _ => None,
    };
    let left_origin = origin(left);
    let right_origin = origin(right);
    // A load identity can occur in several model arms. A producer records
    // the complete load expression it just named, independently of the name's
    // first live origin. Check those selected observations, then retain the
    // original route for facts whose earlier origin is the useful one.
    let latest = |term: &OldMachineTerm| match term {
        OldMachineTerm::Variable(variable) => {
            crate::kernel::eval::latest_wide_load_observation(variable)
        }
        OldMachineTerm::MemoryLoad(..) => {
            crate::kernel::eval::latest_scalar_read_observation(term).or_else(|| Some(term.clone()))
        }
        _ => None,
    };
    let latest_left = latest(left);
    let latest_right = latest(right);
    if (latest_left
        .as_ref()
        .is_some_and(|load| Some(load) != left_origin.as_ref())
        || latest_right
            .as_ref()
            .is_some_and(|load| Some(load) != right_origin.as_ref()))
        && wide_read_observations_have_value(
            left,
            right,
            latest_left.as_ref().or(left_origin.as_ref()),
            latest_right.as_ref().or(right_origin.as_ref()),
            assumptions,
        )
    {
        return true;
    }
    wide_read_observations_have_value(
        left,
        right,
        left_origin.as_ref(),
        right_origin.as_ref(),
        assumptions,
    )
}

fn wide_read_observations_have_value(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    left_origin: Option<&OldMachineTerm>,
    right_origin: Option<&OldMachineTerm>,
    assumptions: &PureFactContext,
) -> bool {
    if left_origin.is_none() && right_origin.is_none() {
        return false;
    }
    if left_origin
        .iter()
        .chain(right_origin.iter())
        .any(|term| !matches!(term, OldMachineTerm::MemoryLoad(_, _, LoadKind::Bits64)))
    {
        return false;
    }
    // Wide reads do not enter the int32 congruence graph. Two spellings of
    // one address can nevertheless read the same eight bytes: first check
    // the selected pointer equality, then retain both reads' memory history.
    // A cached read may name an earlier state than its surface expression,
    // so a shared current state is sufficient but not necessary.
    if let (
        Some(OldMachineTerm::MemoryLoad(left_memory, left_pointer, LoadKind::Bits64)),
        Some(OldMachineTerm::MemoryLoad(right_memory, right_pointer, LoadKind::Bits64)),
    ) = (left_origin, right_origin)
        && crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
            left_pointer,
            right_pointer,
            assumptions,
        )
    {
        if left_memory.point() == right_memory.point() {
            return true;
        }
        if let (Some(left_cell), Some(right_cell)) = (
            bounded_recorded_cell_source(
                left_memory.shared_memory(),
                left_pointer,
                8,
                assumptions,
                64,
            ),
            bounded_recorded_cell_source(
                right_memory.shared_memory(),
                right_pointer,
                8,
                assumptions,
                64,
            ),
        ) && left_cell.node() == right_cell.node()
        {
            return true;
        }
    }
    let stored_value_matches = |read: Option<&OldMachineTerm>, other: &OldMachineTerm| {
        let Some(OldMachineTerm::MemoryLoad(memory, pointer, LoadKind::Bits64)) = read else {
            return false;
        };
        // A simple read-value normalization must not scan the whole path.
        // Longer frames need an explicit intervening proof step.
        let (producer, resolution) =
            bounded_recorded_cell_resolution(memory.shared_memory(), pointer, 8, assumptions, 64);
        let value = resolution.as_ref().and_then(|(cell, _)| {
            cell.resolved_value(pointer, LoadKind::Bits64).or_else(|| {
                // The cheap history classifier may stop at a store whose address
                // uses a recorded pointer-load identity. Check that one endpoint
                // with the full pointer matcher; never search earlier writes or
                // accept an overlapping store of a different width.
                let step = cell.node().derivation()?;
                let MemoryDerivation::Store {
                    pointer: write,
                    value,
                    ..
                } = step.as_ref()
                else {
                    return None;
                };
                (LoadKind::Bits64.reads_value(value.native())
                    && crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
                        write,
                        pointer,
                        assumptions,
                    ))
                .then(|| value.native().clone())
            })
        });
        // Compare only a complete typed word in the current native-width graph.
        let equal = match value.as_ref().map(ProgramValue::numeric_value) {
            Some(ProgramValue::Int64(word) | ProgramValue::UInt64(word)) => {
                assumptions.uint64_values_known_equal(word, other)
            }
            _ => false,
        };
        READ_RESOLUTION_DIAGNOSTICS.with(|slot| {
            if let Some(diagnostics) = slot.borrow_mut().as_mut() {
                if diagnostics.len() >= 16 {
                    return;
                }
                let (stopped_at, reason) = match &resolution {
                    None => (None, "recursive read query already active"),
                    Some((cell, stop)) => {
                        let path = match cell {
                            MemoryDagCell::Stored { path, .. }
                            | MemoryDagCell::Unwritten { path, .. } => path,
                        };
                        let reason = if path.len() >= 64 {
                            "64-hop query limit reached"
                        } else {
                            match stop {
                                CellWalkStop::CommonState => "common state reached",
                                CellWalkStop::RetainedValue => {
                                    "retained typed value before cache forgetting"
                                }
                                CellWalkStop::OldestRecorded => "oldest recorded state reached",
                                CellWalkStop::Affected => "step affects the read's bytes",
                                CellWalkStop::NotShownSeparate => {
                                    "step not proved separate from the read"
                                }
                            }
                        };
                        (Some(cell.node().clone()), reason)
                    }
                };
                diagnostics.push(ReadResolutionDiagnostic {
                    read: read.unwrap().clone(),
                    producer,
                    stopped_at,
                    reason,
                    recovered: value,
                    expected: other.clone(),
                    equal,
                });
            }
        });
        equal
    };
    stored_value_matches(left_origin, right) || stored_value_matches(right_origin, left)
}

/// A read of at most four bytes whose recorded stored value is `other`, by
/// the same bounded walk the 64-bit rule above takes, read against the cited
/// conditions only. The store a frame ends at must write the read's whole
/// width: `t[j + 1] = 0` under a cited `j == 2` is the value `t[3]` reads.
pub(crate) fn narrow_read_has_recorded_value(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    // Identical conversions preserve equality of the selected raw reads.
    // Signed narrow reads are represented by an unsigned read wrapped in
    // a machine conversion. Walk only the two explicitly named terms.
    let (mut left, mut right) = (left, right);
    while let (Some((left_op, left_value)), Some((right_op, right_value))) =
        (left.as_unary(), right.as_unary())
    {
        if left_op != right_op {
            break;
        }
        crate::instrumentation::record_deterministic_work(1);
        left = left_value;
        right = right_value;
    }
    let origin = |term: &OldMachineTerm| match term {
        OldMachineTerm::Variable(variable) => {
            crate::kernel::eval::registered_load_origin_term_for_variable(variable)
        }
        OldMachineTerm::MemoryLoad(..) => Some(term.clone()),
        _ => None,
    };
    // A read compared through its 32-bit widening (as C promotes it) has
    // its stored value compared through the same widening.
    let stored_value_matches = |term: &OldMachineTerm, other: &OldMachineTerm| {
        let (term, widening) = match term {
            OldMachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                value,
                from: source,
                to: destination,
            } if source.format().bits() < 32 && destination.format().bits() == 32 => {
                (value.as_ref(), Some((*source, *destination)))
            }
            term => (term, None),
        };
        let Some(OldMachineTerm::MemoryLoad(memory, pointer, kind)) = origin(term) else {
            return false;
        };
        if !matches!(
            kind,
            LoadKind::Int8 | LoadKind::UInt8 | LoadKind::Int16 | LoadKind::UInt16 | LoadKind::Int32
        ) {
            return false;
        }
        let (_, resolution) = bounded_recorded_cell_resolution(
            memory.shared_memory(),
            &pointer,
            kind.byte_width(),
            assumptions,
            64,
        );
        let Some(value) = resolution.and_then(|(cell, _)| cell.resolved_value(&pointer, kind))
        else {
            return false;
        };
        let word = match value {
            ProgramValue::Bool(word)
            | ProgramValue::Int8(word)
            | ProgramValue::Int16(word)
            | ProgramValue::Int32(word)
            | ProgramValue::UInt8(word)
            | ProgramValue::UInt16(word)
            | ProgramValue::UInt32(word) => word,
            _ => return false,
        };
        // The comparison's format: the widening's, or a narrow read's own.
        let (word, format) = match (widening, kind) {
            (Some((source, destination)), _) => (
                OldMachineTerm::machine_integer_cast(source, destination, word),
                MachineIntegerType::Int32,
            ),
            (None, LoadKind::Int8) => (word, MachineIntegerType::Int8),
            (None, LoadKind::UInt8) => (word, MachineIntegerType::UInt8),
            (None, LoadKind::Int16) => (word, MachineIntegerType::Int16),
            (None, LoadKind::UInt16) => (word, MachineIntegerType::UInt16),
            (None, _) => (word, MachineIntegerType::Int32),
        };
        &word == other
            || assumptions.decide(&OldConditionTerm::Compare {
                format,
                relation: CompareRelation::Equal,
                left: Box::new(word),
                right: Box::new(other.clone()),
            }) == Some(true)
    };
    stored_value_matches(left, right) || stored_value_matches(right, left)
}

/// Whether the read of `value_type` at `pointer` in `memory` ends, by the
/// same bounded walk read against the cited conditions only, at a store that
/// wrote its whole width: that read is of written bytes.
pub(crate) fn read_is_of_a_recorded_store(
    memory: &SymbolicMemory,
    pointer: &Address,
    value_type: ProgramType,
    assumptions: &PureFactContext,
) -> bool {
    let Some(kind) = LoadKind::of_type(value_type) else {
        return false;
    };
    let memory = crate::kernel::intern_memory_ref(memory);
    let (_, resolution) =
        bounded_recorded_cell_resolution(&memory, pointer, kind.byte_width(), assumptions, 64);
    matches!(
        resolution,
        Some((ref cell @ MemoryDagCell::Stored { .. }, _)) if cell.resolved_value(pointer, kind).is_some()
    )
}

/// Deep, assumption-free canonical form for a term: every load resolves its
/// cached cell or canonicalizes its state and pointer, at every depth,
/// including inside conditionals, folds, and pointer offsets. Two forms
/// of the same value produced from different memory states canonicalize
/// identically whenever the difference is representational. The walk is
/// over the term and the values its loads resolve to, each recorded before
/// the state that holds it, so it is finite with no depth cut.
pub(super) fn canonicalize_atomic_loads_deep(term: &OldMachineTerm) -> OldMachineTerm {
    let mut tasks = vec![AtomicCanonicalizationTask::Visit(term)];
    let mut results = Vec::new();
    let mut condition_results = Vec::new();
    let mut offset_results = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            AtomicCanonicalizationTask::Visit(term) => {
                #[cfg(test)]
                ATOMIC_CANONICALIZATION_TERM_VISITS.with(|visits| visits.set(visits.get() + 1));
                match term {
                    OldMachineTerm::ThreadHandle(_) => results.push(term.clone()),
                    bits32_constant!(_)
                    | OldMachineTerm::Variable(_)
                    | int64_constant!(_)
                    | uint64_constant!(_)
                    | native_constant!(_, _) => results.push(term.clone()),
                    OldMachineTerm::IntegerAddress(_, _) => results.push(term.clone()),
                    OldMachineTerm::MemoryLoad(memory, pointer, kind) => {
                        if memory.is_entry_read() {
                            results.push(term.clone());
                            continue;
                        }
                        let kind = *kind;
                        let canonical_pointer = canonicalize_pointer_loads(pointer);
                        let resolved =
                            cell_integer_for_read(memory.memory(), &canonical_pointer, kind, term)
                                .or_else(|| {
                                    cell_integer_for_read(memory.memory(), pointer, kind, term)
                                });
                        let Some(mut value) = resolved else {
                            // A symbolic read with a selected point already has its version.
                            if memory.read_version_id().is_some() {
                                results.push(term.clone());
                                continue;
                            }
                            // Name the cell by its version before restricting
                            // the state: the restriction is a fresh intern
                            // with no derivation, so a version walk over it
                            // could not cross anything. Walking the original
                            // state lets two loads of one unwritten cell at
                            // different points share one canonical form.
                            let version = cell_version_point(
                                memory.shared_memory(),
                                &canonical_pointer,
                                crate::kernel::load_term_access_width(
                                    memory.shared_memory(),
                                    &canonical_pointer,
                                    kind,
                                ),
                            );
                            let version = version.as_ref().unwrap_or(memory.shared_memory());
                            results.push(crate::kernel::OldMachineTerm::read_named(
                                ProgramPoint::walked(
                                    &(canonical_projected_load_memory(version, &canonical_pointer)),
                                    memory,
                                ),
                                canonical_pointer,
                                kind,
                            ));
                            continue;
                        };

                        // A materialized cell may itself contain a load from
                        // another state. Follow that root-load chain here
                        // rather than recursively entering one Rust frame per
                        // cell. Composite recorded values re-enter the normal
                        // structural worklist below.
                        loop {
                            let OldMachineTerm::MemoryLoad(next_memory, next_pointer, next_kind) =
                                &value
                            else {
                                results.push(canonicalize_atomic_loads_deep(&value));
                                break;
                            };
                            if next_memory.is_entry_read() {
                                results.push(value);
                                break;
                            }
                            let next_kind = *next_kind;
                            let canonical_pointer = canonicalize_pointer_loads(next_pointer);
                            let resolved = cell_integer_for_read(
                                next_memory.memory(),
                                &canonical_pointer,
                                next_kind,
                                &value,
                            )
                            .or_else(|| {
                                cell_integer_for_read(
                                    next_memory.memory(),
                                    next_pointer,
                                    next_kind,
                                    &value,
                                )
                            });
                            if let Some(next) = resolved {
                                value = next;
                                continue;
                            }
                            if next_memory.read_version_id().is_some() {
                                results.push(value);
                                break;
                            }
                            let version = cell_version_point(
                                next_memory.shared_memory(),
                                &canonical_pointer,
                                crate::kernel::load_term_access_width(
                                    next_memory.shared_memory(),
                                    &canonical_pointer,
                                    next_kind,
                                ),
                            );
                            let version = version.as_ref().unwrap_or(next_memory.shared_memory());
                            results.push(crate::kernel::OldMachineTerm::read_named(
                                ProgramPoint::walked(
                                    &(canonical_projected_load_memory(version, &canonical_pointer)),
                                    next_memory,
                                ),
                                canonical_pointer,
                                next_kind,
                            ));
                            break;
                        }
                    }
                    OldMachineTerm::If {
                        condition,
                        then_term,
                        else_term,
                    } => {
                        tasks.push(AtomicCanonicalizationTask::RebuildIf);
                        tasks.push(AtomicCanonicalizationTask::Visit(else_term));
                        tasks.push(AtomicCanonicalizationTask::Visit(then_term));
                        tasks.push(AtomicCanonicalizationTask::VisitCondition(condition));
                    }
                    OldMachineTerm::RangeFold {
                        start,
                        end,
                        initial,
                        accumulator,
                        item,
                        body,
                    } => {
                        tasks.push(AtomicCanonicalizationTask::RebuildRangeFold {
                            accumulator: *accumulator,
                            item: *item,
                        });
                        tasks.push(AtomicCanonicalizationTask::Visit(body));
                        tasks.push(AtomicCanonicalizationTask::Visit(initial));
                        tasks.push(AtomicCanonicalizationTask::Visit(end));
                        tasks.push(AtomicCanonicalizationTask::Visit(start));
                    }
                    OldMachineTerm::PureFunctionApplication { name, arguments } => {
                        tasks.push(AtomicCanonicalizationTask::RebuildPureFunction {
                            name: name.clone(),
                            argument_count: arguments.len(),
                        });
                        for argument in arguments.iter().rev() {
                            tasks.push(AtomicCanonicalizationTask::Visit(argument));
                        }
                    }
                    // A `Bool`'s cast is kept as built, as the `Bool` forms are.
                    OldMachineTerm::ClickFunctionApplication { .. }
                    | OldMachineTerm::PureApplicationCount(_)
                    | OldMachineTerm::AlgebraicMatch { .. }
                    | OldMachineTerm::BoolCast { .. }
                    | OldMachineTerm::IntegerToMachine { .. } => results.push(term.clone()),
                    term => match (term.as_binary(), term.as_unary()) {
                        (Some((op, left, right)), _) => {
                            tasks.push(AtomicCanonicalizationTask::RebuildBinary(op));
                            tasks.push(AtomicCanonicalizationTask::Visit(right));
                            tasks.push(AtomicCanonicalizationTask::Visit(left));
                        }
                        (_, Some((op, value))) => {
                            tasks.push(AtomicCanonicalizationTask::RebuildUnary(op));
                            tasks.push(AtomicCanonicalizationTask::Visit(value));
                        }
                        _ => unreachable!("every other variant has its own arm"),
                    },
                }
            }
            AtomicCanonicalizationTask::VisitCondition(condition) => match condition {
                OldConditionTerm::AlgebraicEqual(_, _) | OldConditionTerm::PointerEqual(..) => {
                    condition_results.push(condition.clone())
                }
                crate::kernel::integer_comparison_condition!(_, _) => {
                    condition_results.push(condition.clone())
                }
                OldConditionTerm::Constant(_) | OldConditionTerm::Variable(_) => {
                    condition_results.push(condition.clone())
                }
                // `Bool` values are kept as built, as algebraic equalities are.
                condition if condition.is_bool_value_form() => {
                    condition_results.push(condition.clone())
                }
                OldConditionTerm::Float32(float_condition) => {
                    let term_count = match float_condition {
                        FloatCondition::Comparison { .. } => 2,
                        FloatCondition::Classification { .. } => 1,
                    };
                    tasks.push(AtomicCanonicalizationTask::RebuildFloatCondition {
                        is_float64: false,
                        condition: float_condition.clone(),
                        term_count,
                    });
                    match float_condition {
                        FloatCondition::Comparison { left, right, .. } => {
                            tasks.push(AtomicCanonicalizationTask::Visit(right));
                            tasks.push(AtomicCanonicalizationTask::Visit(left));
                        }
                        FloatCondition::Classification { value, .. } => {
                            tasks.push(AtomicCanonicalizationTask::Visit(value));
                        }
                    }
                }
                OldConditionTerm::Float64(float_condition) => {
                    let term_count = match float_condition {
                        FloatCondition::Comparison { .. } => 2,
                        FloatCondition::Classification { .. } => 1,
                    };
                    tasks.push(AtomicCanonicalizationTask::RebuildFloatCondition {
                        is_float64: true,
                        condition: float_condition.clone(),
                        term_count,
                    });
                    match float_condition {
                        FloatCondition::Comparison { left, right, .. } => {
                            tasks.push(AtomicCanonicalizationTask::Visit(right));
                            tasks.push(AtomicCanonicalizationTask::Visit(left));
                        }
                        FloatCondition::Classification { value, .. } => {
                            tasks.push(AtomicCanonicalizationTask::Visit(value));
                        }
                    }
                }
                OldConditionTerm::AddressOffsetEqual(left, right) => {
                    tasks.push(AtomicCanonicalizationTask::RebuildAddressOffsetEqual);
                    tasks.push(AtomicCanonicalizationTask::VisitOffset(right));
                    tasks.push(AtomicCanonicalizationTask::VisitOffset(left));
                }
                OldConditionTerm::AddressEqual(left, right) => {
                    tasks.push(AtomicCanonicalizationTask::RebuildAddressEqual {
                        left_block: left.base.clone(),
                        right_block: right.base.clone(),
                    });
                    tasks.push(AtomicCanonicalizationTask::VisitOffset(&right.offset));
                    tasks.push(AtomicCanonicalizationTask::VisitOffset(&left.offset));
                }
                condition => {
                    let (op, left, right) = condition
                        .as_bitvector_comparison()
                        .expect("every other condition has its own arm");
                    tasks.push(AtomicCanonicalizationTask::RebuildConditionBinary(op));
                    tasks.push(AtomicCanonicalizationTask::Visit(right));
                    tasks.push(AtomicCanonicalizationTask::Visit(left));
                }
            },
            AtomicCanonicalizationTask::VisitOffset(offset) => match offset.view() {
                OffsetView::Constant(_) | OffsetView::Variable(_) => {
                    offset_results.push(offset.clone())
                }
                OffsetView::Add(left, right) => {
                    tasks.push(AtomicCanonicalizationTask::RebuildOffsetAdd);
                    tasks.push(AtomicCanonicalizationTask::VisitOffset(right));
                    tasks.push(AtomicCanonicalizationTask::VisitOffset(left));
                }
                OffsetView::Int32Scaled { index, .. } | OffsetView::Int64Scaled { index, .. }
                    if index.shared_operand().is_some() =>
                {
                    // A shared index retains its chosen read states. Its
                    // stored values are comparison evidence, not address syntax.
                    offset_results.push(offset.clone());
                }
                // The view owns the index, so its written operand is
                // canonicalized by a nested walk, at the point the operand's
                // task would be popped.
                OffsetView::Int32Scaled { index, byte_width } => {
                    let value = canonicalize_atomic_loads_deep(
                        index
                            .retained_written_operand()
                            .expect("shared indices handled above"),
                    );
                    offset_results.push(AddressOffset::scale_int32(value, byte_width));
                }
                OffsetView::Int64Scaled {
                    index,
                    byte_width,
                    unsigned,
                } => {
                    let value = canonicalize_atomic_loads_deep(
                        index
                            .retained_written_operand()
                            .expect("shared indices handled above"),
                    );
                    offset_results.push(AddressOffset::scale_int64(value, byte_width, unsigned));
                }
            },
            // Integer operators and conversions are rebuilt as bare nodes;
            // float operators and the machine cast through their smart
            // constructors.
            AtomicCanonicalizationTask::RebuildBinary(op) => {
                let right = results.pop().expect("visited right term");
                let left = results.pop().expect("visited left term");
                results.push(if op.is_float() {
                    op.build(left, right)
                } else {
                    op.build_raw(left, right)
                });
            }
            AtomicCanonicalizationTask::RebuildUnary(op) => {
                let value = results.pop().expect("visited unary term");
                let smart = op.is_float()
                    || matches!(
                        op,
                        BitvectorUnaryOp::Cast {
                            spelling: MachineCastSpelling::Generic,
                            ..
                        }
                    );
                results.push(if smart {
                    op.build(value)
                } else {
                    op.build_raw(value)
                });
            }
            AtomicCanonicalizationTask::RebuildConditionBinary(op) => {
                let right = results.pop().expect("visited right condition operand");
                let left = results.pop().expect("visited left condition operand");
                condition_results.push(op.build_raw(left, right));
            }
            AtomicCanonicalizationTask::RebuildFloatCondition {
                is_float64,
                condition,
                term_count,
            } => {
                let first = results.len() - term_count;
                let mut index = first;
                let rebuilt = condition.map_bitvector_terms(|_| {
                    let term = results[index].clone();
                    index += 1;
                    term
                });
                results.truncate(first);
                condition_results.push(if is_float64 {
                    OldConditionTerm::Float64(rebuilt)
                } else {
                    OldConditionTerm::Float32(rebuilt)
                });
            }
            AtomicCanonicalizationTask::RebuildAddressOffsetEqual => {
                let right = offset_results.pop().expect("visited right pointer offset");
                let left = offset_results.pop().expect("visited left pointer offset");
                condition_results.push(OldConditionTerm::AddressOffsetEqual(
                    Box::new(left),
                    Box::new(right),
                ));
            }
            AtomicCanonicalizationTask::RebuildAddressEqual {
                left_block,
                right_block,
            } => {
                let right = offset_results.pop().expect("visited right pointer offset");
                let left = offset_results.pop().expect("visited left pointer offset");
                condition_results.push(OldConditionTerm::AddressEqual(
                    Box::new(Address::new(left_block, left)),
                    Box::new(Address::new(right_block, right)),
                ));
            }
            AtomicCanonicalizationTask::RebuildOffsetAdd => {
                let right = offset_results.pop().expect("visited right pointer offset");
                let left = offset_results.pop().expect("visited left pointer offset");
                offset_results.push(AddressOffset::add(left, right));
            }
            AtomicCanonicalizationTask::RebuildIf => {
                let else_term = results.pop().expect("visited else term");
                let then_term = results.pop().expect("visited then term");
                let condition = condition_results.pop().expect("visited condition");
                results.push(OldMachineTerm::If {
                    condition: Box::new(condition),
                    then_term: Box::new(then_term),
                    else_term: Box::new(else_term),
                });
            }
            AtomicCanonicalizationTask::RebuildRangeFold { accumulator, item } => {
                let body = results.pop().expect("visited fold body");
                let initial = results.pop().expect("visited fold initial value");
                let end = results.pop().expect("visited fold end");
                let start = results.pop().expect("visited fold start");
                results.push(OldMachineTerm::RangeFold {
                    start: Box::new(start),
                    end: Box::new(end),
                    initial: Box::new(initial),
                    accumulator,
                    item,
                    body: Box::new(body),
                });
            }
            AtomicCanonicalizationTask::RebuildPureFunction {
                name,
                argument_count,
            } => {
                let first = results.len() - argument_count;
                let arguments = results.split_off(first);
                results.push(OldMachineTerm::rebuild_pure_application(name, arguments));
            }
        }
    }
    assert_eq!(results.len(), 1, "canonicalization produces one term");
    assert!(condition_results.is_empty());
    assert!(offset_results.is_empty());
    results.pop().unwrap()
}

/// Canonicalizes legacy offset operands while retaining shared index children.
pub(super) fn canonicalize_pointer_loads(pointer: &Address) -> Address {
    enum OffsetTask<'a> {
        Visit(&'a AddressOffset),
        RebuildAdd,
    }
    let mut tasks = vec![OffsetTask::Visit(&pointer.offset)];
    let mut results = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            OffsetTask::Visit(offset) => match offset.view() {
                OffsetView::Constant(_) | OffsetView::Variable(_) => results.push(offset.clone()),
                OffsetView::Add(left, right) => {
                    tasks.push(OffsetTask::RebuildAdd);
                    tasks.push(OffsetTask::Visit(right));
                    tasks.push(OffsetTask::Visit(left));
                }
                OffsetView::Int32Scaled { index, .. } | OffsetView::Int64Scaled { index, .. }
                    if index.shared_operand().is_some() =>
                {
                    // A shared index retains its chosen read states. Its
                    // stored values are comparison evidence, not address syntax.
                    results.push(offset.clone());
                }
                OffsetView::Int32Scaled { index, byte_width } => {
                    results.push(AddressOffset::scale_int32(
                        canonicalize_atomic_loads_deep(
                            index
                                .retained_written_operand()
                                .expect("shared indices handled above"),
                        ),
                        byte_width,
                    ));
                }
                OffsetView::Int64Scaled {
                    index,
                    byte_width,
                    unsigned,
                } => results.push(AddressOffset::scale_int64(
                    canonicalize_atomic_loads_deep(
                        index
                            .retained_written_operand()
                            .expect("shared indices handled above"),
                    ),
                    byte_width,
                    unsigned,
                )),
            },
            OffsetTask::RebuildAdd => {
                let right = results.pop().expect("visited right offset");
                let left = results.pop().expect("visited left offset");
                results.push(AddressOffset::add(left, right));
            }
        }
    }
    pointer.with_offset(results.pop().expect("canonicalization produces one offset"))
}

/// Compares two condition facts operandwise under memory-resolution
/// equality, so forms that differ only in provably-irrelevant cached
/// cells compare equal.
pub(crate) fn program_condition_facts_equivalent_for_memory_resolution(
    left: &Proposition,
    right: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    let (Proposition::ConditionIs(left, left_value), Proposition::ConditionIs(right, right_value)) =
        (left, right)
    else {
        return false;
    };
    if left_value != right_value {
        return false;
    }
    let operands = match (left.old_form(), right.old_form()) {
        (
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            },
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: c,
                right: d,
            },
        )
        | (
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            },
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: c,
                right: d,
            },
        )
        | (
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            },
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: c,
                right: d,
            },
        )
        | (
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            },
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: c,
                right: d,
            },
        )
        | (
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left: a,
                right: b,
            },
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left: c,
                right: d,
            },
        ) => Some((a, b, c, d)),
        _ => None,
    };
    let Some((a, b, c, d)) = operands else {
        return false;
    };
    int32_values_proven_equal_for_memory_resolution(a, c, assumptions)
        && int32_values_proven_equal_for_memory_resolution(b, d, assumptions)
}

#[cfg(test)]
mod condition_fact_graph_equivalence_tests {
    use super::*;

    fn var(id: u64) -> OldMachineTerm {
        OldMachineTerm::Variable(Variable(id))
    }

    fn less_than(left: OldMachineTerm, right: OldMachineTerm) -> Proposition {
        Proposition::condition_is(OldConditionTerm::signed_less_than(left, right), true)
    }

    #[test]
    fn condition_fact_operands_use_graph_with_state_scope() {
        let _session = crate::kernel::VerificationSession::enter();
        let before =
            crate::kernel::intern_memory(SymbolicMemory::new().with_block("fact-graph", 8));
        let pointer =
            |index| Address::new("fact-graph".into(), AddressOffset::scale_int32(index, 4));
        let load = |memory: &SharedMemory, index| {
            OldMachineTerm::Variable(crate::kernel::load_variable_for_cell_with_origin(
                memory,
                &pointer(index),
                crate::kernel::LoadKind::Int32,
                4,
                memory,
            ))
        };
        let (a, b) = (var(91), var(92));
        let after = crate::kernel::intern_memory(before.memory().clone().store(
            pointer(b.clone()),
            ProgramValue::Int32(OldMachineTerm::constant(9)),
        ));
        let sum = |value| OldMachineTerm::add(value, OldMachineTerm::constant(1));
        let source = less_than(sum(load(&before, a.clone())), var(93));
        let target = less_than(sum(load(&before, b.clone())), var(93));
        let later = less_than(sum(load(&after, b.clone())), var(93));
        let premise = OldConditionTerm::equal(a, b.clone());
        let parent = PureFactContext::new();
        let branch = parent.clone().assume_condition(premise.clone(), true);
        let _scope = branch.enter_id_scope();

        PureFactContext::reset_bitvector_equality_index_fact_visits();
        assert!(program_condition_facts_equivalent_for_memory_resolution(
            &source, &target, &branch,
        ));
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(!program_condition_facts_equivalent_for_memory_resolution(
            &source, &later, &branch,
        ));
        assert!(!program_condition_facts_equivalent_for_memory_resolution(
            &source, &target, &parent,
        ));
        let false_target = Proposition::condition_is(
            OldConditionTerm::signed_less_than(sum(load(&before, b.clone())), var(93)),
            false,
        );
        assert!(!program_condition_facts_equivalent_for_memory_resolution(
            &source,
            &false_target,
            &branch,
        ));
        let equal_target = Proposition::condition_is(
            OldConditionTerm::equal(sum(load(&before, b.clone())), var(93)),
            true,
        );
        assert!(!program_condition_facts_equivalent_for_memory_resolution(
            &source,
            &equal_target,
            &branch,
        ));
        let right_premise = OldConditionTerm::equal(var(93), var(94));
        let both = branch.clone().assume_condition(right_premise, true);
        let target_right = less_than(sum(load(&before, b.clone())), var(94));
        assert!(program_condition_facts_equivalent_for_memory_resolution(
            &source,
            &target_right,
            &both,
        ));
        let equal_source = Proposition::condition_is(
            OldConditionTerm::equal(sum(load(&before, var(91))), var(93)),
            true,
        );
        let equal_target = Proposition::condition_is(
            OldConditionTerm::equal(sum(load(&before, b)), var(94)),
            true,
        );
        assert!(program_condition_facts_equivalent_for_memory_resolution(
            &equal_source,
            &equal_target,
            &both,
        ));
        assert!(!program_condition_facts_equivalent_for_memory_resolution(
            &source,
            &target_right,
            &branch,
        ));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../scaling_tests/kernel/memory_history/condition_fact_graph_equivalence_tests.rs"
        );
    }
}

/// Exports each certified store as the condition fact its record proves:
/// loading the stored pointer from the post-store memory yields the stored
/// value. These are execution-certified equations usable by check.
pub(crate) fn certified_store_equations(
    facts: &(impl ExecutionFactSource + ?Sized),
) -> Vec<Proposition> {
    facts
        .fact_iter()
        .filter_map(|fact| {
            fact.certified_store_equation()
                .map(|equation| equation.as_ref().clone())
        })
        .collect()
}

/// Construct the value equation from this one store's operands at admission.
/// Later consumers reuse the retained equation instead of naming its read again.
#[cfg(test)]
pub(super) fn store_value_equation(
    after: &SymbolicMemory,
    pointer: &Address,
    value: &ProgramValue,
) -> Option<Proposition> {
    store_value_equation_at(&ProgramPoint::of_memory(after), pointer, value)
}

pub(super) fn store_value_equation_at(
    after: &ProgramPoint,
    pointer: &Address,
    value: &ProgramValue,
) -> Option<Proposition> {
    if let ProgramValue::Pointer(value) = value
        && matches!(value.program_type(), ProgramType::FunctionPointer(_))
    {
        // The producer knows this exact store's value. Retain its read equation;
        // registration relates aliases by congruence, without looking in cells.
        let read = Pointer::new(
            Address::loaded_value_at(after, pointer),
            value.program_type(),
        );
        return Some(Proposition::condition_is(
            OldConditionTerm::pointer_equal(read, value.clone()),
            true,
        ));
    }
    let stored_bits = match value.numeric_value() {
        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
        ProgramValue::Int8(term) => term.clone(),
        ProgramValue::Bool(term)
        | ProgramValue::Int16(term)
        | ProgramValue::Int32(term)
        | ProgramValue::UInt8(term)
        | ProgramValue::UInt16(term)
        | ProgramValue::UInt32(term)
        | ProgramValue::Int64(term)
        | ProgramValue::UInt64(term)
        | ProgramValue::Int128(term)
        | ProgramValue::UInt128(term) => term.clone(),
        ProgramValue::Void
        | ProgramValue::Pointer(_)
        | ProgramValue::Parameter(_)
        | ProgramValue::Float32(_)
        | ProgramValue::Float64(_) => {
            return None;
        }
    };
    // What the store wrote is the read of its own kind there,
    // equated at the stored value's format. Bool uses its byte carrier.
    let kind = LoadKind::of_value(value)?;
    // The store wrote a four-byte word, so the read naming it is a
    // four-byte access. A word read without a recorded width is named
    // under the eight-byte fallback, which the equality graph does
    // not register as a word read, and a later typed read of the same
    // cell names it under another width than this equation does.
    // Record the width before naming the read, as a typed load
    // producer does. Every other kind's fallback is its own width.
    if kind.is_word32() {
        crate::kernel::eval::record_load_access_width(after.memory(), pointer, value.byte_width());
    }
    // For an indexed store, publish the same typed read that ordinary
    // lowering selects at the written point.
    let read = if let Some(version) = after.indexed_integer_version(pointer, kind)
        && version.read_version_id() == after.id()
    {
        crate::kernel::eval::scalar_read_for_exact_cell_at(
            &version,
            pointer,
            kind,
            value.byte_width(),
        )
    } else {
        crate::kernel::eval::canonical_form_of_load_at(after, pointer.clone(), kind)
    };
    let format = match value.numeric_value() {
        ProgramValue::Bool(_) => MachineIntegerType::UInt8,
        value => MachineIntegerType::from_program_type(value.program_type())?,
    };
    // Use the language comparison constructor as well as its width:
    // 64/128-bit equality has one sign-free, signed-format spelling.
    let condition =
        OldConditionTerm::machine_compare(format, CompareRelation::Equal, read, stored_bits);
    Some(Proposition::condition_is(condition, true))
}

pub(crate) fn certified_store_loadability_facts(
    facts: &(impl ExecutionFactSource + ?Sized),
) -> Vec<Proposition> {
    facts
        .fact_iter()
        .filter_map(|fact| {
            let store = fact.certified_store_data()?;
            // The store materializes one cell of the value's own width; a
            // pointer is `C_POINTER_BYTE_WIDTH` bytes, not four.
            let byte_width = match &store.value {
                ProgramValue::Void => return None,
                value => value.byte_width(),
            };
            Some(Proposition::MemoryLoadable {
                memory: store.after.clone(),
                point: store.after_point.path_link().clone(),
                base: store.pointer.clone(),
                bytes: (OldMachineTerm::constant(byte_width)).into(),
                wide: false,
            })
        })
        .collect()
}

#[cfg(test)]
pub(crate) fn program_condition_fact_memories(fact: &Proposition) -> Vec<SymbolicMemory> {
    let Proposition::ConditionIs(condition, _) = fact else {
        return Vec::new();
    };
    let mut memories = Vec::new();
    collect_condition_memories(condition.old_form(), &mut memories);
    memories
        .into_iter()
        .map(|memory| memory.as_ref().clone())
        .collect()
}

fn collect_condition_operand_memories(
    condition: crate::kernel::BooleanOperandView<'_>,
    memories: &mut Vec<SharedMemory>,
) {
    condition.for_each_dependency_leaf(|leaf| {
        if let crate::kernel::BooleanOperandView::Shared(root) = leaf
            && matches!(
                root.node(),
                crate::kernel::KernelTermNode::BoolLiteral(_)
                    | crate::kernel::KernelTermNode::Variable(_)
                    | crate::kernel::KernelTermNode::Call { .. }
            )
        {
            return;
        }

        if let Some((_, operands)) = leaf.machine_arguments() {
            let mut seen = BTreeSet::new();
            for operand in operands {
                collect_operand_memories(operand, memories, &mut seen);
            }
        } else if let Some(values) = leaf.pointer_values() {
            for value in &values {
                for address in value.addresses() {
                    if let AddressBase::PureFunctionApplication(call) = address.atom()
                        && let Some(bits) = call.integer_address_bits()
                    {
                        collect_bitvector_memories(bits, memories);
                    }
                    let mut seen = BTreeSet::new();
                    address.offset().visit_root_in_order(false, |node| {
                        if let Some(index) = node.index() {
                            collect_operand_memories(
                                crate::kernel::MachineOperandView::Shared(index),
                                memories,
                                &mut seen,
                            );
                        }
                    });
                }
            }
            let mut seen = BTreeSet::new();
            for count in values.iter().filter_map(|value| value.len()) {
                collect_operand_memories(
                    crate::kernel::MachineOperandView::Shared(count),
                    memories,
                    &mut seen,
                );
            }
        } else if let Some(addresses) = leaf.pointer_addresses() {
            for address in addresses {
                collect_equality_address_base_memories(address.atom(), memories);
                let mut seen = BTreeSet::new();
                address.offset().visit_root_in_order(false, |node| {
                    if let Some(index) = node.index() {
                        collect_operand_memories(
                            crate::kernel::MachineOperandView::Shared(index),
                            memories,
                            &mut seen,
                        );
                    }
                });
            }
        } else if let Some(offsets) = leaf.pointer_offsets() {
            let mut seen = BTreeSet::new();
            crate::kernel::SharedAddressOffset::visit_pair(&offsets, |node| {
                if let Some(index) = node.index() {
                    collect_operand_memories(
                        crate::kernel::MachineOperandView::Shared(index),
                        memories,
                        &mut seen,
                    );
                }
            });
        } else {
            // In particular preserve the structural classifier's restricted
            // Integer-comparison admission; do not turn this into a new rule.
            collect_condition_memories(&leaf.native(), memories);
        }
    });
}

fn collect_condition_memories(condition: &OldConditionTerm, memories: &mut Vec<SharedMemory>) {
    let mut collect_binary = |left: &OldMachineTerm, right: &OldMachineTerm| {
        collect_bitvector_memories(left, memories);
        collect_bitvector_memories(right, memories);
    };
    match condition {
        OldConditionTerm::PointerEqual(left, right) => {
            for pointer in left.pointers().chain(right.pointers()) {
                if let AddressBase::PureFunctionApplication(application) = &pointer.base
                    && let Some(bits) = application.integer_address_bits()
                {
                    collect_bitvector_memories(bits, memories);
                }
                collect_pointer_offset_memories(&pointer.offset, memories);
            }
            for count in left.metadata_terms().chain(right.metadata_terms()) {
                collect_bitvector_memories(count, memories);
            }
        }

        OldConditionTerm::AlgebraicEqual(left, right) => {
            let mut seen = BTreeSet::new();
            left.for_each_machine_operand(|view| {
                collect_operand_memories(view, memories, &mut seen)
            });
            right.for_each_machine_operand(|view| {
                collect_operand_memories(view, memories, &mut seen)
            });
        }
        crate::kernel::binary_bitvector_condition!(left, right) => collect_binary(left, right),
        OldConditionTerm::Float32(float_condition) | OldConditionTerm::Float64(float_condition) => {
            float_condition
                .for_each_bitvector_term(|term| collect_bitvector_memories(term, memories));
        }
        OldConditionTerm::AddressOffsetEqual(left, right) => {
            collect_pointer_offset_memories(left, memories);
            collect_pointer_offset_memories(right, memories);
        }
        OldConditionTerm::AddressEqual(left, right) => {
            for pointer in [left, right] {
                collect_equality_address_base_memories(&pointer.base, memories);
                collect_pointer_offset_memories(&pointer.offset, memories);
            }
        }
        crate::kernel::integer_comparison_condition!(_, _) => {
            if let Some(view) =
                crate::kernel::machine_integer::comparison::structural_comparison_view(condition)
            {
                let mut seen = BTreeSet::new();
                for operand in &view.operands {
                    collect_operand_memories(operand.operand_view(), memories, &mut seen);
                }
            }
        }
        OldConditionTerm::Constant(_) | OldConditionTerm::Variable(_) => {}
        // As a word-valued Click application.
        OldConditionTerm::BoolApplication(_) => {}
        OldConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => {
            for condition in [condition, then_condition, else_condition] {
                collect_condition_memories(condition, memories);
            }
        }
        OldConditionTerm::BoolEqual(left, right) => {
            collect_condition_memories(left, memories);
            collect_condition_memories(right, memories);
        }
    }
}

fn collect_equality_address_base_memories(block: &AddressBase, memories: &mut Vec<SharedMemory>) {
    if let AddressBase::PureFunctionApplication(application) = block
        && let Some(bits) = application.integer_address_bits()
    {
        collect_bitvector_memories(bits, memories);
    }
    if let AddressBase::Symbolic(variable) = block
        && let Some((origin, _)) =
            crate::kernel::eval::registered_load_origin_for_variable(variable)
        && !memories.contains(&origin)
    {
        memories.push(origin);
    }
}

fn collect_pointer_offset_memories(offset: &AddressOffset, memories: &mut Vec<SharedMemory>) {
    let mut seen = BTreeSet::new();
    offset.for_each_scaled_operand(|value| {
        collect_operand_memories(value.operand_view(), memories, &mut seen)
    });
}

fn collect_operand_memories(
    view: crate::kernel::MachineOperandView<'_>,
    memories: &mut Vec<SharedMemory>,
    seen: &mut BTreeSet<u64>,
) {
    use crate::kernel::MachineOperandView as V;
    // These memories are search candidates: retain the native walk's first
    // occurrence order, while visiting shared arithmetic nodes only once.
    {
        let mut pending = vec![view];
        while let Some(operand) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let V::Shared(root) = operand else {
                let V::Old(term) = operand else {
                    unreachable!()
                };
                collect_bitvector_memories(term, memories);
                continue;
            };
            if !seen.insert(root.id()) {
                continue;
            }
            if let crate::kernel::KernelTermNode::Match(matched) = root.node() {
                pending.extend(matched.arguments[1..].iter().rev().map(V::Shared));
            } else if let Some((_, _, children)) = operand.fold() {
                pending.extend(children.into_iter().rev());
            } else if let Some(leaf) = root.machine_conversion_leaf() {
                collect_bitvector_memories(leaf, memories);
            } else if let Some((memory, _, _)) = operand.read() {
                if !memories.contains(memory) {
                    memories.push(memory.clone());
                }
            } else if let Some((condition, [left, right])) = operand.conditional_view() {
                collect_condition_operand_memories(condition, memories);
                pending.push(right);
                pending.push(left);
            } else if let Some((_, _, [left, right])) = operand.binary() {
                pending.push(right);
                pending.push(left);
            } else if let Some((_, _, child)) = operand.unary() {
                pending.push(child);
            } else if let Some((_, _, _, child)) = operand.cast() {
                pending.push(child);
            }
        }
    }
}

fn collect_bitvector_memories(term: &OldMachineTerm, memories: &mut Vec<SharedMemory>) {
    match term {
        OldMachineTerm::ThreadHandle(_) => {}
        OldMachineTerm::Constant { .. } | OldMachineTerm::Variable(_) => {}
        OldMachineTerm::IntegerAddress(_, _) => {}
        OldMachineTerm::MemoryLoad(memory, _, _) => {
            if !memories.contains(memory.shared_memory()) {
                memories.push(memory.shared_memory().clone());
            }
        }
        OldMachineTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_memories(condition, memories);
            collect_bitvector_memories(then_term, memories);
            collect_bitvector_memories(else_term, memories);
        }
        OldMachineTerm::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_bitvector_memories(start, memories);
            collect_bitvector_memories(end, memories);
            collect_bitvector_memories(initial, memories);
            collect_bitvector_memories(body, memories);
        }
        OldMachineTerm::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_memories(argument, memories);
            }
        }
        OldMachineTerm::ClickFunctionApplication { .. }
        | OldMachineTerm::PureApplicationCount(_) => {}
        OldMachineTerm::IntegerToMachine { .. } => {}
        OldMachineTerm::BoolCast { value, .. } => collect_condition_memories(value, memories),
        OldMachineTerm::AlgebraicMatch { arms, .. } => {
            for arm in arms {
                collect_bitvector_memories(&arm.body, memories);
            }
        }
        term => {
            if let Some((_, left, right)) = term.as_binary() {
                collect_bitvector_memories(left, memories);
                collect_bitvector_memories(right, memories);
            } else {
                let (_, value) = term
                    .as_unary()
                    .expect("every other term is binary or unary");
                collect_bitvector_memories(value, memories);
            }
        }
    }
}

/// Retained Boolean transport preserves the native authority and refusal rules.
/// Ineligible common roots are declined before any expression export. Selected
/// primitive comparisons retain their operands and use the shared equivalent
/// of native constructors. Other admitted families keep their selected native
/// compatibility reader.
pub(in crate::kernel) fn transport_framed_common_condition(
    condition: &crate::kernel::KernelTerm,
    after: &ProgramPoint,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<crate::kernel::KernelTerm> {
    use crate::kernel::KernelTermNode as Node;
    if crate::kernel::assumptions::reasoning_interrupted() {
        return None;
    }
    match condition.node() {
        Node::BoolLiteral(_)
        | Node::Variable(_)
        | Node::BoolIf { .. }
        | Node::BoolEqual { .. }
        | Node::Call { .. } => None,
        Node::PointerEqual(pair) => {
            let [a, b] = pair.arguments();
            let mapped = crate::kernel::KernelTerm::pointer_equal_raw([
                shared_pointer_transport::transport_pointer(a, after, assumptions)?,
                shared_pointer_transport::transport_pointer(b, after, assumptions)?,
            ]);
            Some(
                if crate::kernel::BooleanOperandView::Shared(condition)
                    .syntax_equal(crate::kernel::BooleanOperandView::Shared(&mapped))
                {
                    condition.clone()
                } else {
                    mapped
                },
            )
        }
        Node::AddressEqual { arguments, .. } => Some(crate::kernel::KernelTerm::address_equal(
            shared_pointer_transport::transport_addresses(arguments, after, assumptions)?,
        )),
        Node::AddressOffsetEqual { arguments } => {
            Some(crate::kernel::KernelTerm::address_offset_equal(
                shared_pointer_transport::transport_offsets(arguments, after, assumptions)?,
            ))
        }
        Node::BoolCompare {
            format, arguments, ..
        }
        | Node::BoolOverflow {
            format, arguments, ..
        } => {
            let mut mapped = Vec::with_capacity(2);
            for argument in arguments {
                let value = crate::kernel::MachineOperandView::Shared(argument).retain(*format);
                let value = transport_framed_index(&value, after, assumptions)?;
                mapped.push(crate::kernel::KernelTerm::retained_machine_operand(
                    *format,
                    value.operand_view(),
                ));
            }
            let arguments = [mapped[0].clone(), mapped[1].clone()];
            let mapped = match condition.node() {
                Node::BoolCompare { relation, .. } => {
                    crate::kernel::KernelTerm::boolean_comparison(*format, *relation, arguments)
                }
                Node::BoolOverflow { operation, .. } => {
                    crate::kernel::KernelTerm::boolean_overflow(*format, *operation, arguments)
                }
                _ => unreachable!(),
            };
            Some(
                if crate::kernel::BooleanOperandView::Shared(condition)
                    .syntax_equal(crate::kernel::BooleanOperandView::Shared(&mapped))
                {
                    condition.clone()
                } else {
                    mapped
                },
            )
        }
        _ => {
            let native = crate::kernel::BooleanOperandView::Shared(condition).native();
            let mapped = transport_framed_atomic_condition(&native, after, assumptions)?;
            Some(if mapped == *native {
                // Match the existing index mapper's unchanged-guard rule.
                condition.clone()
            } else {
                crate::kernel::KernelTermImport::default().condition(&mapped)
            })
        }
    }
}

fn transport_framed_atomic_condition(
    condition: &OldConditionTerm,
    after: &ProgramPoint,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<OldConditionTerm> {
    if crate::kernel::assumptions::reasoning_interrupted() {
        return None;
    }
    if matches!(
        condition,
        crate::kernel::integer_comparison_condition!(_, _)
    ) {
        use crate::kernel::machine_integer::comparison::{
            condition_for_operand_views, structural_comparison_view,
        };
        let view = structural_comparison_view(condition)?;
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view().retain(view.format));
        let left = transport_framed_index(&left, after, assumptions)?;
        let right = transport_framed_index(&right, after, assumptions)?;
        return Some(if view.negated {
            OldConditionTerm::integer_not_equal(
                IntegerTerm::Machine(left),
                IntegerTerm::Machine(right),
            )
        } else {
            condition_for_operand_views(
                view.format,
                view.relation,
                [left.operand_view(), right.operand_view()],
            )
        });
    }
    Some(match condition {
        // Do not claim a state bridge through an opaque algebraic value.
        OldConditionTerm::PointerEqual(left, right) => OldConditionTerm::PointerEqual(
            Box::new(transport_framed_atomic_pointer_value(
                left,
                after,
                assumptions,
            )?),
            Box::new(transport_framed_atomic_pointer_value(
                right,
                after,
                assumptions,
            )?),
        ),
        OldConditionTerm::AlgebraicEqual(_, _) => return None,
        OldConditionTerm::Float32(float_condition) => {
            OldConditionTerm::Float32(float_condition.try_map_bitvector_terms(|term| {
                transport_framed_atomic_bitvector(term, after, assumptions)
            })?)
        }
        OldConditionTerm::Float64(float_condition) => {
            OldConditionTerm::Float64(float_condition.try_map_bitvector_terms(|term| {
                transport_framed_atomic_bitvector(term, after, assumptions)
            })?)
        }
        OldConditionTerm::AddressOffsetEqual(left, right) => {
            OldConditionTerm::address_offset_equal(
                transport_framed_atomic_pointer_offset(left, after, assumptions)?,
                transport_framed_atomic_pointer_offset(right, after, assumptions)?,
            )
        }
        OldConditionTerm::AddressEqual(left, right) => OldConditionTerm::address_equal(
            transport_framed_atomic_pointer(left, after, assumptions)?,
            transport_framed_atomic_pointer(right, after, assumptions)?,
        ),
        OldConditionTerm::Constant(_) | OldConditionTerm::Variable(_) => return None,
        // Machine observations were handled above. Other mathematical integer
        // forms are outside this memory transport path.
        crate::kernel::integer_comparison_condition!(_, _) => return None,
        // Nor does it for `Bool` values yet: they are not transported.
        condition if condition.is_bool_value_form() => return None,
        condition => {
            let (op, left, right) = condition
                .as_bitvector_comparison()
                .expect("every other condition has its own arm");
            op.build(
                transport_framed_atomic_bitvector(left, after, assumptions)?,
                transport_framed_atomic_bitvector(right, after, assumptions)?,
            )
        }
    })
}

fn transport_framed_atomic_pointer_value(
    value: &Pointer,
    after: &ProgramPoint,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<Pointer> {
    // Only reconstructed complete words need their read provenance moved
    // alongside their numeric address. Ordinary pointers keep their origin.
    let reconstructed_word = value.address().integer_address_bits().is_some();
    value.try_map_pointers(
        |pointer| {
            if reconstructed_word && let Some(read) = pointer.as_loaded_value() {
                // The supplied endpoint names this observation. Check its one
                // immediate frame; discovering an older version would be a hidden
                // history search even if a previous query happened to cache it.
                let after = after.shared_memory().clone();
                let mut target = Address::loaded_value(&after, &read.defining_address);
                target.set_offset(pointer.offset.clone());
                return assumptions
                    .is_some_and(|(context, _)| {
                        complete_pointer_reads_equal_across_frame(pointer, &target, context)
                    })
                    .then_some(target);
            }
            transport_framed_atomic_pointer(pointer, after, assumptions)
        },
        // A wide pointer's count is a numeric child, transported as the
        // loads in an offset are: a count read across the same checked frame
        // (`design/rust-slice-values.md`, step 2b-ii-b). A slice read's data
        // pointer keeps its load, as a pointer read's base does.
        |count| transport_framed_atomic_bitvector(count, after, assumptions),
    )
}

fn transport_framed_atomic_pointer(
    pointer: &Address,
    after: &ProgramPoint,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<Address> {
    let block = if let AddressBase::Symbolic(variable) = &pointer.base {
        // An opaque pointer-typed read puts its load identity in the block,
        // rather than in an offset within the storage object's provenance.
        // Transport that identity using the same checked load-frame rule as
        // scalar load variables. Ordinary symbolic pointers have no producer
        // metadata and stay unchanged.
        match transport_framed_atomic_bitvector(
            &OldMachineTerm::Variable(*variable),
            after,
            assumptions,
        )? {
            OldMachineTerm::Variable(variable) => AddressBase::Symbolic(variable),
            _ => return None,
        }
    } else if let AddressBase::PureFunctionApplication(application) = &pointer.base
        && let Some(bits) = application.integer_address_bits()
    {
        // Numeric pointer reconstruction is a pure function of its complete
        // word. Carry loads inside that word across the same checked frame
        // as offset loads; cloning the block would retain the old state.
        Address::from_integer_address(transport_framed_atomic_bitvector(bits, after, assumptions)?)
            .base
            .clone()
    } else {
        pointer.base.clone()
    };
    Some(Address::new(
        block,
        transport_framed_atomic_pointer_offset(&pointer.offset, after, assumptions)?,
    ))
}

fn transport_framed_atomic_pointer_offset(
    offset: &AddressOffset,
    after: &ProgramPoint,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<AddressOffset> {
    if crate::kernel::assumptions::reasoning_interrupted() {
        return None;
    }
    Some(match offset.view() {
        OffsetView::Constant(_) | OffsetView::Variable(_) => offset.clone(),
        OffsetView::Add(left, right) => AddressOffset::add(
            transport_framed_atomic_pointer_offset(left, after, assumptions)?,
            transport_framed_atomic_pointer_offset(right, after, assumptions)?,
        ),
        OffsetView::Int32Scaled { index, byte_width } => transported_scaled_index(
            transport_framed_index(&index, after, assumptions)?,
            byte_width,
            None,
        ),
        OffsetView::Int64Scaled {
            index,
            byte_width,
            unsigned,
        } => transported_scaled_index(
            transport_framed_index(&index, after, assumptions)?,
            byte_width,
            Some(unsigned),
        ),
    })
}

mod shared_index_transport;
// Prepared shared pointer transport; consumers activate after spelling.
#[allow(dead_code)]
mod shared_pointer_transport;
pub(in crate::kernel) use shared_index_transport::{
    index_syntax_equal as pointer_index_syntax_equal, map_index as map_shared_pointer_index,
    map_index_with_descent as map_shared_pointer_index_with_descent,
    map_index_with_fold as map_shared_pointer_index_with_fold,
    map_index_with_fold_and_cache as map_shared_machine_substitution_with_cache,
    transported_scaled_index as rebuild_scaled_pointer_index,
};
use shared_index_transport::{
    normalize_exact_index, transport_framed_index, transported_scaled_index,
};

fn transport_framed_atomic_bitvector(
    term: &OldMachineTerm,
    after: &ProgramPoint,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<OldMachineTerm> {
    if crate::kernel::assumptions::reasoning_interrupted() {
        return None;
    }
    Some(match term {
        OldMachineTerm::ThreadHandle(_) => term.clone(),
        OldMachineTerm::Constant { .. } => term.clone(),
        OldMachineTerm::IntegerAddress(_, _) => term.clone(),
        OldMachineTerm::Variable(variable) => {
            // A load variable transports as the load it represents:
            // when frame evidence rewrites that load to the post-effect
            // state, the fact is rewritten with the post-point load
            // variable. Content-addressed construction gives the same variable
            // to any later lowering at that state. A defining equation
            // in the ambient assumptions carries the mint-time form,
            // whose live state the frame checks can actually relate to
            // `after`; the registry's canonicalized form is the
            // fallback.
            // The registry's origin is the first live state the variable
            // was minted from: DAG-connected and cell-comparable to `after`,
            // which is what the frame checks below relate.
            let named_load =
                crate::kernel::eval::registered_load_origin_term_for_variable(variable);
            if let Some(load) = named_load {
                let transported = transport_framed_atomic_bitvector(&load, after, assumptions)?;
                if transported != load
                    && let Some((renamed, _)) =
                        crate::kernel::eval::load_variable_for_term(&transported)
                {
                    OldMachineTerm::Variable(renamed)
                } else {
                    term.clone()
                }
            } else {
                term.clone()
            }
        }
        OldMachineTerm::MemoryLoad(memory, pointer, kind) => {
            let transported_pointer = pointer.with_offset(transport_framed_atomic_pointer_offset(
                &pointer.offset,
                after,
                assumptions,
            )?);
            if memories_match_for_pointer_load(memory.memory(), after.memory(), pointer)
                || memory_materializes_atomic_load(after.memory(), memory.memory(), pointer, *kind)
                || assumptions.is_some_and(|(assumptions, direct)| {
                    if direct {
                        memory_load_is_directly_unchanged(
                            memory.memory(),
                            after.memory(),
                            pointer,
                            *kind,
                            assumptions,
                        )
                    } else {
                        let left = crate::kernel::OldMachineTerm::read_named(
                            memory.clone(),
                            pointer.as_ref().clone(),
                            *kind,
                        );
                        let right = crate::kernel::OldMachineTerm::read_named(
                            ProgramPoint::viewing(after.shared_memory(), after),
                            transported_pointer.clone(),
                            *kind,
                        );
                        checked_atomic_load_equality(&left, &right, assumptions)
                    }
                })
            {
                crate::kernel::OldMachineTerm::read_named(
                    ProgramPoint::viewing(after.shared_memory(), after),
                    transported_pointer,
                    *kind,
                )
            } else {
                term.clone()
            }
        }
        OldMachineTerm::If {
            condition,
            then_term,
            else_term,
        } => OldMachineTerm::If {
            condition: Box::new(transport_framed_atomic_condition(
                condition,
                after,
                assumptions,
            )?),
            then_term: Box::new(transport_framed_atomic_bitvector(
                then_term,
                after,
                assumptions,
            )?),
            else_term: Box::new(transport_framed_atomic_bitvector(
                else_term,
                after,
                assumptions,
            )?),
        },
        OldMachineTerm::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => OldMachineTerm::RangeFold {
            start: Box::new(transport_framed_atomic_bitvector(
                start,
                after,
                assumptions,
            )?),
            end: Box::new(transport_framed_atomic_bitvector(end, after, assumptions)?),
            initial: Box::new(transport_framed_atomic_bitvector(
                initial,
                after,
                assumptions,
            )?),
            accumulator: *accumulator,
            item: *item,
            body: Box::new(transport_framed_atomic_bitvector(body, after, assumptions)?),
        },
        OldMachineTerm::PureFunctionApplication { name, arguments } => {
            OldMachineTerm::rebuild_pure_application(
                name.clone(),
                arguments
                    .iter()
                    .map(|argument| transport_framed_atomic_bitvector(argument, after, assumptions))
                    .collect::<Option<Vec<_>>>()?,
            )
        }
        OldMachineTerm::BoolCast { to, value } => OldMachineTerm::BoolCast {
            to: *to,
            value: Box::new(transport_framed_atomic_condition(
                value,
                after,
                assumptions,
            )?),
        },
        OldMachineTerm::ClickFunctionApplication { .. }
        | OldMachineTerm::PureApplicationCount(_)
        | OldMachineTerm::AlgebraicMatch { .. }
        | OldMachineTerm::IntegerToMachine { .. } => term.clone(),
        term => match (term.as_binary(), term.as_unary()) {
            // The 32-bit word operators are rebuilt as bare nodes, the rest
            // through their smart constructors.
            (Some((op, left, right)), _) if op.is_bitvector32() => op.build_raw(
                transport_framed_atomic_bitvector(left, after, assumptions)?,
                transport_framed_atomic_bitvector(right, after, assumptions)?,
            ),
            (Some((op, left, right)), _) => op.build(
                transport_framed_atomic_bitvector(left, after, assumptions)?,
                transport_framed_atomic_bitvector(right, after, assumptions)?,
            ),
            (_, Some((op, value))) if op.is_bitvector32() => op.build_raw(
                transport_framed_atomic_bitvector(value, after, assumptions)?,
            ),
            (_, Some((op, value))) => op.build(transport_framed_atomic_bitvector(
                value,
                after,
                assumptions,
            )?),
            _ => unreachable!("every other variant has its own arm"),
        },
    })
}

pub(crate) fn program_pointer_offsets_proven_equal_for_effect(
    left: &AddressOffset,
    right: &AddressOffset,
    assumptions: &PureFactContext,
) -> bool {
    if crate::kernel::assumptions::reasoning_interrupted() {
        return false;
    }
    let left = normalize_exact_memory_loads_in_pointer_offset(left, assumptions);
    if crate::kernel::assumptions::reasoning_interrupted() {
        return false;
    }
    let right = normalize_exact_memory_loads_in_pointer_offset(right, assumptions);
    if crate::kernel::assumptions::reasoning_interrupted() {
        return false;
    }
    left == right || pointer_offsets_proven_equal_for_memory_resolution(&left, &right, assumptions)
}

pub(super) fn normalize_exact_memory_loads_in_pointer_offset(
    offset: &AddressOffset,
    assumptions: &PureFactContext,
) -> AddressOffset {
    enum Task {
        Visit(AddressOffset),
        RebuildAdd,
    }

    let mut tasks = vec![Task::Visit(offset.clone())];
    let mut results = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(offset) => {
                crate::instrumentation::record_deterministic_work(1);
                if crate::kernel::assumptions::reasoning_interrupted() {
                    results.push(offset);
                    continue;
                }
                let offset = match offset.into_add() {
                    Ok((left, right)) => {
                        tasks.push(Task::RebuildAdd);
                        tasks.push(Task::Visit(right));
                        tasks.push(Task::Visit(left));
                        continue;
                    }
                    Err(offset) => offset,
                };
                let scaled = match offset.view() {
                    OffsetView::Constant(_) | OffsetView::Variable(_) => None,
                    OffsetView::Add(..) => unreachable!("sums are split above"),
                    OffsetView::Int32Scaled { index, byte_width } => {
                        let normalized =
                            normalize_exact_index(&index, assumptions).unwrap_or(index);
                        Some(
                            if let Some(bits) = normalized.operand_view().word32_constant() {
                                AddressOffset::constant((bits as i32 as i64) * byte_width)
                            } else {
                                AddressOffset::int32_scaled(normalized, byte_width)
                            },
                        )
                    }
                    OffsetView::Int64Scaled {
                        index,
                        byte_width,
                        unsigned,
                    } => Some(transported_scaled_index(
                        normalize_exact_index(&index, assumptions).unwrap_or(index),
                        byte_width,
                        Some(unsigned),
                    )),
                };
                results.push(scaled.unwrap_or(offset));
            }
            Task::RebuildAdd => {
                let right = results.pop().expect("visited right pointer offset");
                let left = results.pop().expect("visited left pointer offset");
                results.push(AddressOffset::add(left, right));
            }
        }
    }
    results
        .pop()
        .expect("normalization produces one pointer offset")
}

enum ExactLoadNormalizationTask {
    Visit(OldMachineTerm),
    RebuildBinary(BitvectorBinaryOp),
    RebuildUnary(BitvectorUnaryOp),
    RebuildIf(OldConditionTerm),
    RebuildPureFunction { name: String, argument_count: usize },
    LeaveLoad(OldMachineTerm),
}

fn normalize_exact_memory_loads_in_bitvector_iterative(
    term: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> OldMachineTerm {
    #[allow(clippy::boxed_local)]
    fn push_binary(
        tasks: &mut Vec<ExactLoadNormalizationTask>,
        operator: BitvectorBinaryOp,
        left: Box<OldMachineTerm>,
        right: Box<OldMachineTerm>,
    ) {
        tasks.push(ExactLoadNormalizationTask::RebuildBinary(operator));
        tasks.push(ExactLoadNormalizationTask::Visit(*right));
        tasks.push(ExactLoadNormalizationTask::Visit(*left));
    }

    #[allow(clippy::boxed_local)]
    fn push_unary(
        tasks: &mut Vec<ExactLoadNormalizationTask>,
        operator: BitvectorUnaryOp,
        value: Box<OldMachineTerm>,
    ) {
        tasks.push(ExactLoadNormalizationTask::RebuildUnary(operator));
        tasks.push(ExactLoadNormalizationTask::Visit(*value));
    }

    let mut tasks = vec![ExactLoadNormalizationTask::Visit(term.clone())];
    let mut results = Vec::new();
    let mut active_loads = std::collections::HashSet::new();
    while let Some(task) = tasks.pop() {
        match task {
            ExactLoadNormalizationTask::Visit(term) => {
                crate::instrumentation::record_deterministic_work(1);
                if crate::kernel::assumptions::reasoning_interrupted() {
                    results.push(term);
                    continue;
                }
                match term {
                    OldMachineTerm::ThreadHandle(_) => results.push(term),
                    OldMachineTerm::Cast {
                        spelling: MachineCastSpelling::Generic,
                        value,
                        from: source,
                        to: destination,
                    } => push_unary(
                        &mut tasks,
                        BitvectorUnaryOp::Cast {
                            spelling: MachineCastSpelling::Generic,
                            from: source,
                            to: destination,
                        },
                        value,
                    ),

                    OldMachineTerm::Constant { .. } | OldMachineTerm::Variable(_) => {
                        results.push(term)
                    }
                    OldMachineTerm::Binary {
                        format,
                        op,
                        left,
                        right,
                    } => push_binary(
                        &mut tasks,
                        BitvectorBinaryOp::Machine(format, op),
                        left,
                        right,
                    ),
                    OldMachineTerm::Float32Negate(value) => {
                        push_unary(&mut tasks, BitvectorUnaryOp::Float32Negate, value)
                    }
                    OldMachineTerm::Float64Negate(value) => {
                        push_unary(&mut tasks, BitvectorUnaryOp::Float64Negate, value)
                    }
                    OldMachineTerm::Float32Binary {
                        operator,
                        left,
                        right,
                    } => push_binary(
                        &mut tasks,
                        BitvectorBinaryOp::Float32(operator),
                        left,
                        right,
                    ),
                    OldMachineTerm::Float64Binary {
                        operator,
                        left,
                        right,
                    } => push_binary(
                        &mut tasks,
                        BitvectorBinaryOp::Float64(operator),
                        left,
                        right,
                    ),
                    cast_term!(Int64From32, value) => push_unary(
                        &mut tasks,
                        BitvectorUnaryOp::legacy_cast(MachineCastSpelling::Int64From32),
                        value,
                    ),
                    cast_term!(UInt64From32, value) => push_unary(
                        &mut tasks,
                        BitvectorUnaryOp::legacy_cast(MachineCastSpelling::UInt64From32),
                        value,
                    ),
                    cast_term!(UInt32From64, value) => push_unary(
                        &mut tasks,
                        BitvectorUnaryOp::legacy_cast(MachineCastSpelling::UInt32From64),
                        value,
                    ),
                    cast_term!(Int64FromUInt32, value) => push_unary(
                        &mut tasks,
                        BitvectorUnaryOp::legacy_cast(MachineCastSpelling::Int64FromUInt32),
                        value,
                    ),
                    cast_term!(UInt64FromInt32, value) => push_unary(
                        &mut tasks,
                        BitvectorUnaryOp::legacy_cast(MachineCastSpelling::UInt64FromInt32),
                        value,
                    ),
                    cast_term!(UInt64FromInt64, value) => push_unary(
                        &mut tasks,
                        BitvectorUnaryOp::legacy_cast(MachineCastSpelling::UInt64FromInt64),
                        value,
                    ),
                    OldMachineTerm::Unary {
                        format,
                        op,
                        operand: value,
                    } => push_unary(&mut tasks, BitvectorUnaryOp::Machine(format, op), value),
                    OldMachineTerm::If {
                        condition,
                        then_term,
                        else_term,
                    } => {
                        tasks.push(ExactLoadNormalizationTask::RebuildIf(*condition));
                        tasks.push(ExactLoadNormalizationTask::Visit(*else_term));
                        tasks.push(ExactLoadNormalizationTask::Visit(*then_term));
                    }
                    OldMachineTerm::RangeFold { .. } | OldMachineTerm::BoolCast { .. } => {
                        results.push(term)
                    }
                    OldMachineTerm::PureFunctionApplication { name, arguments } => {
                        let argument_count = arguments.len();
                        tasks.push(ExactLoadNormalizationTask::RebuildPureFunction {
                            name,
                            argument_count,
                        });
                        for argument in arguments.into_iter().rev() {
                            tasks.push(ExactLoadNormalizationTask::Visit(argument));
                        }
                    }
                    OldMachineTerm::ClickFunctionApplication { .. }
                    | OldMachineTerm::PureApplicationCount(_)
                    | OldMachineTerm::AlgebraicMatch { .. }
                    | OldMachineTerm::IntegerToMachine { .. } => results.push(term),
                    OldMachineTerm::IntegerAddress(_, _) => results.push(term),
                    load @ OldMachineTerm::MemoryLoad(_, _, _) => {
                        if !active_loads.insert(load.clone()) {
                            results.push(load);
                            continue;
                        }
                        let OldMachineTerm::MemoryLoad(memory, pointer, kind) = &load else {
                            unreachable!()
                        };
                        // The state's own cell answers only a read of its
                        // kind: an `int32` cell is not a byte read's value.
                        let resolved = match memory
                            .shared_memory()
                            .known_value(pointer)
                            .filter(|_| kind.is_word32())
                            .and_then(|value| kind.read_cell(&value))
                        {
                            Some(ProgramValue::Int32(value) | ProgramValue::UInt32(value))
                                if value != load =>
                            {
                                Some(value)
                            }
                            _ => assumptions.resolve_memory_load_term(&load),
                        };
                        let Some(resolved) = resolved else {
                            active_loads.remove(&load);
                            results.push(load);
                            continue;
                        };
                        tasks.push(ExactLoadNormalizationTask::LeaveLoad(load));
                        tasks.push(ExactLoadNormalizationTask::Visit(resolved));
                    }
                }
            }
            ExactLoadNormalizationTask::RebuildBinary(operator) => {
                let right = results.pop().expect("visited right bitvector term");
                let left = results.pop().expect("visited left bitvector term");
                results.push(operator.build(left, right));
            }
            ExactLoadNormalizationTask::RebuildUnary(operator) => {
                let value = results.pop().expect("visited unary bitvector term");
                results.push(operator.build(value));
            }
            ExactLoadNormalizationTask::RebuildIf(condition) => {
                let else_term = results.pop().expect("visited else term");
                let then_term = results.pop().expect("visited then term");
                results.push(OldMachineTerm::If {
                    condition: Box::new(condition),
                    then_term: Box::new(then_term),
                    else_term: Box::new(else_term),
                });
            }
            ExactLoadNormalizationTask::RebuildPureFunction {
                name,
                argument_count,
            } => {
                let first = results.len() - argument_count;
                let arguments = results.split_off(first);
                results.push(OldMachineTerm::rebuild_pure_application(name, arguments));
            }
            ExactLoadNormalizationTask::LeaveLoad(load) => {
                active_loads.remove(&load);
            }
        }
    }
    results
        .pop()
        .expect("normalization produces one bitvector term")
}

pub(super) fn normalize_exact_memory_loads_in_bitvector(
    term: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> OldMachineTerm {
    normalize_exact_memory_loads_in_bitvector_iterative(term, assumptions)
}

#[cfg(test)]
mod exact_load_normalization_tests {
    use super::*;

    fn load_chain(length: usize, tail: u32) -> OldMachineTerm {
        let pointer = Address::new(
            "normalization-load-chain".into(),
            AddressOffset::constant(0),
        );
        (0..length).fold(OldMachineTerm::constant(tail), |value, _| {
            let memory = SymbolicMemory::new().store(pointer.clone(), ProgramValue::Int32(value));
            crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(&(intern_memory(memory))),
                pointer.clone(),
                crate::kernel::LoadKind::Int32,
            )
        })
    }

    fn nested_add(length: usize, tail: OldMachineTerm) -> OldMachineTerm {
        (0..length).fold(tail, |term, _| {
            binary_node!(
                Int32,
                Add,
                Box::new(OldMachineTerm::constant(0)),
                Box::new(term)
            )
        })
    }

    /// A state's own cell answers a load term only when the cell is that
    /// read: a word cell is not the value of a byte read at its address, and
    /// a signed byte cell is not the value of an unsigned byte read. Every
    /// route that resolves a load against the state it names — exact-load
    /// normalization, the deep canonical form, and the materialized-load
    /// frame — asks the same question, so one table pins all of them.
    #[test]
    fn a_state_cell_answers_only_a_read_of_its_own_kind() {
        use crate::kernel::LoadKind;
        let pointer = Address::new("kind-checked-cell".into(), AddressOffset::constant(0));
        let load = |memory: &SymbolicMemory, kind| {
            crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(&(intern_memory(memory.clone()))),
                pointer.clone(),
                kind,
            )
        };
        let word = SymbolicMemory::new()
            .with_block("kind-checked-cell", 4)
            .store(
                pointer.clone(),
                ProgramValue::Int32(OldMachineTerm::constant(256)),
            );
        let signed_byte = SymbolicMemory::new()
            .with_block("kind-checked-cell", 4)
            .store(pointer.clone(), crate::kernel::int8(u32::MAX));
        let context = PureFactContext::new();
        for (memory, own, other, value) in [
            (
                &word,
                LoadKind::Int32,
                LoadKind::UInt8,
                OldMachineTerm::constant(256),
            ),
            (
                &signed_byte,
                LoadKind::Int8,
                LoadKind::UInt8,
                OldMachineTerm::narrow_constant(MachineIntegerType::Int8, 0xFF),
            ),
        ] {
            assert_eq!(
                canonicalize_atomic_loads_deep(&load(memory, own)),
                value,
                "the cell is the value of a read of its own kind"
            );
            assert_ne!(
                canonicalize_atomic_loads_deep(&load(memory, other)),
                value,
                "the cell is not the value of a read of another kind"
            );
            assert_ne!(
                normalize_exact_memory_loads_in_bitvector(&load(memory, other), &context),
                value,
                "exact normalization answers only a read of the cell's kind"
            );
        }
        // A cell holding a read of another kind does not materialize this
        // read: storing the signed read back is not the unsigned read's cell.
        let source = SymbolicMemory::new().with_block("kind-checked-cell", 4);
        let materialized = source.clone().store(
            pointer.clone(),
            ProgramValue::Int8(load(&source, LoadKind::Int8)),
        );
        assert!(memory_materializes_atomic_load(
            &materialized,
            &source,
            &pointer,
            LoadKind::Int8
        ));
        assert!(!memory_materializes_atomic_load(
            &materialized,
            &source,
            &pointer,
            LoadKind::UInt8
        ));
    }

    #[test]
    fn exact_load_normalization_is_complete_past_the_old_depth_limit() {
        let term = nested_add(80, load_chain(80, 29));
        assert_eq!(
            normalize_exact_memory_loads_in_bitvector(&term, &PureFactContext::new()),
            OldMachineTerm::constant(29)
        );

        let offset = (0..80).fold(
            AddressOffset::scaled_int32_node(load_chain(80, 7), 4),
            |offset, _| AddressOffset::raw_add(AddressOffset::constant(0), offset),
        );
        assert_eq!(
            normalize_exact_memory_loads_in_pointer_offset(&offset, &PureFactContext::new()),
            AddressOffset::constant(28)
        );
    }
}

#[cfg(test)]
#[test]
fn effect_pointer_equality_retains_exact_loads_and_explicit_offset_facts() {
    let pointer = Address::new("effect-offset".into(), AddressOffset::constant(0));
    let memory = SymbolicMemory::new().store(
        pointer.clone(),
        ProgramValue::Int32(OldMachineTerm::constant(7)),
    );
    let loaded = AddressOffset::scaled_int32_node(
        crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::unplaced(&(intern_memory(memory))),
            pointer,
            crate::kernel::LoadKind::Int32,
        ),
        4,
    );
    assert!(program_pointer_offsets_proven_equal_for_effect(
        &loaded,
        &AddressOffset::constant(28).clone(),
        &PureFactContext::new(),
    ));
    assert!(!program_pointer_offsets_proven_equal_for_effect(
        &loaded,
        &AddressOffset::constant(32).clone(),
        &PureFactContext::new(),
    ));

    let left = AddressOffset::variable(Variable(901));
    let right = AddressOffset::variable(Variable(902));
    let facts = PureFactContext::new().assume_condition(
        OldConditionTerm::address_offset_equal(left.clone(), right.clone()),
        true,
    );
    assert!(program_pointer_offsets_proven_equal_for_effect(
        &left.clone(),
        &right.clone(),
        &facts
    ));
    assert!(!program_pointer_offsets_proven_equal_for_effect(
        &left.clone(),
        &right.clone(),
        &PureFactContext::new()
    ));
    assert!(!program_pointer_offsets_proven_equal_for_effect(
        &left.clone(),
        &(AddressOffset::variable(Variable(903))).clone(),
        &facts,
    ));
}

#[cfg(test)]
#[test]
fn effect_pointer_equality_does_not_use_general_context_inconsistency() {
    // Surface planning; only this test reaches it from inside the kernel.

    let left = AddressOffset::variable(Variable(911));
    let right = AddressOffset::variable(Variable(912));
    let facts = PureFactContext::new().assume_condition(OldConditionTerm::Constant(false), true);
    let goal = Proposition::condition_is(
        OldConditionTerm::address_offset_equal(left.clone(), right.clone()),
        true,
    );
    assert!(
        crate::kernel::search::ProofSearch::proves(&(facts), &goal),
        "the old general fallback could close this query"
    );
    assert!(!program_pointer_offsets_proven_equal_for_effect(
        &left.clone(),
        &right.clone(),
        &facts
    ));
}

#[cfg(test)]
#[test]
fn effect_pointer_equality_stops_at_the_verification_deadline() {
    let offset = AddressOffset::constant(0);
    crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        assert!(!program_pointer_offsets_proven_equal_for_effect(
            &offset.clone(),
            &offset.clone(),
            &PureFactContext::new(),
        ));
    });
}

/// A lookup already in progress for a cell refuses re-entry without
/// unregistering the outer lookup: the guard is built only when its key is
/// new, so the refused path drops nothing.
#[cfg(test)]
#[test]
fn cell_lookup_guard_refuses_reentry_and_keeps_the_outer_lookup() {
    let memory = crate::kernel::intern_memory(SymbolicMemory::new());
    let pointer = Address::new("cell".into(), AddressOffset::constant(0));
    let outer = CellLookupGuard::enter(&memory, &pointer).expect("the first lookup registers");
    assert!(!memory_dag_cell_lookup_depth_is_zero());
    assert!(
        CellLookupGuard::enter(&memory, &pointer).is_none(),
        "re-entering the cell is a cycle"
    );
    assert!(
        !memory_dag_cell_lookup_depth_is_zero(),
        "the refused re-entry leaves the outer lookup registered"
    );
    drop(outer);
    assert!(memory_dag_cell_lookup_depth_is_zero());
}

/// Canonicalizes the loads inside a binary condition so forms differing
/// only in redundant cached cells compare and prove identically.
pub(super) fn condition_with_canonicalized_loads(
    condition: &OldConditionTerm,
) -> Option<OldConditionTerm> {
    let binary = |left: &OldMachineTerm, right: &OldMachineTerm| {
        (
            Box::new(canonicalize_atomic_loads_deep(left)),
            Box::new(canonicalize_atomic_loads_deep(right)),
        )
    };
    Some(match condition {
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left,
            right,
        } => {
            let (left, right) = binary(left, right);
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            }
        }
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left,
            right,
        } => {
            let (left, right) = binary(left, right);
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            }
        }
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        } => {
            let (left, right) = binary(left, right);
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left,
                right,
            }
        }
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        } => {
            let (left, right) = binary(left, right);
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            }
        }
        OldConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            relation: CompareRelation::Equal,
            left,
            right,
        } => {
            let (left, right) = binary(left, right);
            OldConditionTerm::Compare {
                format: *format,
                relation: CompareRelation::Equal,
                left,
                right,
            }
        }
        _ => return None,
    })
}

/// Never-inlined endpoint matcher for the effect arms: the direct-unchanged
/// check participates in transport recursion where added frame bytes
/// overflow the stack. The fact's state handles may differ from the
/// effect's endpoints by bookkeeping (materialized cells, recorded locals);
/// what the chain needs is agreement on the loaded cell, which the
/// directly-match check decides per pointer with havoc-marker parity.
#[inline(never)]
fn directly_matched_effect_endpoint(
    effect_side: &SymbolicMemory,
    side: &SymbolicMemory,
    pointer: &Address,
    assumptions: &PureFactContext,
) -> bool {
    memories_directly_match_for_pointer_load(effect_side, side, pointer, assumptions)
}

#[cfg(test)]
mod opaque_pointer_frame_tests {
    use super::*;

    // Exercise the same explicit primitive as a Surface preserve tactic: observe
    // both endpoints, narrow the supplied separation, and apply one effect.
    fn explicit_pointer_store_frame(
        before: &SymbolicMemory,
        after: &SymbolicMemory,
        field: &Address,
        write: &Address,
        facts: &PureFactContext,
    ) -> Option<(Pointer, Proposition)> {
        let resource = |p: Address, bytes| {
            Resource::Memory(MemoryRange::new_with_element_width(
                p,
                0u32.into(),
                1u32.into(),
                bytes,
            ))
        };
        let changed = resource(write.clone(), 4);
        let kept = resource(field.clone(), 8);
        if !facts.proves_resource_separate(&changed, &kept) {
            return None;
        }
        let entry = ExecutionState::new().with_memory(before.clone());
        let exit = entry.clone().with_memory(after.clone());
        let observe = |state: &ExecutionState| {
            let paths = crate::kernel::eval::evaluate_logical_memory_load_paths(
                state.memory(),
                field.clone(),
                ProgramType::Int32Pointer,
                Default::default(),
                Vec::new(),
                &PureFactContext::new(),
            );
            let [path] = paths.as_slice() else {
                panic!("one logical read")
            };
            let ExpressionOutcome::Value(ProgramValue::Pointer(value)) = &path.outcome else {
                panic!("pointer observation")
            };
            crate::kernel::eval::typed_reads::record_at(
                &state.program_point(),
                field,
                &ProgramValue::Pointer(value.clone()),
            );
            value.clone()
        };
        let before_value = observe(&entry);
        let after_value = observe(&exit);
        let result = Proposition::condition_is(
            OldConditionTerm::pointer_equal(after_value.clone(), before_value),
            true,
        );
        let footprint = crate::kernel::RegionFootprint::transition(
            "selected".into(),
            &entry,
            &exit,
            &Vec::<ExecutionPureFact>::new(),
        );
        let separation = Proposition::ResourceSeparate {
            left: Box::new(Resource::Footprint(footprint)),
            right: Box::new(kept),
        };
        crate::kernel::proof::preservation::apply(&separation, None, &result, None, |p| {
            p == &separation
        })
        .unwrap();
        Some((after_value, result))
    }

    #[test]
    fn complete_pointer_domains_follow_numeric_storage_equality_only() {
        let _session = crate::kernel::VerificationSession::enter();
        let [a, b, c, d] = [1, 2, 3, 4].map(|id| Address::symbolic(Variable(9_880_450 + id)));
        let memory = intern_memory(SymbolicMemory::new());
        let left = Address::loaded_value(&memory, &a);
        let right = Address::loaded_value(&memory, &d);
        let address_equality = |a: &Address, b: &Address| {
            OldConditionTerm::uint64_equal(
                OldMachineTerm::integer_address(a.clone()),
                OldMachineTerm::integer_address(b.clone()),
            )
        };
        let numbers_only =
            PureFactContext::new().assume_condition(address_equality(&left, &right), true);
        assert!(!pointer_read_provenance_equal(&left, &right, &numbers_only));
        let mut same_storage = PureFactContext::new();
        for (a, b) in [(&a, &b), (&c, &d), (&b, &c)] {
            same_storage = same_storage.assume_condition(address_equality(a, b), true);
        }
        assert!(pointer_read_provenance_equal(&left, &right, &same_storage));
        assert!(pointer_read_bounds_equal(&left, &right, &same_storage));
        let overwritten = intern_memory(
            memory
                .memory()
                .clone()
                .store(a.offset_by_bytes(4), ProgramValue::UInt32(0u32.into())),
        );
        let changed = Address::loaded_value(&overwritten, &d);
        assert!(!pointer_read_provenance_equal(
            &left,
            &changed,
            &same_storage
        ));
        assert!(!pointer_read_bounds_equal(&left, &changed, &same_storage));
    }

    #[test]
    fn complete_pointer_read_addresses_follow_a_shared_unchanged_source() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Address::symbolic(Variable(9_880_490));
        let base = intern_memory(SymbolicMemory::new());
        let left = intern_memory(base.memory().clone().store(
            field.offset_by_bytes(8),
            ProgramValue::UInt64(OldMachineTerm::uint64_constant(1)),
        ));
        let right = intern_memory(base.memory().clone().store(
            field.offset_by_bytes(16),
            ProgramValue::UInt64(OldMachineTerm::uint64_constant(2)),
        ));
        let a = Address::loaded_value(&left, &field);
        let b = Address::loaded_value(&right, &field);
        let context = PureFactContext::new();
        assert!(pointer_read_provenance_equal(&a, &b, &context));
        assert!(pointer_read_bounds_equal(&a, &b, &context));
        assert!(complete_pointer_reads_equal_across_frame(&a, &b, &context));
        let changed = intern_memory(
            base.memory()
                .clone()
                .store(field.offset_by_bytes(4), ProgramValue::UInt32(0u32.into())),
        );
        assert!(!complete_pointer_reads_equal_across_frame(
            &a,
            &Address::loaded_value(&changed, &field),
            &context,
        ));
    }

    #[test]
    fn complete_pointer_read_addresses_use_exact_retained_typed_producers() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Address::symbolic(Variable(9_880_491));
        let base = SymbolicMemory::new();
        let left = intern_memory(base.clone().store(
            field.offset_by_bytes(8),
            ProgramValue::UInt64(OldMachineTerm::uint64_constant(1)),
        ));
        let right = intern_memory(base.store(
            field.offset_by_bytes(16),
            ProgramValue::UInt64(OldMachineTerm::uint64_constant(2)),
        ));
        let cell_bits = |memory: &SharedMemory| {
            crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(memory),
                field.clone(),
                LoadKind::Int32,
            )
        };
        let read = |memory: &SharedMemory| Address::loaded(&cell_bits(memory)).unwrap();
        let a = read(&left);
        let b = read(&right);
        // A pointer read names its typed producer's exact definition.
        for value in [&a, &b] {
            let definition = value.as_loaded_value().expect("a typed pointer read");
            assert_eq!(definition.defining_address, field);
            assert_eq!(definition.displacement, AddressOffset::constant(0));
        }
        let context = PureFactContext::new();
        assert!(complete_pointer_reads_equal_across_frame(&a, &b, &context));
        assert!(!complete_pointer_reads_equal_across_frame(
            &a,
            &b.offset_by_bytes(8),
            &context
        ));
        // Arithmetic resemblance to a typed producer supplies no read
        // identity: an address indexed by the cell's scalar is not the read.
        let scalar_indexed = field.offset_by_elements(cell_bits(&right), 4);
        assert!(!complete_pointer_reads_equal_across_frame(
            &a,
            &scalar_indexed,
            &context
        ));
        let changed = intern_memory(
            right
                .memory()
                .clone()
                .store(field.offset_by_bytes(4), ProgramValue::UInt32(0u32.into())),
        );
        let c = read(&changed);
        assert!(c.as_loaded_value().is_some());
        assert!(!complete_pointer_reads_equal_across_frame(&a, &c, &context));
    }

    #[test]
    fn complete_pointer_domain_uses_explicit_whole_header_separation() {
        let _session = crate::kernel::VerificationSession::enter();
        let header = Address::symbolic(Variable(9_880_410));
        let field = header.clone().offset_by_bytes(8);
        let buffer = Address::symbolic(Variable(9_880_411));
        let before = intern_memory(SymbolicMemory::new());
        let after = intern_memory(before.memory().clone().store(
            buffer.clone().offset_by_bytes(4),
            ProgramValue::Int32(7u32.into()),
        ));
        let read = |retained_state: &SharedMemory| Address::loaded_value(retained_state, &field);
        let separation = |header_words: u32| Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new(
                header.clone(),
                0u32.into(),
                header_words.into(),
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                buffer.clone(),
                0u32.into(),
                8u32.into(),
            ))),
        };
        let empty = PureFactContext::new();
        let context = empty.clone().assume_proposition(separation(4));
        assert!(!pointer_read_provenance_equal(
            &read(&before),
            &read(&after),
            &empty
        ));
        assert!(pointer_read_provenance_equal(
            &read(&before),
            &read(&after),
            &context
        ));
        assert!(pointer_read_bounds_equal(
            &read(&before),
            &read(&after),
            &context
        ));
        let too_short = empty.assume_proposition(separation(1));
        assert!(!pointer_read_provenance_equal(
            &read(&before),
            &read(&after),
            &too_short
        ));
        let overwritten = intern_memory(after.memory().clone().store(
            field.clone().offset_by_bytes(4),
            ProgramValue::Int32(0u32.into()),
        ));
        assert!(!pointer_read_provenance_equal(
            &read(&before),
            &read(&overwritten),
            &context
        ));
        assert!(!pointer_read_bounds_equal(
            &read(&before),
            &read(&overwritten),
            &context
        ));
    }

    #[test]
    fn copied_pointer_value_uses_explicit_whole_header_separation() {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = crate::kernel::TransportReadScope::enter();
        let header = Address::symbolic(Variable(9_880_420));
        let field = header.clone().offset_by_bytes(8);
        let buffer = Address::symbolic(Variable(9_880_421));
        let target = Address::symbolic(Variable(9_880_422));
        let stored = Pointer::new(target.clone(), ProgramType::Int32Pointer)
            .with_bounds(Some(SubobjectBounds::new(target, 4u32.into())));
        let before =
            SymbolicMemory::new().store(field.clone(), ProgramValue::Pointer(stored.clone()));
        let write = buffer.clone().offset_by_bytes(4);
        let memory = intern_memory(
            before
                .clone()
                .without_possible_aliasing_cells(&write, 4, &PureFactContext::new())
                .store(write.clone(), ProgramValue::Int32(7u32.into())),
        );
        let read = |memory: &SharedMemory| {
            Pointer::from_read(
                stored.address().clone(),
                ProgramType::Int32Pointer,
                memory,
                &field,
            )
        };
        let separation = |words: u32| Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new(
                header.clone(),
                0u32.into(),
                words.into(),
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                buffer.clone(),
                0u32.into(),
                8u32.into(),
            ))),
        };
        let empty = PureFactContext::new();
        assert!(!empty.pointer_provenance_match(&read(&memory), &stored));
        let context = empty.clone().assume_proposition(separation(4));
        let (observed, equality) =
            explicit_pointer_store_frame(&before, memory.memory(), &field, &write, &context)
                .unwrap();
        let context = context.assume_proposition(equality);
        assert!(context.pointer_provenance_match(&observed, &stored));
        // Provenance matching includes the complete pointer's subobject bounds.
        let too_short = empty.assume_proposition(separation(1));
        assert!(
            explicit_pointer_store_frame(&before, memory.memory(), &field, &write, &too_short)
                .is_none()
        );
        assert!(!too_short.pointer_provenance_match(&read(&memory), &stored));
        let partial = intern_memory(memory.memory().clone().store(
            field.clone().offset_by_bytes(4),
            ProgramValue::Int32(0u32.into()),
        ));
        assert!(!context.pointer_provenance_match(&read(&partial), &stored));
    }

    fn setup() -> (Address, Address, Address, Proposition, Proposition) {
        let field = Address::new(
            AddressBase::Concrete("local:opaque-frame".into()),
            AddressOffset::constant(0),
        );
        let write = Address::symbolic(Variable(9_880_001));
        let argument = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(128));
        let alias = Proposition::condition_is(
            OldConditionTerm::address_equal(write.clone(), argument.clone()),
            true,
        );
        let separation = Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                field.clone(),
                OldMachineTerm::constant(0),
                OldMachineTerm::constant(1),
                8,
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                argument.clone(),
                OldMachineTerm::constant(0),
                OldMachineTerm::constant(1),
                4,
            ))),
        };
        (field, write, argument, alias, separation)
    }

    #[test]
    fn aliased_store_frame_retains_and_rechecks_exact_alias_and_separation() {
        let (field, write, _, alias, separation) = setup();
        let assumptions = PureFactContext::new()
            .assume_proposition(alias.clone())
            .assume_proposition(separation.clone());
        let step = MemoryDerivation::Store {
            base: intern_memory(SymbolicMemory::default()),
            pointer: write.clone(),
            value: ProgramValue::Int32(OldMachineTerm::constant(7)).into(),
        };
        let proof = typed_store_separated_ranges_evidence(&write, 4, &field, 8, &assumptions)
            .expect("one exact alias must select the stated range separation");
        assert!(proof.checks(&step, &field, 8, &assumptions));
        for remaining in [alias, separation] {
            let missing = PureFactContext::new().assume_proposition(remaining);
            assert!(!proof.checks(&step, &field, 8, &missing));
        }
        let wrong_step = MemoryDerivation::Store {
            base: intern_memory(SymbolicMemory::default()),
            pointer: field.clone(),
            value: ProgramValue::Int32(OldMachineTerm::constant(7)).into(),
        };
        assert!(!proof.checks(&wrong_step, &field, 8, &assumptions));
    }

    #[test]
    fn bounded_pointer_read_preserves_value_across_forgotten_cache() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(128));
        let possible_write = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(9_880_201)), 4),
        );
        let stored = Address::symbolic(Variable(9_880_202));
        let memory = SymbolicMemory::new().store(
            field.clone(),
            ProgramValue::typed_pointer(stored.clone(), ProgramType::Int32Pointer),
        );
        let memory =
            memory.without_possible_aliasing_cells(&possible_write, 4, &PureFactContext::new());
        let retained_state = intern_memory(memory);
        assert!(matches!(
            retained_state.derivation().as_deref(),
            Some(MemoryDerivation::CellsForgotten { .. })
        ));
        let read = Address::loaded_value(&retained_state, &field);
        let context = PureFactContext::new();
        context
            .equality_graph
            .register_pointer_read_definition(&read, &retained_state, &field);
        assert!(pointer_read_has_recorded_value(&read, &stored, &context));
        let read_from = |memory| {
            let retained_state = intern_memory(memory);
            let read = Address::loaded_value(&retained_state, &field);
            context
                .equality_graph
                .register_pointer_read_definition(&read, &retained_state, &field);
            read
        };
        let replacement = Address::symbolic(Variable(9_880_203));
        let changed = read_from(retained_state.memory().clone().store(
            field.clone(),
            ProgramValue::typed_pointer(replacement.clone(), ProgramType::Int32Pointer),
        ));
        assert!(!pointer_read_has_recorded_value(
            &changed, &stored, &context
        ));
        assert!(pointer_read_has_recorded_value(
            &changed,
            &replacement,
            &context
        ));
        for address in [field.clone(), field.offset_by_bytes(4), possible_write] {
            let changed = read_from(
                retained_state
                    .memory()
                    .clone()
                    .store(address, ProgramValue::Int32(OldMachineTerm::constant(7))),
            );
            assert!(!pointer_read_has_recorded_value(
                &changed, &stored, &context
            ));
        }
    }

    #[test]
    fn opaque_pointer_transport_requires_unchanged_field_bytes() {
        let (field, _, argument, _, separation) = setup();
        let before = intern_memory(SymbolicMemory::default().with_block("local:opaque-frame", 8));
        let read = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&before),
            field.clone(),
            LoadKind::Int32,
        );
        let variable = crate::kernel::eval::load_variable_for_term(&read)
            .unwrap()
            .0;
        let pointer = Address::symbolic(variable);
        let source = Proposition::condition_is(
            OldConditionTerm::address_equal(pointer.clone(), argument.clone()),
            true,
        );
        let assumptions = PureFactContext::new()
            .assume_proposition(source.clone())
            .assume_proposition(separation.clone());
        let after = before
            .memory()
            .clone()
            .store(pointer, ProgramValue::Int32(OldMachineTerm::constant(7)));
        let theorem = prove_program_condition_fact_transport(
            &source,
            &crate::kernel::ProgramPoint::of_memory(&after),
            &assumptions,
        )
        .expect("unchanged pointer identity transports across an aliased store");
        assert!(
            program_condition_fact_transport_target_in_context(&theorem, &source, &assumptions)
                .is_some()
        );
        assert!(
            program_condition_fact_transport_target_in_context(
                &theorem,
                &source,
                &PureFactContext::new().assume_proposition(source.clone())
            )
            .is_none()
        );
        let changed = before
            .memory()
            .clone()
            .store(field, ProgramValue::pointer(argument));
        assert!(
            prove_program_condition_fact_transport(
                &source,
                &crate::kernel::ProgramPoint::of_memory(&changed),
                &assumptions
            )
            .is_none()
        );
    }

    #[test]
    fn wide_alias_reads_reconnect_each_endpoints_own_projection() {
        let _session = crate::kernel::VerificationSession::enter();
        let left_pointer = Address::symbolic(Variable(9_880_610));
        let right_pointer = Address::symbolic(Variable(9_880_611));
        let alias = Proposition::condition_is(
            OldConditionTerm::address_equal(left_pointer.clone(), right_pointer.clone()),
            true,
        );
        let context = PureFactContext::new().assume_proposition(alias);
        let source = intern_memory(
            SymbolicMemory::new()
                .with_block_without_derivation("local:projection-left", 4)
                .with_block_without_derivation("local:projection-right", 4),
        );
        // These projections retain different irrelevant local declarations.
        // Neither changes the bytes observable through either symbolic pointer.
        let left_memory = intern_memory(
            SymbolicMemory::new().with_block_without_derivation("local:projection-left", 4),
        );
        let right_memory = intern_memory(
            SymbolicMemory::new().with_block_without_derivation("local:projection-right", 4),
        );
        record_canonical_load_projection(&source, &left_memory, &left_pointer);
        record_canonical_load_projection(&source, &right_memory, &right_pointer);
        let left = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&left_memory),
            left_pointer.clone(),
            LoadKind::Bits64,
        );
        let right = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&right_memory),
            right_pointer.clone(),
            LoadKind::Bits64,
        );
        assert!(wide_read_has_recorded_value(&left, &right, &context));
        assert!(wide_read_has_recorded_value(&right, &left, &context));
        assert!(!wide_read_has_recorded_value(
            &left,
            &right,
            &PureFactContext::new(),
        ));
        let narrow = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&right_memory),
            right_pointer.clone(),
            LoadKind::Int32,
        );
        assert!(!wide_read_has_recorded_value(&left, &narrow, &context));
        let overwritten_source = intern_memory(source.memory().clone().store(
            right_pointer.clone(),
            ProgramValue::UInt64(OldMachineTerm::uint64_constant(7)),
        ));
        let overwritten = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(
                &(canonical_projected_load_memory(&overwritten_source, &right_pointer)),
            ),
            right_pointer,
            LoadKind::Bits64,
        );
        assert!(!wide_read_has_recorded_value(&left, &overwritten, &context));
    }

    #[test]
    fn wide_value_uses_retained_projection_source_and_rejects_overwrites() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(9_880_401)), 4),
        );
        let write = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(9_880_402)), 4),
        );
        let alias = Proposition::condition_is(
            OldConditionTerm::address_equal(write.clone(), address.clone()),
            true,
        );
        let context = PureFactContext::new().assume_proposition(alias);
        let value = OldMachineTerm::uint64_constant(42);
        let source = intern_memory(
            SymbolicMemory::new()
                .with_block("local:wide-unrelated", 4)
                .store(
                    Address::new(
                        AddressBase::Concrete("local:wide-unrelated".into()),
                        AddressOffset::constant(0),
                    ),
                    ProgramValue::Int32(OldMachineTerm::constant(1)),
                )
                .store(write.clone(), ProgramValue::UInt64(value.clone())),
        );
        let projected = canonical_projected_load_memory(&source, &address);
        assert_ne!(projected, source);
        let direct = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&source),
            address.clone(),
            LoadKind::Bits64,
        );
        let read = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&projected),
            address.clone(),
            LoadKind::Bits64,
        );
        assert!(wide_read_has_recorded_value(&direct, &value, &context));
        assert!(wide_read_has_recorded_value(&read, &value, &context));
        assert!(!wide_read_has_recorded_value(
            &read,
            &value,
            &PureFactContext::new()
        ));
        let projected_read = |memory| {
            let source = intern_memory(memory);
            crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(&(canonical_projected_load_memory(&source, &address))),
                address.clone(),
                LoadKind::Bits64,
            )
        };
        let replacement = OldMachineTerm::uint64_constant(7);
        let changed = projected_read(
            source
                .memory()
                .clone()
                .store(write.clone(), ProgramValue::UInt64(replacement.clone())),
        );
        assert!(!wide_read_has_recorded_value(&changed, &value, &context));
        assert!(wide_read_has_recorded_value(
            &changed,
            &replacement,
            &context
        ));
        for at in [write.clone(), write.offset_by_bytes(4)] {
            let changed = projected_read(
                source
                    .memory()
                    .clone()
                    .store(at, ProgramValue::Int32(OldMachineTerm::constant(7))),
            );
            assert!(!wide_read_has_recorded_value(&changed, &value, &context));
        }
        let unknown = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(9_880_403)), 4),
        );
        let forgotten = projected_read(source.memory().without_possible_aliasing_cells(
            &unknown,
            4,
            &PureFactContext::new(),
        ));
        assert!(wide_read_has_recorded_value(&forgotten, &value, &context));
        let changed = projected_read(
            source
                .memory()
                .clone()
                .store(unknown, ProgramValue::Int32(OldMachineTerm::constant(7))),
        );
        let (proved, diagnostics) =
            capture_read_resolutions(|| wide_read_has_recorded_value(&changed, &value, &context));
        assert!(!proved);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(
            diagnostics[0].reason,
            "step not proved separate from the read"
        );
        assert!(diagnostics[0].recovered.is_none());
        // Nested capture consumes only its own query; the outer written check
        // is restored and never inherits a speculative inner query.
        let (_, outer) = capture_read_resolutions(|| {
            let (_, inner) = capture_read_resolutions(|| {
                wide_read_has_recorded_value(&changed, &value, &context)
            });
            assert_eq!(inner.len(), 1);
        });
        assert!(outer.is_empty());
    }

    #[test]
    fn a_wide_numeric_read_observes_bits_without_copying_the_pointer_record() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Address::symbolic(Variable(9_880_490));
        let bits = OldMachineTerm::uint64_constant(17);
        let number = ProgramValue::UInt64(bits.clone());
        let word = number
            .clone()
            .complete_word(Address::symbolic(Variable(9_880_491)));
        let context = PureFactContext::new();
        let same_value = || {
            crate::kernel::reasoning::program_values_proven_equal_for_memory_resolution(
                &word, &number, &context,
            )
        };
        assert!(!same_value());
        let memory = intern_memory(SymbolicMemory::new().store(field.clone(), word.clone()));
        let read = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&memory),
            field,
            LoadKind::Bits64,
        );
        assert!(wide_read_has_recorded_value(&read, &bits, &context));
        assert!(wide_read_has_recorded_value(&bits, &read, &context));
        assert!(!same_value());
    }

    #[test]
    fn recovered_wide_word_uses_current_equality_closure() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(128));
        let parent = Address::symbolic(Variable(9_880_501));
        let alias = Address::symbolic(Variable(9_880_502));
        let equality = Proposition::condition_is(
            OldConditionTerm::address_equal(parent.clone(), alias.clone()),
            true,
        );
        let context = PureFactContext::new().assume_proposition(equality);
        let stored = OldMachineTerm::IntegerAddress(
            Box::new(parent),
            crate::kernel::AddressObjectClass::NONE,
        );
        let wanted = OldMachineTerm::IntegerAddress(
            Box::new(alias),
            crate::kernel::AddressObjectClass::NONE,
        );
        assert_ne!(stored, wanted);
        assert!(context.uint64_values_known_equal(&stored, &wanted));
        let memory =
            intern_memory(SymbolicMemory::new().store(field.clone(), ProgramValue::UInt64(stored)));
        let read = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&memory),
            field,
            LoadKind::Bits64,
        );
        assert!(wide_read_has_recorded_value(&read, &wanted, &context));
        assert!(wide_read_has_recorded_value(&wanted, &read, &context));
        let (proved, diagnostics) = capture_read_resolutions(|| {
            wide_read_has_recorded_value(&read, &wanted, &PureFactContext::new())
        });
        assert!(!proved);
        assert_eq!(diagnostics.len(), 1);
        let diagnostic = &diagnostics[0];
        assert_eq!(diagnostic.reason, "step affects the read's bytes");
        assert!(diagnostic.recovered.is_some());
        assert!(!diagnostic.equal);
        assert_eq!(diagnostic.expected, wanted);
        assert_eq!(diagnostic.stopped_at.as_ref(), Some(&diagnostic.producer));
        let mut labels = crate::surface::proof_diagnostics::render::MemoryStateLabels::ambient();
        let rendered = crate::surface::proof_diagnostics::render::render_read_resolution(
            diagnostic,
            &mut labels,
        );
        assert!(rendered.contains("recovered word equality:"), "{rendered}");
        assert!(
            rendered.contains("equality check: not proved"),
            "{rendered}"
        );
        assert!(rendered.contains("producer source: state#"), "{rendered}");
        assert!(!rendered.contains("…"), "{rendered}");
        assert!(wide_read_has_recorded_value(&read, &wanted, &context));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/memory_history/opaque_pointer_frame_tests.rs");
    }
}

#[cfg(test)]
mod canonical_numeric_run_tests {
    use super::*;
    use crate::kernel::primitives::{CellRun, IndexIntervals, RunValueMode};

    #[test]
    fn deep_canonicalization_retains_structural_numeric_run_addresses() {
        let _session = crate::kernel::VerificationSession::enter();
        let index_cell = Address::new("canonical-index".into(), AddressOffset::constant(0));
        let source = intern_memory(
            SymbolicMemory::new()
                .with_block("canonical-index", 4)
                .store(
                    index_cell.clone(),
                    ProgramValue::Int32(OldMachineTerm::constant(8)),
                ),
        );
        let base = Address::new(
            "canonical-run".into(),
            AddressOffset::scaled_int32_node(
                crate::kernel::OldMachineTerm::read_named(
                    ProgramPoint::at(&source),
                    index_cell,
                    LoadKind::Int32,
                ),
                1,
            ),
        );
        let canonical_base = canonicalize_pointer_loads(&base);
        assert_eq!(canonical_base, base);
        let mut holes = IndexIntervals::default();
        holes.insert(3);
        let run = CellRun::new(base, 1, ProgramType::UInt8, 8, source, holes);
        let mut memory = SymbolicMemory::new();
        std::sync::Arc::make_mut(&mut memory.cells).add_run(run.clone());
        let canonical = canonical_memory_deep(&memory);
        for index in 0..8 {
            let pointer = canonical_base.offset_by_bytes(index);
            if index == 3 {
                assert!(canonical.cells.get(&pointer).is_none());
            } else {
                assert_eq!(canonical.cells.get(&pointer), Some(run.value(index)));
            }
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/memory_history/canonical_numeric_run_tests.rs");
    }
}

#[cfg(test)]
mod pointer_store_endpoint_tests {
    use super::*;

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/memory_history/pointer_store_endpoint_tests.rs");
    }
}

#[cfg(test)]
mod wide_range_reader_tests {
    use super::*;
    // Resource comparison may see two unequal native endpoints or mixed kinds.
    #[test]
    fn wide_resource_matching_refuses_signed_endpoint_comparison() {
        let base = Address::symbolic(Variable(984_200));
        let wide = MemoryRange::new_wide(
            base.clone(),
            OldMachineTerm::uint64_constant(0),
            OldMachineTerm::uint64_constant(1 << 33),
            4,
        );
        let other = MemoryRange::new_wide(
            base.clone(),
            OldMachineTerm::uint64_constant(0),
            OldMachineTerm::uint64_constant(2 << 33),
            4,
        );
        let narrow = MemoryRange::new(base, 0u32.into(), 1u32.into());
        let facts = PureFactContext::new();
        assert!(resources_directly_match(
            &Resource::Memory(wide.clone()),
            &Resource::Memory(wide.clone()),
            &facts
        ));
        for right in [other, narrow] {
            assert!(!resources_directly_match(
                &Resource::Memory(wide.clone()),
                &Resource::Memory(right),
                &facts
            ));
        }
    }
}

#[cfg(test)]
mod borrow_partition_tests {
    use super::*;
    use crate::kernel::borrows::{BorrowBinding, BorrowLedger};

    fn range(id: u64) -> MemoryRange {
        MemoryRange::new(
            Address::new(
                AddressBase::ExternalArgument,
                AddressOffset::variable(Variable(id)),
            ),
            0u32.into(),
            1u32.into(),
        )
    }

    fn resources() -> (ResourceContext, ResourceContext, MemoryRange, MemoryRange) {
        let write = range(901_001);
        let read = range(901_002);
        let view = ResourceFact::view_memory(read.clone());
        let bare = ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own_memory(write.clone()))
            .unchecked_with_fact(view.clone());
        let support = bare.occurrences_for_fact(&view)[0];
        let ledger = BorrowLedger::new();
        let holder = ledger.fresh_participant().unwrap();
        let opening = ledger
            .borrowed_contract_input(holder, support, view.clone(), None)
            .unwrap();
        let ledger = ledger.apply(&opening.transition).unwrap();
        assert!(ledger.permits_view(
            holder,
            &opening.description,
            opening.root_share,
            &PureFactContext::new()
        ));
        let bound = bare.clone().with_borrow_dependency(
            support,
            BorrowBinding {
                borrow: opening.borrow,
                scope: opening.scope,
                share: opening.root_share,
                support,
                viewed: view,
                hold: None,
            },
        );
        (bare, bound, write, read)
    }

    #[test]
    fn borrow_partition_evidence_requires_live_binding_and_rechecks_overlap() {
        let (bare, bound, write, read) = resources();
        let proposition = Proposition::ResourceComposition(bound.clone());
        let context = PureFactContext::new().assume_proposition(proposition.clone());
        let witness =
            typed_store_separated_ranges_evidence(write.base(), 4, read.base(), 4, &context)
                .unwrap();
        let step = MemoryDerivation::Store {
            base: intern_memory(SymbolicMemory::new()),
            pointer: write.base().clone(),
            value: ProgramValue::Int32(1u32.into()).into(),
        };
        assert!(witness.checks(&step, read.base(), 4, &context));
        let missing = PureFactContext::new()
            .assume_proposition(Proposition::ResourceComposition(bare.clone()));
        assert!(
            typed_store_separated_ranges_evidence(write.base(), 4, read.base(), 4, &missing)
                .is_none()
        );
        assert!(!witness.checks(&step, read.base(), 4, &missing));
        assert!(!witness.checks(&step, read.base(), 8, &context));
        let overlapping = context.assume_condition(
            OldConditionTerm::address_equal(write.base().clone(), read.base().clone()),
            true,
        );
        assert!(!witness.checks(&step, read.base(), 4, &overlapping));
        assert!(
            typed_store_separated_ranges_evidence(write.base(), 4, read.base(), 4, &overlapping)
                .is_none()
        );

        // Only metadata changes: the resource store itself is shared.
        let installed = missing.assume_proposition(proposition);
        assert!(
            typed_store_separated_ranges_evidence(write.base(), 4, read.base(), 4, &installed)
                .is_some()
        );
        let occurrence = bound.occurrences_for_fact(&ResourceFact::view_memory(read.clone()))[0];
        let removed = bound
            .clone()
            .without_bound_view_occurrence(occurrence, bound.borrow_dependency(occurrence).unwrap())
            .unwrap()
            .unchecked_with_fact(ResourceFact::view_memory(read.clone()));
        assert!(!removed.proves_borrow_partition_separate(&write, &read));
    }

    #[test]
    fn borrow_partition_binding_journal_tracks_branches_and_ignores_repeated_binding() {
        let (bare, bound, _, read) = resources();
        let occurrence = bound.occurrences_for_fact(&ResourceFact::view_memory(read))[0];
        let binding = bound.borrow_dependency(occurrence).unwrap().clone();
        let initial =
            crate::kernel::borrows::BorrowBindings::from_state(bare.borrow_dependency_state());
        let left = initial.with_inserted(occurrence, binding.clone());
        let right = initial.with_inserted(occurrence, binding.clone());
        // Equal-length branches have distinct updates; neither is a prefix.
        assert_eq!(
            left.state().changed_occurrences_since(&right.state()),
            vec![occurrence, occurrence]
        );
        let removed = left.without(occurrence);
        assert_eq!(
            removed.state().changed_occurrences_since(&left.state()),
            vec![occurrence]
        );
        assert_eq!(
            left.state().changed_occurrences_since(&removed.state()),
            vec![occurrence]
        );
        let mut repeated = left.clone();
        for _ in 0..1024 {
            repeated = repeated.with_inserted(occurrence, binding.clone());
        }
        assert!(std::sync::Arc::ptr_eq(&left.state(), &repeated.state()));
        assert!(
            repeated
                .state()
                .changed_occurrences_since(&left.state())
                .is_empty()
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/memory_history/borrow_partition_tests.rs");
    }
}

#[cfg(test)]
mod reversed_history_queries {
    use super::*;

    fn changed_history(size: usize) -> (SharedMemory, SharedMemory, Address) {
        let pointer = Address::new(
            format!("reversed-history-{size}").into(),
            AddressOffset::constant(0),
        );
        let before = SymbolicMemory::new()
            .with_block(format!("reversed-history-{size}"), (size as u32 + 2) * 4)
            .store(
                pointer.clone(),
                ProgramValue::Int32(OldMachineTerm::constant(0)),
            );
        let mut after = before.clone().store(
            pointer.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        );
        for index in 1..=size {
            after = after.store(
                pointer.offset_by_bytes(index as u32 * 4),
                ProgramValue::Int32(OldMachineTerm::constant(index as u32)),
            );
        }
        (intern_memory(before), intern_memory(after), pointer)
    }

    #[test]
    fn reversed_refusal_keeps_its_context_and_read_width() {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Address::new(
            "conditional-history".into(),
            AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(9_840_000)), 4),
        );
        let read_index = OldMachineTerm::Variable(Variable(9_840_001));
        let write_index = OldMachineTerm::Variable(Variable(9_840_002));
        let pointer = base.offset_by_elements(read_index.clone(), 4);
        crate::kernel::eval::declare_load_access_width(&pointer, 4);
        let write = base.offset_by_elements(write_index.clone(), 4);
        let weak = PureFactContext::new();
        let strong = weak.clone().assume_condition(
            OldConditionTerm::signed_less_than(read_index, write_index),
            true,
        );
        let before = SymbolicMemory::new().with_block("conditional-history", 64);
        let after = before.clone().store_with_context(
            write,
            ProgramValue::Int32(OldMachineTerm::constant(9)),
            &strong,
        );
        let before = intern_memory(before);
        let after = intern_memory(after);
        let _explicit = ExplicitReadScope(EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true)));
        with_extended_dag_bridging(|| {
            for (left, right) in [(&before, &after), (&after, &before)] {
                let history = recorded_load_history(left, right, &pointer, LoadKind::Int32, &weak);
                assert!(
                    !matches!(history, LoadHistory::OneVersion(_)),
                    "{history:?}"
                );
                assert_eq!(
                    history,
                    recorded_load_history_uncached(left, right, &pointer, LoadKind::Int32, &weak)
                );
            }
            let reference =
                recorded_load_history_uncached(&after, &before, &pointer, LoadKind::Int32, &strong);
            assert!(
                matches!(reference, LoadHistory::OneVersion(_)),
                "uncached: {reference:?}"
            );
            let unchanged =
                recorded_load_history(&after, &before, &pointer, LoadKind::Int32, &strong);
            assert!(
                matches!(unchanged, LoadHistory::OneVersion(_)),
                "{unchanged:?}"
            );
            let wide = recorded_load_history(&after, &before, &pointer, LoadKind::Bits64, &strong);
            assert!(!matches!(wide, LoadHistory::OneVersion(_)));
            assert_eq!(
                wide,
                recorded_load_history_uncached(
                    &after,
                    &before,
                    &pointer,
                    LoadKind::Bits64,
                    &strong
                )
            );
        });
    }

    mod scaling_tests {
        include!("../scaling_tests/kernel/memory_history/reversed_history_queries.rs");
    }
}

#[cfg(test)]
mod direct_unchanged_scaling_tests {
    use super::*;

    fn cell(block: &str) -> Address {
        Address::new(AddressBase::from(block), AddressOffset::constant(0))
    }

    fn value(index: usize) -> ProgramValue {
        ProgramValue::UInt32(OldMachineTerm::uint32_constant(index as u32))
    }

    /// The memory history's liveness query walks only the steps between its
    /// two points: unrelated stores keep a block live, the block's own
    /// lifetime ending does not, and the work grows with the steps walked,
    /// never with facts or other paths.
    #[test]
    fn recorded_writes_take_a_seeded_run_as_one_range_whatever_its_length() {
        let mut samples = Vec::new();
        for size in [16u32, 256, 4096] {
            let _session = crate::kernel::VerificationSession::enter();
            let base = Address::symbolic(Variable(98_700));
            let source = intern_memory(SymbolicMemory::new().store(base.clone(), value(1)));
            let start = ExecutionState::new()
                .with_memory(SymbolicMemory::new())
                .begin_function_entry_memory();
            let seeded = start.memory().clone().with_seeded_cells(
                base.clone(),
                4,
                ProgramType::Int32,
                0,
                size,
                source,
            );
            let state = start.clone().with_memory(seeded);
            let (writes, work) = crate::instrumentation::measure_deterministic_work(|| {
                RecordedWrites::between(start.path_link(), state.path_link())
            });
            let writes = writes.expect("the seeded state is reached from the start");
            assert!(writes.accesses.is_empty());
            assert_eq!(writes.ranges.len(), 1, "the run is one range");
            assert_eq!(writes.ranges[0].0.base(), &base);
            samples.push((size, work));
        }
        assert!(
            samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
            "recording a seeded run walked its slots: {samples:?}"
        );
    }

    #[test]
    fn liveness_walks_only_the_steps_between_its_points() {
        let block: AddressBase = "local:kept".into();
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let start = ExecutionState::new()
                .with_memory(SymbolicMemory::new().with_block(block.clone(), 4))
                .begin_function_entry_memory();
            let mut state = start.clone();
            for index in 0..size {
                let memory = state
                    .memory()
                    .clone()
                    .with_block(format!("local:other{index}"), 4)
                    .store(cell(&format!("local:other{index}")), value(index));
                state = state.with_memory(memory);
            }
            let (live, work) = crate::instrumentation::measure_deterministic_work(|| {
                liveness_preserved_between_points(start.path_link(), state.path_link(), &block)
            });
            assert_eq!(live, Some(true), "unrelated stores keep the block live");
            samples.push((size, work));
            let ended = state
                .clone()
                .with_memory(state.memory().without_local_block(&block));
            assert_eq!(
                liveness_preserved_between_points(start.path_link(), ended.path_link(), &block),
                Some(false),
                "the block's lifetime ended"
            );
        }
        let per_step = |(size, work): (usize, usize)| work / size;
        assert!(
            samples
                .iter()
                .all(|sample| per_step(*sample) == per_step(samples[0])),
            "the liveness walk is not linear in the steps between its points: {samples:?}"
        );
    }

    /// The route carrying a loadable fact across recorded effects to a later
    /// state reads the loadable facts filed under the base's block, not
    /// every proposition fact. Across the gate it never proved a fact
    /// another route had not, so this pins its miss: a stated fact at a
    /// state no effect connects is the one candidate it reads.
    #[test]
    fn carried_loadability_ignores_unrelated_loadable_facts() {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let loadable = |memory: &SymbolicMemory, base: Address| Proposition::MemoryLoadable {
                point: Default::default(),
                memory: memory.clone(),
                base,
                bytes: (OldMachineTerm::constant(4)).into(),
                wide: false,
            };
            // The queried state holds no target object, so no other
            // route carries the fact.
            let stated = SymbolicMemory::new().with_block("target", 4);
            let queried = SymbolicMemory::new();
            let facts = (0..size)
                .fold(PureFactContext::new(), |facts, index| {
                    facts.assume_proposition(loadable(&stated, cell(&format!("unrelated-{index}"))))
                })
                .assume_proposition(loadable(&stated, cell("target")));
            CARRIED_LOADABLE_VISITS.with(|visits| visits.set(0));
            let carried = facts.proves_atomic_without_search(&loadable(&queried, cell("target")));
            assert!(!carried, "no effect connects the two states");
            samples.push((size, CARRIED_LOADABLE_VISITS.with(std::cell::Cell::get)));
        }
        let (_, smallest) = samples[0];
        assert!(smallest > 0, "the carried route read no fact: {samples:?}");
        assert!(
            samples.iter().all(|(_, visits)| *visits == smallest),
            "carried loadability read unrelated loadable facts (size, facts read): {samples:?}"
        );
    }

    /// `memory_load_is_directly_unchanged` reads the effect facts filed
    /// under its `before` memory. It once scanned every proposition fact, so
    /// each load check after a long run of calls paid for every earlier
    /// call's effect summary. Its work must not grow with unrelated effects.
    #[test]
    fn a_direct_unchanged_check_ignores_unrelated_effect_facts() {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let target = cell("target");
            // A call stands between the states: the direct check cannot
            // match its havoc away, and only the call's effect summary, whose
            // one mutable range is in another object, shows the target cell
            // unchanged.
            let before = SymbolicMemory::new()
                .store(target.clone(), value(1))
                .with_block("call-havoc:0", 0);
            let after = before.clone().with_block("call-havoc:1", 0);
            let written = cell("written");
            assert!(!memories_directly_match_for_pointer_load(
                &before,
                &after,
                &target,
                &PureFactContext::new()
            ));
            let facts = (0..size).fold(PureFactContext::new(), |facts, index| {
                let base =
                    SymbolicMemory::new().store(cell(&format!("unrelated-{index}")), value(index));
                facts.assume_proposition(Proposition::MemoryEffectSummary {
                    before_point: Default::default(),
                    after_point: Default::default(),
                    before: base.clone(),
                    after: base
                        .clone()
                        .store(cell(&format!("unrelated-{index}")), value(index + 1)),
                    mutable_ranges: Vec::new(),
                })
            });
            let facts = facts.assume_proposition(Proposition::MemoryEffectSummary {
                before_point: Default::default(),
                after_point: Default::default(),
                before: before.clone(),
                after: after.clone(),
                mutable_ranges: vec![MemoryRange::new(
                    written.clone(),
                    OldMachineTerm::constant(0),
                    OldMachineTerm::constant(1),
                )],
            });
            DIRECT_UNCHANGED_VISITS.with(|visits| visits.set(0));
            let (unchanged, work) = crate::instrumentation::measure_deterministic_work(|| {
                memory_load_is_directly_unchanged(&before, &after, &target, LoadKind::Int32, &facts)
            });
            assert!(unchanged, "the summary's write misses the target cell");
            samples.push((
                size,
                work,
                DIRECT_UNCHANGED_VISITS.with(std::cell::Cell::get),
            ));
        }
        let (_, work, visits) = samples[0];
        assert!(visits > 0, "the check read no effect fact: {samples:?}");
        assert!(
            samples
                .iter()
                .all(|sample| (sample.1, sample.2) == (work, visits)),
            "a direct unchanged check grew with unrelated effect facts \
             (size, work, effect facts visited): {samples:?}"
        );
    }
}

#[test]
fn certified_scalar_store_equations_name_the_read_at_its_actual_width() {
    use crate::kernel::{ExecutionFacts, ExecutionPureFact};
    let _session = crate::kernel::VerificationSession::enter();
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let address = Address::symbolic(Variable(989_777));
        let before = SymbolicMemory::new();
        let one = crate::kernel::machine_integer::range::constant_word(format, &1.into()).unwrap();
        let term = OldMachineTerm::logical_machine_binary(
            format,
            crate::kernel::MachineBinaryOp::Add,
            OldMachineTerm::Variable(Variable(989_778)),
            one,
        );
        let value = match format {
            MachineIntegerType::Int32 => ProgramValue::Int32(term.clone()),
            MachineIntegerType::UInt32 => ProgramValue::UInt32(term.clone()),
            MachineIntegerType::Int64 => ProgramValue::Int64(term.clone()),
            MachineIntegerType::UInt64 => ProgramValue::UInt64(term.clone()),
            _ => unreachable!(),
        };
        let after = before.clone().store(address.clone(), value.clone());
        let named = crate::kernel::canonical_form_of_load(
            crate::kernel::intern_memory_ref(&after),
            address.clone(),
            LoadKind::of_value(&value).unwrap(),
        );
        let facts: ExecutionFacts = vec![ExecutionPureFact::certified_store(
            before,
            Default::default(),
            ProgramPoint::of_memory(&after),
            address,
            value,
            None,
        )]
        .into();
        let equations = certified_store_equations(&facts);
        assert_eq!(
            equations,
            vec![Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: if format == MachineIntegerType::UInt64 {
                        MachineIntegerType::Int64
                    } else {
                        format
                    },
                    relation: CompareRelation::Equal,
                    left: Box::new(named),
                    right: Box::new(term),
                },
                true
            )]
        );
        let Proposition::ConditionIs(condition, _) = &equations[0] else {
            unreachable!()
        };
        assert!(crate::kernel::condition_variable_widths(condition.old_form()).is_ok());
    }
}

/// A store equation admitted before any typed read of its cell still joins
/// the equality graph as a word read. Its read was named under the unrecorded
/// fallback width, which the graph does not register as a four-byte read, and
/// a later typed read of the same cell does not revisit a context that already
/// holds the equation. A read at an index equal to the stored one then missed
/// in that context, but not in one rebuilt from the same facts, so expanding
/// `arena_write` replayed `close()` against a context that knew less.
#[test]
fn a_store_equation_admitted_before_a_typed_read_joins_reads_at_equal_indexes() {
    use crate::kernel::{ExecutionFacts, ExecutionPureFact, PureFactContext};
    let _session = crate::kernel::VerificationSession::enter();
    let variable = |id| OldMachineTerm::Variable(Variable(id));
    let cell = |index| {
        Address::new(
            "array".into(),
            AddressOffset::scale_int32(variable(index), 4),
        )
    };
    let (stored, read, value) = (989_790, 989_791, 989_792);
    let before = SymbolicMemory::new().with_block("array", 4096);
    let after = before
        .clone()
        .store(cell(stored), ProgramValue::Int32(variable(value)));
    let facts: ExecutionFacts = vec![ExecutionPureFact::certified_store(
        before,
        Default::default(),
        ProgramPoint::of_memory(&after),
        cell(stored),
        ProgramValue::Int32(variable(value)),
        None,
    )]
    .into();
    let equations = certified_store_equations(&facts);
    // The incremental order: the step admits the store equation, the index
    // equality follows, and only then does a typed C read of the stored cell
    // record its width.
    let context = equations
        .into_iter()
        .fold(PureFactContext::new(), PureFactContext::assume_proposition)
        .assume_condition(
            OldConditionTerm::equal(variable(stored), variable(read)),
            true,
        );
    let after = crate::kernel::intern_memory(after);
    crate::kernel::eval::record_load_access_width(after.memory(), &cell(stored), 4);
    crate::kernel::eval::record_load_access_width(after.memory(), &cell(read), 4);
    let goal = Proposition::condition_is(
        OldConditionTerm::equal(
            crate::kernel::canonical_form_of_load(after, cell(read), LoadKind::Int32),
            variable(value),
        ),
        true,
    );
    assert!(context.contains_known(&goal));
}

#[cfg(test)]
mod store_equation_width_tests {
    use super::*;
    include!("../scaling_tests/kernel/memory_history/store_equation_width_tests.rs");
}

#[cfg(test)]
mod range_scan_accounting_tests {
    use super::*;
    include!("../scaling_tests/kernel/memory_history/range_scan_accounting_tests.rs");
}

#[cfg(test)]
mod retained_offset_evidence_tests {
    use super::*;
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelTermImport, KernelType, MachineBinaryOp,
        MachineOperandView, VerificationSession,
    };

    fn offset(value: &OldMachineTerm, width: i64) -> AddressOffset {
        let root = KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::Int32, value)
            .unwrap();
        AddressOffset::int32_scaled(
            MachineOperandView::Shared(&root).retain(MachineIntegerType::Int32),
            width,
        )
    }

    #[test]
    fn retained_offset_matching_keeps_native_value_rules() {
        let _session = VerificationSession::enter();
        let x = OldMachineTerm::Variable(Variable(1018801));
        let y = OldMachineTerm::Variable(Variable(1018802));
        let pairs = [
            (x.clone(), y.clone()),
            (
                OldMachineTerm::add(x.clone(), x.clone()),
                OldMachineTerm::add(y.clone(), y.clone()),
            ),
            (
                OldMachineTerm::add(x.clone(), 1u32.into()),
                OldMachineTerm::add(y.clone(), 1u32.into()),
            ),
            (OldMachineTerm::constant(1), OldMachineTerm::constant(2)),
        ];
        let contexts = [
            PureFactContext::new(),
            PureFactContext::new().assume_condition(OldConditionTerm::equal(x, y), true),
        ];
        for context in contexts {
            let _scope = context.enter_id_scope();
            for (left, right) in &pairs {
                let expected =
                    int32_values_proven_equal_for_memory_resolution(left, right, &context)
                        || explicit_atomic_equality_from_memory_derivations(left, right, &context);
                let (a, b) = (offset(left, 4), offset(right, 4));
                let exports = KernelTermExport::machine_export_count();
                assert_eq!(
                    pointer_offsets_match_from_memory_derivations(&a, &b, &context),
                    expected
                );
                assert!(!pointer_offsets_match_from_memory_derivations(
                    &a,
                    &offset(right, 8),
                    &context
                ));
                assert_eq!(KernelTermExport::machine_export_count(), exports);
            }
        }
    }

    #[test]
    fn retained_offset_read_evidence_keeps_exact_states_and_widths() {
        let _session = VerificationSession::enter();
        let read = Address::new("retained-offset-source".into(), AddressOffset::constant(0));
        crate::kernel::eval::declare_load_access_width(&read, 4);
        let base = SymbolicMemory::new().with_block("retained-offset-source", 16);
        let facts = PureFactContext::new();
        let havoc = |id| {
            base.clone().with_call_memory_havoc(
                Variable(id),
                &[MemoryRange::new(
                    read.offset_by_bytes(8),
                    0u32.into(),
                    8u32.into(),
                )],
                &facts,
                None,
            )
        };
        let left = havoc(1018811);
        let right = havoc(1018812);
        let load = |memory: &SymbolicMemory| {
            crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(&(crate::kernel::intern_memory_ref(memory))),
                read.clone(),
                LoadKind::Int32,
            )
        };
        let (a, b) = (offset(&load(&left), 4), offset(&load(&right), 4));
        let exports = KernelTermExport::machine_export_count();
        let evidence =
            with_extended_dag_bridging(|| address_offset_equality_evidence(&a, &b, &facts))
                .expect("same source cell");
        assert!(evidence.checks(&a, &b, &facts));
        assert!(!evidence.checks(&a, &offset(&load(&right), 8), &facts));
        let changed = right.store(read.clone(), ProgramValue::Int32(7u32.into()));
        let changed = offset(&load(&changed), 4);
        assert!(!evidence.checks(&a, &changed, &facts));
        assert!(
            with_extended_dag_bridging(|| address_offset_equality_evidence(&a, &changed, &facts))
                .is_none()
        );
        let arithmetic = offset(
            &OldMachineTerm::add(OldMachineTerm::Variable(Variable(1018813)), 1u32.into()),
            4,
        );
        assert!(!evidence.checks(&a, &arithmetic, &facts));
        assert!(address_offset_equality_evidence(&a, &arithmetic, &facts).is_none());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    mod scaling_tests {
        use super::*;
        include!("../scaling_tests/kernel/memory_history/retained_offset_evidence_tests.rs");
    }
}

#[cfg(test)]
mod retained_boolean_dependency_tests {
    use super::*;

    #[test]
    fn common_boolean_memories_keep_state_order_and_call_opacity() {
        use crate::kernel::{BooleanOperandView, KernelTermImport, SharedPureApplication};
        let first = crate::kernel::intern_memory(SymbolicMemory::new());
        let second = crate::kernel::intern_memory(
            SymbolicMemory::new().with_block(AddressBase::Concrete("boolean_memory".into()), 8),
        );
        let read = |memory| {
            crate::kernel::OldMachineTerm::read_named(
                memory,
                Address::symbolic(Variable(970_010)),
                LoadKind::Int32,
            )
        };
        let source = OldConditionTerm::BoolEqual(
            Box::new(OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(read(ProgramPoint::at(&first))),
                right: Box::new(read(ProgramPoint::at(&second))),
            }),
            Box::new(OldConditionTerm::BoolApplication(
                SharedPureApplication::intern(
                    "opaque_memory_dependency".into(),
                    vec![PureFunctionArgument::Value(ProgramValue::Int32(read(
                        ProgramPoint::at(&second),
                    )))],
                ),
            )),
        );
        let root = KernelTermImport::default().condition(&source);
        let mut native = Vec::new();
        let mut common = Vec::new();
        collect_condition_memories(&source, &mut native);
        collect_condition_operand_memories(BooleanOperandView::Shared(&root), &mut common);
        assert_eq!(native, vec![first, second]);
        assert_eq!(common, native);
    }
}

#[cfg(test)]
mod common_boolean_transport_tests {
    use super::*;
    use crate::kernel::{KernelTermExport, KernelTermImport};

    #[test]
    fn common_boolean_transport_matches_native_states_and_constructors() {
        let _session = crate::kernel::VerificationSession::enter();
        let before = SymbolicMemory::new()
            .with_block("bool-transport", 8)
            .with_block("other-transport", 4);
        let memory = crate::kernel::intern_memory(before.clone());
        let address = SymbolicMemory::global_pointer("bool-transport");
        let after = before.store(
            SymbolicMemory::global_pointer("other-transport"),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        );
        for source in [
            OldConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: crate::kernel::OverflowOperation::Add,
                left: Box::new(crate::kernel::OldMachineTerm::read_named(
                    ProgramPoint::at(&memory),
                    address.clone(),
                    LoadKind::Int32,
                )),
                right: Box::new(OldMachineTerm::constant(1)),
            },
            OldConditionTerm::PointerEqual(
                Box::new(Pointer::new(
                    Address::new(
                        AddressBase::Symbolic(Variable(972_003)),
                        AddressOffset::scaled_int32_node(
                            crate::kernel::OldMachineTerm::read_named(
                                ProgramPoint::at(&memory),
                                address.clone(),
                                LoadKind::Int32,
                            ),
                            4,
                        ),
                    ),
                    ProgramType::Int32Pointer,
                )),
                Box::new(Pointer::new(Address::null(), ProgramType::Int32Pointer)),
            ),
            OldConditionTerm::AddressEqual(
                Box::new(Address::new(
                    AddressBase::Symbolic(Variable(972_003)),
                    AddressOffset::scaled_int32_node(
                        crate::kernel::OldMachineTerm::read_named(
                            ProgramPoint::at(&memory),
                            address.clone(),
                            LoadKind::Int32,
                        ),
                        4,
                    ),
                )),
                Box::new(Address::null()),
            ),
            OldConditionTerm::AddressOffsetEqual(
                Box::new(AddressOffset::raw_add(
                    AddressOffset::constant(0),
                    AddressOffset::scaled_int32_node(
                        crate::kernel::OldMachineTerm::read_named(
                            ProgramPoint::at(&memory),
                            address.clone(),
                            LoadKind::Int32,
                        ),
                        4,
                    ),
                )),
                Box::new(AddressOffset::scaled_int64_node(
                    OldMachineTerm::Variable(Variable(972_002)),
                    8,
                    true,
                )),
            ),
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(crate::kernel::OldMachineTerm::read_named(
                    ProgramPoint::at(&memory),
                    address,
                    LoadKind::Int32,
                )),
                right: Box::new(OldMachineTerm::constant(0)),
            },
            OldConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(Variable(972_001))),
                right: Box::new(OldMachineTerm::Variable(Variable(972_001))),
            },
        ] {
            let root = KernelTermImport::default().condition(&source);
            let expected = transport_framed_atomic_condition(
                &source,
                &crate::kernel::ProgramPoint::of_memory(&after),
                None,
            )
            .unwrap();
            let actual = transport_framed_common_condition(
                &root,
                &crate::kernel::ProgramPoint::of_memory(&after),
                None,
            )
            .unwrap();
            assert_eq!(KernelTermExport::condition(&actual).unwrap(), expected);
        }
    }

    /// A wide pointer's count transports as a numeric child: an equality of
    /// two slices crosses a frame that leaves their counts unchanged, where
    /// it was refused before (`design/rust-slice-values.md`, step 2b-ii-b).
    #[test]
    fn framed_transport_carries_a_slice_count() {
        let _session = crate::kernel::VerificationSession::enter();
        let wide = |pointer, count| {
            Pointer::new(
                Address::symbolic(Variable(pointer)),
                ProgramType::UInt8Pointer,
            )
            .with_element_count(OldMachineTerm::Variable(Variable(count)))
        };
        let source = OldConditionTerm::PointerEqual(
            Box::new(wide(972_010, 972_011)),
            Box::new(wide(972_012, 972_013)),
        );
        assert_eq!(
            transport_framed_atomic_condition(
                &source,
                &crate::kernel::ProgramPoint::of_memory(&SymbolicMemory::new()),
                None
            ),
            Some(source)
        );
    }

    /// A slice-valued pure application's count transports as its thin
    /// part's application block does: unchanged, as a numeric child of the
    /// slice (`design/rust-slice-values.md`, step 2b-iii-b-ii).
    #[test]
    fn framed_transport_carries_a_slice_application_count() {
        let _session = crate::kernel::VerificationSession::enter();
        let application = crate::kernel::SharedPureApplication::intern(
            "slice_of".into(),
            vec![crate::kernel::PureFunctionArgument::Value(
                ProgramValue::Int32(OldMachineTerm::Variable(Variable(972_020))),
            )],
        );
        let slice = crate::kernel::spec::pure_slice_application_value(
            &application,
            crate::kernel::SliceElement::UInt8,
            ProgramType::SlicePointer(crate::kernel::SliceElement::UInt8),
        );
        let other = Pointer::new(
            Address::symbolic(Variable(972_021)),
            ProgramType::UInt8Pointer,
        )
        .with_element_count(OldMachineTerm::Variable(Variable(972_022)));
        let after = crate::kernel::ProgramPoint::of_memory(&SymbolicMemory::new());
        let source = OldConditionTerm::PointerEqual(Box::new(slice.clone()), Box::new(other));
        assert_eq!(
            transport_framed_atomic_condition(&source, &after, None),
            Some(source)
        );
        let count = slice.len().expect("a slice has a count");
        assert_eq!(
            transport_framed_atomic_bitvector(count, &after, None).as_ref(),
            Some(count)
        );
    }

    #[test]
    fn common_boolean_transport_keeps_composite_and_load_refusals() {
        let memory = crate::kernel::intern_memory(SymbolicMemory::new());
        for source in [
            OldConditionTerm::Constant(true),
            OldConditionTerm::Variable(Variable(972_002)),
            OldConditionTerm::BoolEqual(
                Box::new(OldConditionTerm::Constant(true)),
                Box::new(OldConditionTerm::Constant(false)),
            ),
            OldConditionTerm::boolean_cell_read(
                crate::kernel::ProgramPoint::at(&memory),
                Address::symbolic(Variable(972_003)),
            ),
        ] {
            assert!(
                transport_framed_atomic_condition(
                    &source,
                    &crate::kernel::ProgramPoint::of_memory(&SymbolicMemory::new()),
                    None
                )
                .is_none()
            );
            let root = KernelTermImport::default().condition(&source);
            assert!(
                transport_framed_common_condition(
                    &root,
                    &crate::kernel::ProgramPoint::of_memory(&SymbolicMemory::new()),
                    None
                )
                .is_none()
            );
        }
    }
}

#[cfg(test)]
mod common_boolean_read_tests {
    use super::*;
    #[test]
    fn boolean_reads_use_the_same_state_candidates_as_byte_reads() {
        let _session = crate::kernel::VerificationSession::enter();
        let before = SymbolicMemory::new()
            .with_block("bool-memory-index", 4)
            .with_block("bool-memory-other", 4);
        let after = before.clone().store(
            SymbolicMemory::global_pointer("bool-memory-other"),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        );
        let old = crate::kernel::intern_memory(before);
        let new = crate::kernel::intern_memory(after);
        let source = OldConditionTerm::boolean_cell_read(
            crate::kernel::ProgramPoint::at(&new.clone()),
            Address::new(
                AddressBase::Symbolic(Variable(999370)),
                AddressOffset::scaled_int32_node(
                    crate::kernel::OldMachineTerm::read_named(
                        ProgramPoint::at(&old),
                        SymbolicMemory::global_pointer("bool-memory-index"),
                        LoadKind::Int32,
                    ),
                    4,
                ),
            ),
        );
        let root = crate::kernel::KernelTermImport::default().condition(&source);
        let mut expected = Vec::new();
        let mut actual = Vec::new();
        collect_condition_memories(&source, &mut expected);
        collect_condition_operand_memories(
            crate::kernel::BooleanOperandView::Shared(&root),
            &mut actual,
        );
        assert_eq!(actual, expected);
        // The machine-read candidate contributes its own state. Its address
        // is checked separately by the load transport rule.
        assert_eq!(actual, vec![new]);
    }
}

#[test]
fn atomic_canonicalization_keeps_two_written_read_points() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = SymbolicMemory::new();
    let pointer = Address::symbolic(Variable(989_790));
    let first = ProgramPoint::starting_at(&memory).for_exact_read();
    let second = ProgramPoint::starting_at(&memory).for_exact_read();
    let kind = LoadKind::Bits64;
    let first = crate::kernel::OldMachineTerm::read_named(first, pointer.clone(), kind);
    let second = crate::kernel::OldMachineTerm::read_named(second, pointer, kind);
    assert_ne!(first, second);
    assert_eq!(canonicalize_atomic_loads(&first), first);
    assert_eq!(canonicalize_atomic_loads(&second), second);
    assert_eq!(crate::kernel::canonical_term(&first), first);
    assert_eq!(crate::kernel::canonical_term(&second), second);
}

#[test]
fn the_equation_for_an_indexed_store_names_its_written_point() {
    let _session = crate::kernel::VerificationSession::enter();
    let slot = SymbolicMemory::local_pointer("stored_equation_word");
    let before = ExecutionState::new().with_memory(
        SymbolicMemory::new().with_declared_scalar_block(slot.base.clone(), 8, ProgramType::UInt64),
    );
    let value = ProgramValue::UInt64(OldMachineTerm::Variable(Variable(989_793)));
    let after = before
        .clone()
        .with_memory(before.memory().clone().store(slot.clone(), value.clone()));
    let point = after.program_point();
    let fact = ExecutionPureFact::certified_store(
        before.memory().clone(),
        before.memory_point(),
        point.clone(),
        slot.clone(),
        value,
        None,
    );
    let Some((OldConditionTerm::Compare { left, .. }, true)) = fact
        .certified_store_equation()
        .and_then(|fact| fact.old_condition())
    else {
        panic!("certified store equality");
    };
    let OldMachineTerm::MemoryLoad(read, address, LoadKind::Bits64) = left.as_ref() else {
        panic!("store equation's typed read");
    };
    assert_eq!(address.as_ref(), &slot);
    assert_eq!(read.read_version_id(), point.id());
}
