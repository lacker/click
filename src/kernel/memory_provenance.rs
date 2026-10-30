use super::primitives::*;
use super::reasoning::*;
use super::resource_tracker::cell_source::*;
use crate::kernel::ExecutionFactSource;
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::{CompareRelation, MachineIntegerType};
use std::collections::BTreeSet;

/// Results retained from the actual selected read query, never reconstructed
/// by the terminal renderer under a different arena or assumption context.
#[derive(Clone)]
pub(crate) struct ReadResolutionDiagnostic {
    pub read: Bitvector32Term,
    pub producer: SharedCMemory,
    pub stopped_at: Option<SharedCMemory>,
    pub reason: &'static str,
    pub recovered: Option<CValue>,
    pub expected: Bitvector32Term,
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
    pub start: SharedCMemory,
    pub pointer: Pointer,
    pub bytes: u32,
    pub stopped_at: SharedCMemory,
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

pub(crate) fn take_transport_cell_walk_diagnostics() -> Vec<TransportCellWalkDiagnostic> {
    TRANSPORT_CELL_WALKS.with(|slot| {
        slot.borrow_mut()
            .take()
            .map(|capture| capture.walks)
            .unwrap_or_default()
    })
}

pub(in crate::kernel) fn record_transport_cell_walk(
    memory: &SharedCMemory,
    pointer: &Pointer,
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
                CellWalkStop::CommonSnapshot => "common snapshot reached",
                CellWalkStop::RetainedValue => "retained typed value before cache forgetting",
                CellWalkStop::OldestRecorded => "oldest recorded snapshot reached",
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
    match (left, right) {
        (AlgebraicValue::C(left), AlgebraicValue::C(right)) => {
            // A resource index observes an integer's numeric value. Matching
            // indices neither copies a C word nor transports its hidden record.
            c_values_proven_equal_for_memory_resolution(
                left.numeric_value(),
                right.numeric_value(),
                assumptions,
            )
        }
        (AlgebraicValue::Algebraic(left), AlgebraicValue::Algebraic(right)) => {
            left.algebraic_type == right.algebraic_type
                && (left == right
                    || assumptions.proves_exact(&Proposition::Equal(
                        Term::Algebraic(left.clone()),
                        Term::Algebraic(right.clone()),
                    ))
                    || assumptions.proves_exact(&Proposition::Equal(
                        Term::Algebraic(right.clone()),
                        Term::Algebraic(left.clone()),
                    ))
                    || assumptions.decide(&ConditionTerm::AlgebraicEqual(
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
pub(crate) fn instance_arguments_proven_equal(
    left: &AlgebraicValue,
    right: &AlgebraicValue,
    assumptions: &PureFactContext,
) -> bool {
    if let (AlgebraicValue::C(left), AlgebraicValue::C(right)) = (left, right)
        && let (CValue::Pointer(left), CValue::Pointer(right)) =
            (left.numeric_value(), right.numeric_value())
    {
        return (assumptions.pointer_designations_match(left, right)
            || assumptions.designations_equal(left.designation(), right.designation()))
            && crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
                left.pointer(),
                right.pointer(),
                assumptions,
            );
    }
    resource_arguments_proven_equal(left, right, assumptions)
}

pub(crate) fn canonical_c_memory_for_pointer_load(memory: &CMemory, pointer: &Pointer) -> CMemory {
    canonical_memory_for_pointer_load(memory, pointer)
}

/// Constructs the pointer-observable snapshot used by atomic-load
/// canonicalization and retains the exact producer-known projection edge.
/// The edge is separate from the ordinary memory DAG because the interned
/// result may be shared by projections of several source snapshots.
/// The memory a load of a value of `bytes` at `pointer`, an enum's or a
/// type parameter's, names: the
/// point the cell was last written, projected to the cell, as an integer
/// load's canonical form names its cell. Two loads of one unwritten cell at
/// different points are then one term.
pub(crate) fn canonical_value_load_memory(
    memory: &SharedCMemory,
    pointer: &Pointer,
    bytes: u32,
) -> SharedCMemory {
    let version = cell_version_point(memory, pointer, bytes);
    let named = canonical_projected_load_memory(version.as_ref().unwrap_or(memory), pointer);
    record_value_load_origin(memory, &named, pointer, bytes);
    named
}

fn canonical_projected_load_memory(source: &SharedCMemory, pointer: &Pointer) -> SharedCMemory {
    let projected =
        crate::kernel::intern_c_memory(canonical_c_memory_for_pointer_load(source, pointer));
    record_canonical_load_projection(source, &projected, pointer);
    projected
}

/// Checks whether two resource forms denote the same resource using only
/// exact facts and the bounded memory-resolution relation. This is intended
/// for certificate validation: it does not search for containment or separation.
pub(crate) fn c_resources_directly_match(
    left: &CResource,
    right: &CResource,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    let values_match = |left: &CValue, right: &CValue| match (left, right) {
        (CValue::Void, CValue::Void) => true,
        (CValue::Int32(left), CValue::Int32(right)) => crate::instrumentation::measure_operation(
            "kernel",
            "resource context equality",
            "resource direct match: bitvector value",
            || int32_values_proven_equal_for_memory_resolution(left, right, assumptions),
        ),
        (CValue::UInt8(left), CValue::UInt8(right)) => crate::instrumentation::measure_operation(
            "kernel",
            "resource context equality",
            "resource direct match: bitvector value",
            || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions),
        ),
        (CValue::Int8(left), CValue::Int8(right)) => crate::instrumentation::measure_operation(
            "kernel",
            "resource context equality",
            "resource direct match: bitvector value",
            || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions),
        ),
        (CValue::Int16(left), CValue::Int16(right))
        | (CValue::UInt16(left), CValue::UInt16(right)) => {
            crate::instrumentation::measure_operation(
                "kernel",
                "resource context equality",
                "resource direct match: bitvector value",
                || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions),
            )
        }
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            crate::instrumentation::measure_operation(
                "kernel",
                "resource context equality",
                "resource direct match: pointer value",
                || {
                    assumptions.pointer_designations_match(left, right)
                        && pointers_match_for_resource_check(left, right, assumptions)
                },
            )
        }
        _ => false,
    };
    match (left, right) {
        (CResource::Memory(left), CResource::Memory(right)) => {
            left == right
                || (((!left.typed_carrier
                    || assumptions.access_designations_match(left.access_designation(), right))
                    && (!right.typed_carrier
                        || assumptions
                            .access_designations_match(right.access_designation(), left)))
                    && left.int32_bounds().is_some()
                    && right.int32_bounds().is_some()
                    && crate::instrumentation::measure_operation(
                        "kernel",
                        "resource context equality",
                        "resource memory match: width",
                        || left.element_width() == right.element_width(),
                    )
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
        (CResource::Instance(left), CResource::Instance(right)) => {
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
                    .all(|(a, b)| resource_arguments_proven_equal(a, b, assumptions))
        }
        (
            CResource::Composite {
                name: left_name,
                arguments: left_arguments,
            },
            CResource::Composite {
                name: right_name,
                arguments: right_arguments,
            },
        )
        | (
            CResource::Token {
                name: left_name,
                arguments: left_arguments,
            },
            CResource::Token {
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
                        (AlgebraicValue::C(left), AlgebraicValue::C(right)) => {
                            values_match(left, right)
                        }
                        _ => resource_arguments_proven_equal(left, right, assumptions),
                    })
        }
        _ => false,
    }
}

fn bitvectors_match_for_resource_check(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    // Memory-range endpoints are int32 values. Their equality does not
    // identify byte offsets or grant access to either range.
    assumptions.int32_values_known_equal(left, right)
}

pub(in crate::kernel) fn pointer_offsets_match_from_memory_derivations(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
            pointer_offsets_match_from_memory_derivations(left_a, right_a, assumptions)
                && pointer_offsets_match_from_memory_derivations(left_b, right_b, assumptions)
        }
        (
            PointerOffsetTerm::Int32Scaled {
                value: left,
                byte_width: left_width,
            },
            PointerOffsetTerm::Int32Scaled {
                value: right,
                byte_width: right_width,
            },
        ) => {
            left_width == right_width
                && (assumptions.int32_values_known_equal(left, right)
                    || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
                    || explicit_atomic_equality_from_memory_derivations(left, right, assumptions))
        }
        _ => false,
    }
}

fn pointer_offsets_match_for_resource_check(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
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
    let transported_matches = |offset: &PointerOffsetTerm, target: &PointerOffsetTerm| {
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
                        &memory,
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
        || c_pointer_offsets_proven_equal_for_effect(left, right, assumptions),
    )
}

fn pointers_match_for_resource_check(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    if left.block == right.block
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
/// produced from different memory snapshots compare equal when their
/// difference is representational.
pub(crate) fn canonical_c_memory_deep(memory: &CMemory) -> CMemory {
    // Assumption-free and deterministic; keyed by interned snapshot identity.
    let key = crate::kernel::intern_c_memory_ref(memory);
    if let Some(hit) = DEEP_MEMORY_CACHE.with(|cache| cache.borrow().get(&key).cloned()) {
        return hit;
    }
    let result = canonical_c_memory_deep_uncached(memory);
    DEEP_MEMORY_CACHE.with(|cache| cache.borrow_mut().insert(key, result.clone()));
    result
}

fn canonical_c_memory_deep_uncached(memory: &CMemory) -> CMemory {
    let mut canonical = memory.clone();
    let cells = canonical.cells.map_cells_preserving_runs(
        |pointer, value| {
            let key = canonicalize_pointer_loads(pointer);
            let value = match value {
                CValue::PointerInteger(record) => CValue::PointerInteger(PointerIntegerValue {
                    kind: record.kind.clone(),
                    numeric: Box::new(match record.numeric.as_ref() {
                        CValue::Int64(t) => CValue::Int64(canonicalize_atomic_loads(t)),
                        CValue::UInt64(t) => CValue::UInt64(canonicalize_atomic_loads(t)),
                        _ => unreachable!("LP64 representation"),
                    }),
                    pointer: Box::new(record.pointer.map_addresses(canonicalize_pointer_loads)),
                }),
                CValue::Parameter(term) => CValue::Parameter(term.clone()),
                CValue::Void => CValue::Void,
                CValue::Bool(term) => CValue::Bool(canonicalize_atomic_loads(term)),
                CValue::Int8(term) => CValue::Int8(canonicalize_atomic_loads(term)),
                CValue::Int16(term) => CValue::Int16(canonicalize_atomic_loads(term)),
                CValue::Int32(term) => CValue::Int32(canonicalize_atomic_loads(term)),
                CValue::UInt8(term) => CValue::UInt8(canonicalize_atomic_loads(term)),
                CValue::UInt16(term) => CValue::UInt16(canonicalize_atomic_loads(term)),
                CValue::UInt32(term) => CValue::UInt32(canonicalize_atomic_loads(term)),
                CValue::Int64(term) => CValue::Int64(canonicalize_atomic_loads(term)),
                CValue::UInt64(term) => CValue::UInt64(canonicalize_atomic_loads(term)),
                CValue::Int128(term) => CValue::Int128(canonicalize_atomic_loads(term)),
                CValue::UInt128(term) => CValue::UInt128(canonicalize_atomic_loads(term)),
                CValue::Float32(term) => CValue::Float32(canonicalize_atomic_loads(term)),
                CValue::Float64(term) => CValue::Float64(canonicalize_atomic_loads(term)),
                CValue::Pointer(pointer) => CValue::Pointer(
                    pointer
                        .map_addresses(canonicalize_pointer_loads)
                        .with_pointee_volatile(false)
                        .with_pointee_constant(false),
                ),
            };
            (key, value)
        },
        |_| None,
        |run| {
            // Numeric Load/Copy slots are minted by canonical_form_of_load,
            // which returns a load variable for every typed memory load.
            // Atomic-load canonicalization leaves those variables unchanged.
            // A canonical base plus a constant slot shift is canonical too:
            // slot_pointer and canonicalize_pointer_loads both use the same
            // folding PointerOffsetTerm::add constructor. Source cells and
            // derivation edges can vary across the run; neither is sampled.
            matches!(
                run.value_mode(),
                crate::kernel::primitives::RunValueMode::Load
                    | crate::kernel::primitives::RunValueMode::Copy { .. }
            ) && matches!(
                run.element_type(),
                CType::Int8
                    | CType::Int16
                    | CType::Int32
                    | CType::Int64
                    | CType::Int128
                    | CType::UInt8
                    | CType::UInt16
                    | CType::UInt32
                    | CType::UInt64
                    | CType::UInt128
                    | CType::Float32
                    | CType::Float64
            ) && canonicalize_pointer_loads(run.base()) == *run.base()
        },
    );
    canonical.cells = std::sync::Arc::new(cells);
    let union_cells = std::mem::take(&mut canonical.union_cells);
    for ((pointer, c_type), value) in union_cells.iter() {
        let key = canonicalize_pointer_loads(pointer);
        let value = match value {
            CValue::PointerInteger(record) => CValue::PointerInteger(PointerIntegerValue {
                kind: record.kind.clone(),
                numeric: Box::new(match record.numeric.as_ref() {
                    CValue::Int64(t) => CValue::Int64(canonicalize_atomic_loads(t)),
                    CValue::UInt64(t) => CValue::UInt64(canonicalize_atomic_loads(t)),
                    _ => unreachable!("LP64 representation"),
                }),
                pointer: Box::new(record.pointer.map_addresses(canonicalize_pointer_loads)),
            }),
            CValue::Parameter(term) => CValue::Parameter(term.clone()),
            CValue::Void => CValue::Void,
            CValue::Bool(term) => CValue::Bool(canonicalize_atomic_loads(term)),
            CValue::Int8(term) => CValue::Int8(canonicalize_atomic_loads(term)),
            CValue::Int16(term) => CValue::Int16(canonicalize_atomic_loads(term)),
            CValue::Int32(term) => CValue::Int32(canonicalize_atomic_loads(term)),
            CValue::UInt8(term) => CValue::UInt8(canonicalize_atomic_loads(term)),
            CValue::UInt16(term) => CValue::UInt16(canonicalize_atomic_loads(term)),
            CValue::UInt32(term) => CValue::UInt32(canonicalize_atomic_loads(term)),
            CValue::Int64(term) => CValue::Int64(canonicalize_atomic_loads(term)),
            CValue::UInt64(term) => CValue::UInt64(canonicalize_atomic_loads(term)),
            CValue::Int128(term) => CValue::Int128(canonicalize_atomic_loads(term)),
            CValue::UInt128(term) => CValue::UInt128(canonicalize_atomic_loads(term)),
            CValue::Float32(term) => CValue::Float32(canonicalize_atomic_loads(term)),
            CValue::Float64(term) => CValue::Float64(canonicalize_atomic_loads(term)),
            CValue::Pointer(pointer) => CValue::Pointer(
                pointer
                    .map_addresses(canonicalize_pointer_loads)
                    .with_pointee_volatile(false)
                    .with_pointee_constant(false),
            ),
        };
        std::sync::Arc::make_mut(&mut canonical.union_cells).insert((key, *c_type), value);
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
fn cell_version_point(
    memory: &SharedCMemory,
    pointer: &Pointer,
    bytes: u32,
) -> Option<SharedCMemory> {
    crate::kernel::resource_tracker::last_same_point(
        crate::kernel::resource_tracker::Resource::Cell { pointer, bytes },
        &crate::kernel::resource_tracker::ProgramPoint::at(memory),
    )
    .map(|point| point.snapshot().clone())
}

/// Deep-canonical memory equality; see [`canonical_c_memory_deep`].
pub(crate) fn c_memories_canonically_equal(left: &CMemory, right: &CMemory) -> bool {
    left == right || canonical_c_memory_deep(left) == canonical_c_memory_deep(right)
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
    EqualResolvedValue(CValue),
    LeftRetainsRightRead,
    RightRetainsLeftRead,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum AtomicMemoryLoadEqualityEvidence {
    SameCell(MemoryDagLoadEqualityEvidence),
    /// One or both load endpoints are pointer-observable canonical
    /// projections. The projection edge is producer-known provenance; the
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
    pub(super) source: SharedCMemory,
    pub(super) projected: SharedCMemory,
    pub(super) pointer: Pointer,
}

impl CanonicalLoadProjectionEvidence {
    fn for_endpoint(projected: &SharedCMemory, pointer: &Pointer) -> Option<Self> {
        canonical_load_projection_source(projected, pointer).map(|source| Self {
            source,
            projected: projected.clone(),
            pointer: pointer.clone(),
        })
    }

    pub(super) fn checks(&self, projected: &SharedCMemory, pointer: &Pointer) -> bool {
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
    left: Bitvector32Term,
    right: Bitvector32Term,
    evidence: CheckedLoadEqualityEvidence,
}

/// A bounded candidate path through aliases indexed under the endpoints.
/// Each retained edge is checked against its exact named premise on checking.
fn selected_pointer_alias_path(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> Option<Vec<(Pointer, Pointer)>> {
    let equal = |first: &Pointer, second: &Pointer| {
        first == second
            || assumptions.proves_exact(&Proposition::ConditionIs(
                ConditionTerm::pointer_equal(first.clone(), second.clone()),
                true,
            ))
            || assumptions.proves_exact(&Proposition::ConditionIs(
                ConditionTerm::pointer_equal(second.clone(), first.clone()),
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
    /// recorded origin snapshots are structurally identical at that cell.
    /// Keeping both endpoints and the selected offset proof makes this a
    /// finite checked path rather than a request to rediscover pointer
    /// equality during proof-object validation.
    OriginDirectSnapshot {
        left: OriginLoadEndpoint,
        right: OriginLoadEndpoint,
        offset: PointerOffsetCongruenceEvidence,
    },
    /// Equal-width scalar reads at one execution or explicitly named snapshot,
    /// with exact pointer equality retained as their address witness. The source load
    /// names remain distinct, so explicit proof rewrites keep their addresses.
    OriginAliasedSnapshot {
        left: OriginLoadEndpoint,
        right: OriginLoadEndpoint,
        alias: Box<Proposition>,
        alias_path: Option<Vec<(Pointer, Pointer)>>,
        snapshots: Option<Box<CheckedLoadEquality>>,
        /// Named endpoints use only a shared defining snapshot, never a
        /// first-observed origin or a call-event correspondence.
        named_snapshot: bool,
    },
    /// The two source-level load terms meet along the recorded memory DAG
    /// when viewed at their original execution snapshots.
    OriginMemoryDag {
        left: OriginLoadEndpoint,
        right: OriginLoadEndpoint,
        equality: AtomicMemoryLoadEqualityEvidence,
    },
    /// One exact effect-summary fact connects the two original snapshots,
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
    memory: SharedCMemory,
    pointer: Pointer,
    kind: LoadKind,
}

fn origin_load_width(term: &Bitvector32Term) -> Option<u32> {
    match term {
        Bitvector32Term::Variable(variable) => {
            crate::kernel::eval::registered_load_bytes_for_variable(variable)
        }
        Bitvector32Term::MemoryLoad(memory, pointer, kind) => Some(
            crate::kernel::load_term_access_width(memory, pointer, *kind),
        ),
        _ => None,
    }
}

impl OriginLoadEndpoint {
    fn for_term(term: &Bitvector32Term) -> Option<Self> {
        let (memory, pointer, kind) = match term {
            Bitvector32Term::MemoryLoad(memory, pointer, kind) => {
                (memory.clone(), pointer.as_ref().clone(), *kind)
            }
            Bitvector32Term::Variable(variable) => {
                let (memory, pointer) =
                    crate::kernel::eval::registered_load_origin_for_variable(variable)?;
                let kind = crate::kernel::eval::registered_load_kind_for_variable(variable)?;
                (memory, pointer, kind)
            }
            _ => return None,
        };
        Some(Self {
            memory,
            pointer,
            kind,
        })
    }

    /// The snapshot explicitly named by a term or its registered defining load.
    /// Unlike an observation origin, this identity is independent of which
    /// execution arm first observed a load variable.
    fn for_named_term(term: &Bitvector32Term) -> Option<Self> {
        match term {
            Bitvector32Term::Variable(variable) => Self::for_term(
                &crate::kernel::eval::registered_load_term_for_variable(variable)?,
            ),
            _ => Self::for_term(term),
        }
    }

    /// The access width a walk from this endpoint uses.
    fn bytes(&self) -> u32 {
        crate::kernel::load_term_access_width(&self.memory, &self.pointer, self.kind)
    }

    fn matches_term(&self, term: &Bitvector32Term) -> bool {
        Self::for_term(term).as_ref() == Some(self)
    }

    fn as_term(&self) -> Bitvector32Term {
        Bitvector32Term::MemoryLoad(
            self.memory.clone(),
            Box::new(self.pointer.clone()),
            self.kind,
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CheckedCallLoadEqualityEvidence {
    event: crate::kernel::proof::CheckedCallEvent,
    pointer: Pointer,
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
        BTreeSet<(Bitvector32Term, Bitvector32Term)>,
    > = const { std::cell::RefCell::new(BTreeSet::new()) };
}

struct CheckedOriginLoadEqualityGuard {
    query: (Bitvector32Term, Bitvector32Term),
}

impl CheckedOriginLoadEqualityGuard {
    fn enter(left: &Bitvector32Term, right: &Bitvector32Term) -> Option<Self> {
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
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> Option<CheckedCallLoadEqualityEvidence> {
    let (
        Bitvector32Term::MemoryLoad(left_memory, left_pointer, left_kind),
        Bitvector32Term::MemoryLoad(right_memory, right_pointer, right_kind),
    ) = (left, right)
    else {
        return None;
    };
    if left_pointer != right_pointer || left_kind != right_kind {
        return None;
    }
    let left = memory_dag_cell_source(
        left_memory,
        left_pointer,
        crate::kernel::load_term_access_width(left_memory, left_pointer, *left_kind),
        assumptions,
        true,
    )?;
    let right = memory_dag_cell_source(
        right_memory,
        right_pointer,
        crate::kernel::load_term_access_width(right_memory, right_pointer, *right_kind),
        assumptions,
        true,
    )?;
    if !left.has_only_typed_hops()
        || !right.has_only_typed_hops()
        || !matches!(
            left.node().derivation().as_deref(),
            Some(CMemoryDerivation::CallHavoc { .. })
        )
        || !matches!(
            right.node().derivation().as_deref(),
            Some(CMemoryDerivation::CallHavoc { .. })
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
                Some(CMemoryDerivation::CallHavoc {
                    variable: left_variable,
                    mutable_ranges: left_ranges,
                    ..
                }),
                Some(CMemoryDerivation::CallHavoc {
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
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    with_extended_dag_bridging(|| {
        checked_call_load_equality_evidence(left, right, assumptions).is_some()
    })
}

impl CheckedLoadEquality {
    fn new(
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        Self::new_with_canonical_fallback(left, right, assumptions, true)
    }

    fn new_with_canonical_fallback(
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        assumptions: &PureFactContext,
        allow_canonical_fallback: bool,
    ) -> Option<Self> {
        if !matches!(left, Bitvector32Term::MemoryLoad(_, _, _))
            || !matches!(right, Bitvector32Term::MemoryLoad(_, _, _))
        {
            return None;
        }
        // Prefer the named-memory DAG: its work is proportional to the two
        // selected derivation paths. Deep canonicalization is a complete
        // structural fallback, but can walk unrelated snapshot cells.
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
            && !crate::kernel::reasoning::load_equality_refuted_by_history(left, right, assumptions)
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
                let Some((pointer, written @ (CValue::Int32(_) | CValue::UInt32(_)))) =
                    stored_write_reaching(
                        derivation.as_ref(),
                        &endpoint.pointer,
                        bytes,
                        assumptions,
                    )
                else {
                    return false;
                };
                let (CValue::Int32(stored) | CValue::UInt32(stored)) = &written else {
                    unreachable!("matched as a 32-bit word store")
                };
                let pointer = &pointer;
                endpoint.matches_term(load)
                    && cell.has_only_typed_hops()
                    // The stored value is the read's only when the store is
                    // exactly the read's kind; the address half is `offset`
                    // below.
                    && endpoint.kind.reads_value(&written)
                    && written.byte_width() == bytes
                    && cell.checks_walk_from(&endpoint.memory, &endpoint.pointer, bytes, assumptions)
                    && pointer.block == endpoint.pointer.block
                    && offset.checks(&pointer.offset, &endpoint.pointer.offset, assumptions)
                    && stored == value
            }
            CheckedLoadEqualityEvidence::Canonical => {
                crate::kernel::eval::canonical_term(&self.left)
                    == crate::kernel::eval::canonical_term(&self.right)
            }
            CheckedLoadEqualityEvidence::MemoryDag(evidence) => evidence.checks(
                &Proposition::ConditionIs(
                    ConditionTerm::equal(self.left.clone(), self.right.clone()),
                    true,
                ),
                assumptions,
            ),
            CheckedLoadEqualityEvidence::OriginDirectSnapshot {
                left,
                right,
                offset,
            } => {
                left.matches_term(&self.left)
                    && right.matches_term(&self.right)
                    && left.kind == right.kind
                    && left.pointer.block == right.pointer.block
                    && offset.checks(&left.pointer.offset, &right.pointer.offset, assumptions)
                    && memories_match_for_pointer_load(&left.memory, &right.memory, &left.pointer)
            }
            CheckedLoadEqualityEvidence::OriginMemoryDag {
                left,
                right,
                equality,
            } => {
                left.matches_term(&self.left)
                    && right.matches_term(&self.right)
                    && equality.checks(
                        &Proposition::ConditionIs(
                            ConditionTerm::equal(left.as_term(), right.as_term()),
                            true,
                        ),
                        assumptions,
                    )
            }
            CheckedLoadEqualityEvidence::OriginAliasedSnapshot {
                left,
                right,
                alias,
                alias_path,
                snapshots,
                named_snapshot,
            } => {
                let endpoints_match = if *named_snapshot {
                    snapshots.is_none()
                        && OriginLoadEndpoint::for_named_term(&self.left).as_ref() == Some(left)
                        && OriginLoadEndpoint::for_named_term(&self.right).as_ref() == Some(right)
                } else {
                    left.matches_term(&self.left) && right.matches_term(&self.right)
                };
                endpoints_match
                    && left.kind == right.kind
                    && match snapshots {
                        None => left.memory == right.memory,
                        Some(equality) => {
                            let Bitvector32Term::MemoryLoad(memory, pointer, kind) = &equality.left
                            else {
                                return false;
                            };
                            memory == &left.memory
                                && *kind == left.kind
                                && (pointer.as_ref() == &left.pointer
                                    || pointer.as_ref() == &right.pointer)
                                && equality.right
                                    == Bitvector32Term::MemoryLoad(
                                        right.memory.clone(),
                                        pointer.clone(),
                                        right.kind,
                                    )
                                && equality.checks_with_call_events(assumptions, call_events)
                        }
                    }
                    && origin_load_width(&self.left) == Some(4)
                    && origin_load_width(&self.right) == Some(4)
                    && (alias.as_ref()
                        == &Proposition::ConditionIs(
                            ConditionTerm::pointer_equal(
                                left.pointer.clone(),
                                right.pointer.clone(),
                            ),
                            true,
                        )
                        || alias.as_ref()
                            == &Proposition::ConditionIs(
                                ConditionTerm::pointer_equal(
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
                                    assumptions.proves_exact(&Proposition::ConditionIs(
                                        ConditionTerm::pointer_equal(
                                            step.0.clone(),
                                            step.1.clone(),
                                        ),
                                        true,
                                    )) || assumptions.proves_exact(&Proposition::ConditionIs(
                                        ConditionTerm::pointer_equal(
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
                let Proposition::CMemoryEffectSummary {
                    before,
                    after,
                    mutable_ranges,
                } = summary.as_ref()
                else {
                    return false;
                };
                let (expected_left, expected_right) = if *reversed {
                    (after, before)
                } else {
                    (before, after)
                };
                left.matches_term(&self.left)
                    && right.matches_term(&self.right)
                    && left.pointer == right.pointer
                    && left.kind == right.kind
                    && left.memory.memory() == expected_left
                    && right.memory.memory() == expected_right
                    && assumptions.contains_assumed_exact(summary)
                    && ranges.len() == mutable_ranges.len()
                    && ranges.iter().zip(mutable_ranges).all(|(evidence, range)| {
                        evidence.checks(range, &left.pointer, left.bytes(), assumptions)
                    })
            }
            CheckedLoadEqualityEvidence::SameCheckedCallEvent(evidence) => {
                let (
                    Bitvector32Term::MemoryLoad(left_memory, left_pointer, left_kind),
                    Bitvector32Term::MemoryLoad(right_memory, right_pointer, right_kind),
                ) = (&self.left, &self.right)
                else {
                    return false;
                };
                left_pointer == right_pointer
                    && left_kind == right_kind
                    && left_pointer.as_ref() == &evidence.pointer
                    && call_events.contains(&evidence.event)
                    && call_events.contains_view(&evidence.event, evidence.left.node())
                    && call_events.contains_view(&evidence.event, evidence.right.node())
                    && matches!(
                        evidence.left.node().derivation().as_deref(),
                        Some(CMemoryDerivation::CallHavoc { .. })
                    )
                    && matches!(
                        evidence.right.node().derivation().as_deref(),
                        Some(CMemoryDerivation::CallHavoc { .. })
                    )
                    && evidence.left.checks_walk_from(
                        left_memory,
                        left_pointer,
                        crate::kernel::load_term_access_width(
                            left_memory,
                            left_pointer,
                            *left_kind,
                        ),
                        assumptions,
                    )
                    && evidence.right.checks_walk_from(
                        right_memory,
                        right_pointer,
                        crate::kernel::load_term_access_width(
                            right_memory,
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
            | CheckedLoadEqualityEvidence::OriginDirectSnapshot { .. }
            | CheckedLoadEqualityEvidence::OriginAliasedSnapshot { .. }
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
        left: Bitvector32Term,
        right: Bitvector32Term,
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
    left: &Bitvector32Term,
    right: &Bitvector32Term,
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
/// structural snapshot rule separately.
pub(crate) fn checked_recorded_atomic_load_equality(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
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
pub(crate) fn checked_stored_origin_equality(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    for (value, load, reversed) in [(left, right, false), (right, left, true)] {
        let Some(endpoint) = OriginLoadEndpoint::for_term(load) else {
            continue;
        };
        let previous = EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true));
        let cell = with_extended_dag_bridging(|| {
            memory_dag_cell_source(
                &endpoint.memory,
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
        let Some((pointer, written @ (CValue::Int32(_) | CValue::UInt32(_)))) = written else {
            continue;
        };
        let (CValue::Int32(stored) | CValue::UInt32(stored)) = &written else {
            unreachable!("matched as a 32-bit word store")
        };
        let pointer = &pointer;
        // Exactly the read's kind and as wide as the walk, as
        // `write_supplies_read` asks of every stored value; the address half
        // is the offset congruence below.
        let bytes = endpoint.bytes();
        if stored != value
            || pointer.block != endpoint.pointer.block
            || !endpoint.kind.reads_value(&written)
            || written.byte_width() != bytes
        {
            continue;
        }
        let Some(offset) = assumptions
            .pointer_offset_congruence_evidence(&pointer.offset, &endpoint.pointer.offset)
        else {
            continue;
        };
        let equality = CheckedLoadEquality {
            left: left.clone(),
            right: right.clone(),
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

/// Select a finite equality witness for two loads at the snapshots where the
/// execution first observed them. This is the evidence-producing replacement
/// for the former recursive origin fallback in `memory_loads_proven_equal`.
pub(crate) fn checked_origin_load_equality(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    let Some(_query) = CheckedOriginLoadEqualityGuard::enter(left, right) else {
        return false;
    };
    // Equal names are definitionally one snapshot. Address congruence at
    // that snapshot does not require connecting first-observed origins,
    // which may belong to disconnected execution arms.
    let named_endpoints = OriginLoadEndpoint::for_named_term(left)
        .zip(OriginLoadEndpoint::for_named_term(right))
        .filter(|(left, right)| {
            left.memory == right.memory && left.pointer.block != right.pointer.block
        });
    let named_snapshot = named_endpoints.is_some();
    let Some((left_endpoint, right_endpoint)) = named_endpoints
        .or_else(|| OriginLoadEndpoint::for_term(left).zip(OriginLoadEndpoint::for_term(right)))
    else {
        return false;
    };
    if left_endpoint.kind != right_endpoint.kind {
        return false;
    }
    if left_endpoint.pointer.block != right_endpoint.pointer.block {
        if origin_load_width(left) == Some(4) && origin_load_width(right) == Some(4) {
            for (first, second) in [
                (&left_endpoint.pointer, &right_endpoint.pointer),
                (&right_endpoint.pointer, &left_endpoint.pointer),
            ] {
                let alias = Proposition::ConditionIs(
                    ConditionTerm::pointer_equal(first.clone(), second.clone()),
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
                    let snapshots = if left_endpoint.memory == right_endpoint.memory {
                        None
                    } else {
                        let mut selected = None;
                        for pointer in [&left_endpoint.pointer, &right_endpoint.pointer] {
                            let first = Bitvector32Term::MemoryLoad(
                                left_endpoint.memory.clone(),
                                Box::new(pointer.clone()),
                                left_endpoint.kind,
                            );
                            let second = Bitvector32Term::MemoryLoad(
                                right_endpoint.memory.clone(),
                                Box::new(pointer.clone()),
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
                        evidence: CheckedLoadEqualityEvidence::OriginAliasedSnapshot {
                            left: left_endpoint.clone(),
                            right: right_endpoint.clone(),
                            alias: Box::new(alias),
                            alias_path,
                            snapshots,
                            named_snapshot,
                        },
                    });
                    return true;
                }
            }
        }
        return false;
    }
    // The arms below compare the two origin snapshots' cell maps, and a cell
    // map does not record the stores it dropped. Ask the history about the
    // endpoints this comparison is about to take as equal.
    if left_endpoint.pointer == right_endpoint.pointer
        && crate::kernel::reasoning::loads_separated_by_recorded_history(
            &left_endpoint.memory,
            &right_endpoint.memory,
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
                &left_endpoint.memory,
                &right_endpoint.memory,
                &left_endpoint.pointer,
            )
        })
        .map(|offset| CheckedLoadEqualityEvidence::OriginDirectSnapshot {
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
                .memory_effect_facts_naming(left_endpoint.memory.memory())
                .find_map(|summary| {
                    let Proposition::CMemoryEffectSummary {
                        before,
                        after,
                        mutable_ranges,
                    } = summary
                    else {
                        return None;
                    };
                    let reversed = if before == left_endpoint.memory.memory()
                        && after == right_endpoint.memory.memory()
                    {
                        false
                    } else if after == left_endpoint.memory.memory()
                        && before == right_endpoint.memory.memory()
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
                                    &left_endpoint.memory,
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
pub(crate) enum PointerOffsetEqualityEvidence {
    Exact,
    Add {
        first: Box<PointerOffsetEqualityEvidence>,
        second: Box<PointerOffsetEqualityEvidence>,
        swapped: bool,
    },
    Int32Scaled {
        byte_width: i64,
        values: AtomicMemoryLoadEqualityEvidence,
    },
}

pub(super) fn pointer_offset_equality_evidence(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> Option<PointerOffsetEqualityEvidence> {
    if left == right {
        return Some(PointerOffsetEqualityEvidence::Exact);
    }
    match (left, right) {
        (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
            if let Some((first, second)) =
                pointer_offset_equality_evidence(left_a, right_a, assumptions).zip(
                    pointer_offset_equality_evidence(left_b, right_b, assumptions),
                )
            {
                return Some(PointerOffsetEqualityEvidence::Add {
                    first: Box::new(first),
                    second: Box::new(second),
                    swapped: false,
                });
            }
            let (first, second) =
                pointer_offset_equality_evidence(left_a, right_b, assumptions).zip(
                    pointer_offset_equality_evidence(left_b, right_a, assumptions),
                )?;
            Some(PointerOffsetEqualityEvidence::Add {
                first: Box::new(first),
                second: Box::new(second),
                swapped: true,
            })
        }
        (
            PointerOffsetTerm::Int32Scaled {
                value: left,
                byte_width: left_width,
            },
            PointerOffsetTerm::Int32Scaled {
                value: right,
                byte_width: right_width,
            },
        ) if left_width == right_width => {
            let values = atomic_memory_load_equality_evidence(left, right, assumptions)?;
            values
                .is_fully_typed()
                .then_some(PointerOffsetEqualityEvidence::Int32Scaled {
                    byte_width: *left_width,
                    values,
                })
        }
        _ => None,
    }
}

impl PointerOffsetEqualityEvidence {
    pub(super) fn checks(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
        assumptions: &PureFactContext,
    ) -> bool {
        match self {
            Self::Exact => left == right,
            Self::Add {
                first,
                second,
                swapped,
            } => {
                let (
                    PointerOffsetTerm::Add(left_a, left_b),
                    PointerOffsetTerm::Add(right_a, right_b),
                ) = (left, right)
                else {
                    return false;
                };
                let (right_first, right_second) = if *swapped {
                    (right_b.as_ref(), right_a.as_ref())
                } else {
                    (right_a.as_ref(), right_b.as_ref())
                };
                first.checks(left_a, right_first, assumptions)
                    && second.checks(left_b, right_second, assumptions)
            }
            Self::Int32Scaled { byte_width, values } => {
                let (
                    PointerOffsetTerm::Int32Scaled {
                        value: left,
                        byte_width: left_width,
                    },
                    PointerOffsetTerm::Int32Scaled {
                        value: right,
                        byte_width: right_width,
                    },
                ) = (left, right)
                else {
                    return false;
                };
                left_width == byte_width
                    && right_width == byte_width
                    && values.checks(
                        &Proposition::ConditionIs(
                            ConditionTerm::equal(left.as_ref().clone(), right.as_ref().clone()),
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
        // width-independent: that the two snapshots hold one version of the
        // cell at one address. How many bytes the C access reads is the
        // walk's own input, taken from the load registry on both the
        // construction and the checking side, not something the goal's
        // carrier decides.
        let Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            }
            | ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            true,
        ) = proposition
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
            Bitvector32Term::MemoryLoad(left_memory, left_pointer, left_kind),
            Bitvector32Term::MemoryLoad(right_memory, right_pointer, right_kind),
        ) = (left.as_ref(), right.as_ref())
        else {
            return false;
        };
        let left_start = match left_projection {
            Some(projection) if projection.checks(left_memory, left_pointer) => &projection.source,
            Some(_) => return false,
            None => left_memory,
        };
        let right_start = match right_projection {
            Some(projection) if projection.checks(right_memory, right_pointer) => {
                &projection.source
            }
            Some(_) => return false,
            None => right_memory,
        };
        left_pointer == right_pointer
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
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> Option<AtomicMemoryLoadEqualityEvidence> {
    let (
        Bitvector32Term::MemoryLoad(left_memory, left_pointer, left_kind),
        Bitvector32Term::MemoryLoad(right_memory, right_pointer, right_kind),
    ) = (left, right)
    else {
        return None;
    };
    if left_pointer != right_pointer || left_kind != right_kind {
        return None;
    }
    let left_projection = CanonicalLoadProjectionEvidence::for_endpoint(left_memory, left_pointer);
    let right_projection =
        CanonicalLoadProjectionEvidence::for_endpoint(right_memory, right_pointer);
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
            .unwrap_or(left_memory);
        let right_start = right_selected
            .map(|projection| &projection.source)
            .unwrap_or(right_memory);
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
    range: &CMemoryRange,
    pointer: &Pointer,
) -> Option<Bitvector32Term> {
    if range.base.block != pointer.block {
        return None;
    }
    let PointerOffsetTerm::Add(left, right) = &range.base.offset else {
        return None;
    };
    if pointer.offset == **left {
        element_index_from_offset(right, range.element_width())
    } else if pointer.offset == **right {
        element_index_from_offset(left, range.element_width())
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
    pointer: &Pointer,
    base: &Pointer,
    element_width: u32,
) -> Option<i64> {
    let element_width = i64::from(element_width);
    if element_width <= 0 {
        return None;
    }
    let bytes = signed_bitvector_constant(&pointer_byte_offset_from_base(pointer, base)?)?;
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
fn separation_index_blocks(pointer: &Pointer, assumptions: &PureFactContext) -> Vec<PointerBlock> {
    let mut blocks = vec![pointer.block.clone()];
    if let Some(alias) = assumptions.exact_pointer_aliases(pointer).find(|alias| {
        !matches!(
            alias.block,
            PointerBlock::Symbolic(_) | PointerBlock::FunctionSymbolic(_)
        )
    }) && alias.block != pointer.block
    {
        blocks.push(alias.block.clone());
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
    range: &CMemoryRange,
    pointer: &Pointer,
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
    // two selected addresses. Retain their complete extents, just as the
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
        crate::kernel::record_implicit_reasoning_provenance(
            assumptions,
            &Proposition::CResourceComposition(resources.clone()),
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
            crate::kernel::record_implicit_reasoning_provenance(assumptions, fact);
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
    // already retain their complete typed extents.
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
    let range_start = Bitvector32Term::add(offset.clone(), range.start().clone());
    let positive = PositiveTermEvidence::for_term(&range_start, assumptions)?;
    Some(RangeDisjointFromPointerEvidence::ForwardOffset { offset, positive })
}

/// Shared cheap byte-separation rule for cache retention and read-over-store.
/// Numeric address geometry is consulted before separation authority: a known
/// partial overlap invalidates an old partition just as an equal base does.
/// Stated authority is indexed by the two anchors, not their shared C block.
pub(in crate::kernel) fn indexed_store_byte_separation_evidence(
    write: &Pointer,
    write_bytes: u32,
    pointer: &Pointer,
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
    if write.block == pointer.block
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
        crate::kernel::record_implicit_reasoning_provenance(assumptions, proposition);
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
                load_bytes,
                assumptions,
                true,
            )
        })
}

pub(in crate::kernel) fn typed_store_separated_ranges_evidence(
    write: &Pointer,
    write_bytes: u32,
    pointer: &Pointer,
    load_bytes: u32,
    assumptions: &PureFactContext,
) -> Option<MemoryDagHopJustification> {
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
                alias.block,
                PointerBlock::Symbolic(_) | PointerBlock::FunctionSymbolic(_)
            )
        })
        .unwrap_or(write);
    let resolved_load = assumptions
        .exact_pointer_aliases(pointer)
        .find(|alias| {
            !matches!(
                alias.block,
                PointerBlock::Symbolic(_) | PointerBlock::FunctionSymbolic(_)
            )
        })
        .unwrap_or(pointer);
    let stated = assumptions
        .memory_separation_candidates(&resolved_write.block, &resolved_load.block)
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
            crate::kernel::record_implicit_reasoning_provenance(assumptions, proposition);
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
    crate::kernel::record_implicit_reasoning_provenance(
        assumptions,
        &Proposition::CResourceComposition(resources.clone()),
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
/// snapshot, so each denotes one fixed address however far the proof has
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
/// the same interned snapshot. Both walks pass `PureFactContext::new()`
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
    write: &Pointer,
    write_bytes: u32,
    pointer: &Pointer,
    load_bytes: u32,
    assumptions: &PureFactContext,
) -> Option<MemoryDagHopJustification> {
    owned_composition_store_separated_evidence_impl(
        write,
        write_bytes,
        pointer,
        load_bytes,
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
    write: &Pointer,
    write_bytes: u32,
    pointer: &Pointer,
    load_bytes: u32,
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
                                [&write.block, &pointer.block]
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
                let member = |pointer: &Pointer, bases: &[Pointer]| {
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
                crate::kernel::record_implicit_reasoning_provenance(
                    assumptions,
                    &Proposition::CResourceComposition(resources.clone()),
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
fn store_member_probe_bases(pointer: &Pointer, assumptions: &PureFactContext) -> Vec<Pointer> {
    let mut bases = Vec::new();
    let mut base = pointer.clone();
    loop {
        bases.push(base.clone());
        bases.extend(assumptions.exact_pointer_aliases(&base).cloned());
        base.offset = match &base.offset {
            PointerOffsetTerm::Add(left, _) => (**left).clone(),
            PointerOffsetTerm::Constant(value) if *value != 0 => PointerOffsetTerm::Constant(0),
            // A loaded pointer's displacement is all of its offset: the
            // read itself, at displacement zero, is the object's base.
            PointerOffsetTerm::Int32Scaled { .. } | PointerOffsetTerm::Int64Scaled { .. }
                if matches!(base.block, PointerBlock::LoadedPointer(_)) =>
            {
                PointerOffsetTerm::Constant(0)
            }
            _ => break,
        };
    }
    bases
}

pub(in crate::kernel) fn typed_ranges_disjoint_from_pointer_evidence(
    ranges: &[CMemoryRange],
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
) -> Option<Vec<RangeDisjointFromPointerEvidence>> {
    ranges
        .iter()
        .map(|range| typed_range_disjoint_from_pointer_evidence(range, pointer, bytes, assumptions))
        .collect()
}

/// A typed pointer read may recover a stored pointer in a different block.
/// Compare the complete stored value, never just its offset.
pub(crate) fn pointer_read_has_stored_value(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    pointer_read_stored_value(left, assumptions, None).is_some_and(|stored| {
        stored.pointer() == right || assumptions.pointers_known_equal(stored.pointer(), right)
    })
}

/// Canonical load projections retain all potentially observable scalar bytes
/// (up to MAX_SCALAR_ACCESS_BYTES). Reuse the producer's retained source for
/// a complete pointer read, whose eight bytes fit that projection, so its
/// selected memory history is available without rebuilding either snapshot.
fn complete_pointer_read_source(read: &LoadedPointerView) -> SharedCMemory {
    canonical_load_projection_source(&read.defining_memory, &read.defining_address)
        .unwrap_or_else(|| read.defining_memory.clone())
}

/// Whether two reads at addresses the caller proved equal see the bytes of
/// one cell source. Reads of one snapshot are one read. Each may also be a
/// projection of a different snapshot, which it agrees with at its own cell;
/// that does not make the two reads differ. A frame can retain an opaque read
/// without materializing its cell, so the walk follows only the selected
/// cell, stopping at the older named snapshot.
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
    left: &Pointer,
    right: &Pointer,
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
        &Bitvector32Term::pointer_address(left.clone()),
        &Bitvector32Term::pointer_address(right.clone()),
    )
}

/// Equal complete read applications across a frame denote equal numeric
/// addresses too. This rule is used only when comparing complete C pointers;
/// ordinary scalar load variables cannot acquire a typed read from it.
pub(in crate::kernel) fn complete_pointer_reads_equal_across_frame(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    // A symbolic read identity denotes a complete read only when its typed
    // producer retained this exact definition. Never infer one from a scalar
    // load variable, matching arithmetic, or a different pointee stride.
    let read = |value: &Pointer| {
        value.as_loaded_value().or_else(|| {
            let Bitvector32Term::MemoryLoad(memory, address, LoadKind::Int32) =
                crate::kernel::equality_graph::logical_pointer_read_term(value)?
            else {
                return None;
            };
            Pointer::loaded_value(&memory, &address).as_loaded_value()
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
            matches!(cell, MemoryDagCell::Stored { value: CValue::Pointer(value), .. }
                if value.pointer() == &Pointer::loaded_value(&read.defining_memory, &read.defining_address))
        };
        left.node() == right.node() || stores_read(&left, &b) || stores_read(&right, &a)
    })
}

pub(in crate::kernel) fn pointer_read_designations_equal(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    pointer_read_domains_equal(left, right, assumptions, false)
}

pub(in crate::kernel) fn pointer_read_extents_equal(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    pointer_read_domains_equal(left, right, assumptions, true)
}

fn pointer_read_domains_equal(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
    extent: bool,
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
    if matches!(&a_value, Some(CValue::Pointer(stored)) if if extent { stored.extent().is_none() && !stored.extent_is_known() && stored.opaque_extent() == Some(right_origin) } else { stored.designation() == right_origin })
        || matches!(&b_value, Some(CValue::Pointer(stored)) if if extent { stored.extent().is_none() && !stored.extent_is_known() && stored.opaque_extent() == Some(left_origin) } else { stored.designation() == left_origin })
    {
        return true;
    }
    matches!((a_value, b_value),
        (Some(CValue::Pointer(a)), Some(CValue::Pointer(b))) if a == b)
}

/// Recover only an actual complete pointer stored at this read's source.
/// Numeric scalar values and address equalities supply no pointer metadata.
pub(in crate::kernel) fn complete_pointer_read_value(
    origin: &Pointer,
    assumptions: &PureFactContext,
) -> Option<CPointerValue> {
    let CValue::Pointer(value) = complete_pointer_carrier_read_value(origin, assumptions)? else {
        return None;
    };
    Some(value)
}

/// Recover an actual complete pointer or pointer-carrying integer store.
/// Numeric scalar bytes never manufacture a representation record.
pub(in crate::kernel) fn complete_pointer_carrier_read_value(
    origin: &Pointer,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    let read = origin.as_loaded_value()?;
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
    // A walk stopped by an affecting edge can retain a scalar-prefix cache.
    // Only a reached whole-pointer store supplies the complete value.
    let MemoryDagCell::Stored {
        value: value @ (CValue::Pointer(_) | CValue::PointerInteger(_)),
        ..
    } = cell
    else {
        return None;
    };
    Some(value)
}

/// Explicit pointer read-value normalization follows at most 64 recorded
/// edges and compares the entire pointer using only the cited conditions.
/// A different block with the same offset is not the stored pointer.
pub(crate) fn pointer_read_has_recorded_value(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if pointer_reads_share_recorded_cell(left, right, assumptions) {
        return true;
    }
    [(left, right), (right, left)]
        .into_iter()
        .any(|(read, value)| {
            pointer_read_stored_value(read, assumptions, Some(64)).is_some_and(|stored| {
                stored.pointer() == value
                    || assumptions.pointers_known_equal(stored.pointer(), value)
            })
        })
}

/// Compare complete typed reads in one producer-retained snapshot using only
/// the selected address equality. This adds neither memory transport nor
/// permission to read the cell.
fn pointer_reads_share_recorded_cell(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    let read = |value: &Pointer| {
        if let Some(observation) = crate::kernel::eval::latest_pointer_read_observation(value) {
            return Some((observation.0, Box::new(observation.1)));
        }
        let Bitvector32Term::MemoryLoad(memory, address, kind) =
            crate::kernel::equality_graph::logical_pointer_read_term(value)?
        else {
            return None;
        };
        (crate::kernel::load_term_access_width(&memory, &address, kind)
            == crate::kernel::C_POINTER_BYTE_WIDTH)
            .then_some((memory, address))
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
/// discovery. The result carries no object designation or access authority.
/// The caller must keep any numeric union local to its resource query.
pub(in crate::kernel) fn checked_pointer_read_endpoint(
    read: &Pointer,
    assumptions: &PureFactContext,
) -> Option<Pointer> {
    checked_pointer_read_endpoint_and_kind(read, assumptions).map(|(endpoint, _)| endpoint)
}

/// [`checked_pointer_read_endpoint`] when the checked walk ends at a stored
/// complete pointer, rather than at an older snapshot's read of the cell.
pub(in crate::kernel) fn checked_pointer_read_stored_value(
    read: &Pointer,
    assumptions: &PureFactContext,
) -> Option<Pointer> {
    checked_pointer_read_endpoint_and_kind(read, assumptions)
        .and_then(|(endpoint, stored)| stored.then_some(endpoint))
}

/// The checked endpoint, and whether it is a stored complete pointer.
fn checked_pointer_read_endpoint_and_kind(
    read: &Pointer,
    assumptions: &PureFactContext,
) -> Option<(Pointer, bool)> {
    let Bitvector32Term::MemoryLoad(memory, address, kind) =
        crate::kernel::equality_graph::logical_pointer_read_term(read).or_else(|| {
            let application = assumptions.retained_pointer_read_application(read)?;
            let definition = application.as_loaded_value()?;
            Some(Bitvector32Term::MemoryLoad(
                definition.defining_memory,
                Box::new(definition.defining_address),
                LoadKind::of_type(CType::Int32Pointer)?,
            ))
        })?
    else {
        return None;
    };
    if crate::kernel::load_term_access_width(&memory, &address, kind)
        != crate::kernel::C_POINTER_BYTE_WIDTH
    {
        return None;
    }
    let source =
        canonical_load_projection_source(&memory, &address).unwrap_or_else(|| memory.clone());
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
            MemoryDagCell::Stored { value, .. } => match kind.read_cell(value) {
                Some(CValue::Pointer(stored)) => Some((stored.into_pointer(), true)),
                _ => None,
            },
            // A walk can stop at an unproved or affecting edge. Its cached
            // cell map is not a certificate for a value across that edge.
            MemoryDagCell::Unwritten { .. } => {
                Some((Pointer::loaded_value(cell.node(), &address), false))
            }
        }
    })
}

/// Resolve a selected recorded read from its producer's exact source, not
/// the cell cache its canonical projection happens to retain. Bookkeeping
/// edges write no program bytes; every actual write still uses the existing
/// typed access classifier. The hop bound applies to the selected source path.
fn bounded_recorded_cell_source(
    memory: &SharedCMemory,
    address: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
    limit: usize,
) -> Option<MemoryDagCell> {
    bounded_recorded_cell_resolution(memory, address, bytes, assumptions, limit)
        .1
        .map(|(cell, _)| cell)
}

fn bounded_recorded_cell_resolution(
    memory: &SharedCMemory,
    address: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
    limit: usize,
) -> (SharedCMemory, Option<(MemoryDagCell, CellWalkStop)>) {
    crate::instrumentation::record_deterministic_work(1);
    let source =
        canonical_load_projection_source(memory, address).unwrap_or_else(|| memory.clone());
    let result = with_extended_dag_bridging(|| {
        memory_dag_cell_source_with_hop_limit_and_stop(&source, address, bytes, assumptions, limit)
    });
    (source, result)
}

pub(in crate::kernel) fn pointer_read_stored_value(
    read: &Pointer,
    assumptions: &PureFactContext,
    max_hops: Option<usize>,
) -> Option<CPointerValue> {
    let Bitvector32Term::MemoryLoad(memory, address, kind) =
        crate::kernel::equality_graph::logical_pointer_read_term(read)?
    else {
        return None;
    };
    let bytes = crate::kernel::load_term_access_width(&memory, &address, kind);
    if bytes != crate::kernel::C_POINTER_BYTE_WIDTH {
        return None;
    }
    let cell = match max_hops {
        Some(limit) => bounded_recorded_cell_source(&memory, &address, bytes, assumptions, limit),
        None => memory_dag_cell_source(&memory, &address, bytes, assumptions, true),
    }?;
    if let Some(value) = cell.resolved_value(&address, kind) {
        return match value {
            CValue::Pointer(stored) => Some(stored),
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
    address: &Pointer,
    kind: LoadKind,
    bytes: u32,
    assumptions: &PureFactContext,
) -> Option<CPointerValue> {
    let step = cell.node().derivation()?;
    let CMemoryDerivation::Store {
        pointer: write,
        value,
        ..
    } = step.as_ref()
    else {
        return None;
    };
    let CValue::Pointer(stored) = value else {
        return None;
    };
    (bytes == crate::kernel::C_POINTER_BYTE_WIDTH
        && value.byte_width() == bytes
        && kind.reads_value(value)
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
/// `PointerOffsetTerm`s, so they cannot use the int32 load-equality API even
/// though the same checked store/call-frame walk supplies their value.
pub(crate) fn pointer_load_offset_proven_equal(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> bool {
    let PointerOffsetTerm::Int32Scaled { value, .. } = left else {
        return false;
    };
    let load = match value.as_ref() {
        load @ Bitvector32Term::MemoryLoad(_, _, _) => Some(load.clone()),
        Bitvector32Term::Variable(variable) => {
            crate::kernel::eval::registered_load_origin_term_for_variable(variable)
        }
        _ => None,
    };
    let Some(Bitvector32Term::MemoryLoad(memory, pointer, kind)) = load else {
        return false;
    };
    let bytes = crate::kernel::load_term_access_width(&memory, &pointer, kind);
    let Some(cell) = memory_dag_cell_source(&memory, &pointer, bytes, assumptions, true) else {
        return false;
    };
    let Some(CValue::Pointer(stored)) = cell.resolved_value(&pointer, kind) else {
        return false;
    };
    crate::kernel::reasoning::pointer_offsets_proven_equal_for_memory_resolution(
        &stored.pointer().offset,
        right,
        assumptions,
    )
}

/// The write a walk stopped at: the store's pointer and value, for a `Store`
/// edge, and for a `CellsSeeded` edge the one store of the run that writes
/// the cell at `pointer`, asked exactly as the walk asked it.
fn stored_write_reaching(
    derivation: &CMemoryDerivation,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
) -> Option<(Pointer, CValue)> {
    match derivation {
        CMemoryDerivation::Store {
            pointer: written,
            value,
            ..
        } => Some((written.clone(), value.clone())),
        CMemoryDerivation::CellsSeeded { .. } => {
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
    allocation_base: &Pointer,
    bytes: &Bitvector32Term,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    // Only the allocation's *memory* can be separate from a cell by address.
    // The allocation token is a separate resource from every memory range,
    // including the one it covers: a composite holding `allocation(p, n)`
    // and `owns p[0..k]` states the two members separate, and reading that as
    // "the freed bytes miss `p[0]`" framed a load of freed memory across its
    // own `free`.
    let cell = CResource::Memory(CMemoryRange::new(
        pointer.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ));
    int32_element_count_from_bytes(bytes).is_some_and(|count| {
        let allocation_memory = CResource::Memory(CMemoryRange::new(
            allocation_base.clone(),
            Bitvector32Term::Constant(0),
            count,
        ));
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
/// them. Where those take two embedded snapshots, deep-canonicalize both and
/// compare the results structurally, this follows named edges and compares
/// arena ids, so the common case — two forms of one cell separated only
/// by stores that provably missed it — costs a short walk instead of a deep
/// term rewrite.
///
/// A missing result means "the DAG did not answer". Derivations are not
/// guaranteed to connect every pair of snapshots, so callers may try another
/// exact evidence source.
pub(super) fn memory_load_equality_evidence_at(
    left_memory: &SharedCMemory,
    right_memory: &SharedCMemory,
    pointer: &Pointer,
    kind: LoadKind,
    assumptions: &PureFactContext,
) -> Option<MemoryDagLoadEqualityEvidence> {
    if let Some(common) = one_snapshot_equality_evidence(left_memory, right_memory) {
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
    memory: &SharedCMemory,
    pointer: &Pointer,
    kind: LoadKind,
) -> bool {
    let Some(crate::kernel::integer32_c_value!(value)) = cell
        .node()
        .cells
        .concrete()
        .get(pointer)
        .and_then(|value| kind.read_cell(value))
    else {
        return false;
    };
    value == crate::kernel::canonical_form_of_load(memory.clone(), pointer.clone(), kind)
}

/// The equality two identical snapshots have without walking anything.
fn one_snapshot_equality_evidence(
    left_memory: &SharedCMemory,
    right_memory: &SharedCMemory,
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
/// reached say whether the two snapshots hold *one* version of the cell; the
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
        left_memory: &SharedCMemory,
        right_memory: &SharedCMemory,
        pointer: &Pointer,
        kind: LoadKind,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        let left_bytes = crate::kernel::load_term_access_width(left_memory, pointer, kind);
        let right_bytes = crate::kernel::load_term_access_width(right_memory, pointer, kind);
        // A shared snapshot already fixes one version of the cell. Reuse the
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
                    CellWalkStop::CommonSnapshot,
                    None,
                );
            }
            return Some(Self {
                left,
                right,
                left_stop: CellWalkStop::CommonSnapshot,
                right_stop: CellWalkStop::CommonSnapshot,
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
    fn equality_reason(&self, pointer: &Pointer) -> Option<MemoryDagLoadEqualityReason> {
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
    fn equality(self, pointer: &Pointer) -> Option<MemoryDagLoadEqualityEvidence> {
        let reason = self.equality_reason(pointer)?;
        Some(MemoryDagLoadEqualityEvidence {
            left: self.left,
            right: self.right,
            reason,
        })
    }

    /// Whether a recorded step that provably acts on this access's bytes
    /// stands between the two snapshots.
    ///
    /// A walk stops on such a step having proved something, not having given
    /// up: the cell one step older is a different *version* of this cell. Two
    /// loads separated by one of those are not one value by any structural
    /// route, whatever the snapshots' cell maps happen to have kept. The
    /// exhaustion and unclassified stops prove nothing and leave every other
    /// route to speak. A common-snapshot stop instead establishes equality.
    fn cross_an_affecting_step(&self) -> bool {
        self.left_stop == CellWalkStop::Affected || self.right_stop == CellWalkStop::Affected
    }

    /// [`Self::equality`], and then, where stored-value pinning is in scope,
    /// the arm that reads one side's walk as pinning the *other side's whole
    /// load term*.
    ///
    /// One side's walk may land on a `Store` whose recorded value IS the
    /// other side verbatim — the common case for a load-caching store
    /// (`cells[p] := load(older, p)`): the newer snapshot's cell literally
    /// pins the older form. That is still a pure history answer (the value
    /// comes off a derivation edge, compared structurally), so it stays
    /// inside the exact-facts-plus-edges determinism boundary.
    fn equality_or_resolved_endpoint(
        self,
        left_memory: &SharedCMemory,
        right_memory: &SharedCMemory,
        pointer: &Pointer,
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
        let load = |memory: &SharedCMemory| {
            Bitvector32Term::MemoryLoad(memory.clone(), Box::new(pointer.clone()), kind)
        };
        let pins = |cell: &MemoryDagCell, other: &Bitvector32Term| {
            matches!(
                cell.resolved_value(pointer, kind),
                Some(
                    crate::kernel::integer32_c_value!(value)
                ) if &value == other
            )
        };
        if pins(&self.left, &load(right_memory)) {
            Some(AtomicMemoryLoadEqualityEvidence::LeftResolvesToRight { left: self.left })
        } else if pins(&self.right, &load(left_memory)) {
            Some(AtomicMemoryLoadEqualityEvidence::RightResolvesToLeft { right: self.right })
        } else {
            None
        }
    }
}

/// Compare two selected read histories, stopping as soon as their checked
/// no-write prefixes meet. Alternating the walks avoids inspecting history
/// older than a nearby shared source, including for sibling snapshot views.
fn typed_reads_share_memory_source(
    left: &SharedCMemory,
    right: &SharedCMemory,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    let _scope = ExplicitReadScope(EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true)));
    with_extended_dag_bridging(|| {
        let mut current = [Some(left.clone()), Some(right.clone())];
        let mut reached = [
            std::collections::HashSet::from([left.clone()]),
            std::collections::HashSet::from([right.clone()]),
        ];
        let evidence = crate::kernel::resource_tracker::step_effect::Evidence {
            assumptions,
            cross_loop_havoc: true,
        };
        while current.iter().any(Option::is_some) {
            for side in 0..2 {
                let Some(node) = current[side].take() else {
                    continue;
                };
                crate::instrumentation::record_deterministic_work(1);
                let Some(step) = node.derivation() else {
                    continue;
                };
                if !matches!(
                    crate::kernel::resource_tracker::step_effect::affects(
                        &step,
                        &node,
                        crate::kernel::resource_tracker::Resource::Cell { pointer, bytes },
                        &evidence,
                    ),
                    crate::kernel::resource_tracker::step_effect::StepEffect::Separate(
                        crate::kernel::resource_tracker::step_effect::Separation::Cell(_)
                    )
                ) {
                    continue;
                }
                let base = step.base();
                if reached[1 - side].contains(base) {
                    return true;
                }
                if reached[side].insert(base.clone()) {
                    current[side] = Some(base.clone());
                }
            }
        }
        false
    })
}

/// Initialization can cross only checked no-write edges for this typed range.
/// Reaching equal stored values at different sources is insufficient: value
/// equality grants no authority to read an initialized object.
pub(super) fn typed_read_has_same_memory_source(
    before: &CMemory,
    after: &CMemory,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
) -> bool {
    // Complete pointer identity needs the explicit, whole-byte separation
    // premises too, rather than only the planner's address-distinctness rungs.
    let _scope = ExplicitReadScope(EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true)));
    with_extended_dag_bridging(|| {
        let before = intern_c_memory_ref(before);
        let mut current = intern_c_memory_ref(after);
        let evidence = crate::kernel::resource_tracker::step_effect::Evidence {
            assumptions,
            cross_loop_havoc: true,
        };
        // Stop at the named premise, never walk its unrelated earlier history.
        loop {
            crate::instrumentation::record_deterministic_work(1);
            if current == before {
                return true;
            }
            let Some(step) = current.derivation() else {
                return false;
            };
            if !matches!(
                crate::kernel::resource_tracker::step_effect::affects(
                    &step,
                    &current,
                    crate::kernel::resource_tracker::Resource::Cell { pointer, bytes },
                    &evidence,
                ),
                crate::kernel::resource_tracker::step_effect::StepEffect::Separate(
                    crate::kernel::resource_tracker::step_effect::Separation::Cell(_)
                )
            ) {
                return false;
            }
            current = step.base().clone();
        }
    })
}

/// The memory-DAG equality arm as a term-level test:
/// true only when both sides are atomic loads the DAG resolves alike.
///
/// Beyond the node-identity comparison, one side's walk may land on a
/// `Store` whose recorded value IS the other side verbatim — the common case
/// for a load-caching store (`cells[p] := load(older, p)`): the newer
/// snapshot's cell literally pins the older form. That is still a pure
/// DAG answer (the value comes off a derivation edge, compared structurally),
/// so it stays inside the exact-facts-plus-edges determinism boundary.
pub(crate) fn atomic_loads_equal_along_memory_derivations(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    atomic_memory_load_equality_evidence(left, right, assumptions).is_some()
}

/// Evidence-producing form of
/// [`atomic_loads_equal_along_memory_derivations`]. Positive memo entries
/// retain this evidence instead of caching only the boolean answer.
pub(super) fn atomic_memory_load_equality_evidence(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> Option<AtomicMemoryLoadEqualityEvidence> {
    let (
        Bitvector32Term::MemoryLoad(left_memory, left_pointer, left_kind),
        Bitvector32Term::MemoryLoad(right_memory, right_pointer, right_kind),
    ) = (left, right)
    else {
        return None;
    };
    if left_pointer != right_pointer || left_kind != right_kind {
        return None;
    }
    match recorded_load_history(
        left_memory,
        right_memory,
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
/// the one a snapshot comparison cannot reconstruct. A cell map records what
/// is *known* at a snapshot, not what *happened* to it: a store drops the
/// cell it partly overwrites, and the naming projection discards what it
/// leaves behind, so two snapshots a store separates can be cell-identical.
/// Absence of a differing cell is therefore never evidence that no store
/// happened. The history has the store either way.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum LoadHistory {
    /// The two snapshots hold one version of the cell, with this evidence.
    OneVersion(AtomicMemoryLoadEqualityEvidence),
    /// A recorded step that provably acts on this access's bytes stands
    /// between the two snapshots, so they hold two different versions of it.
    /// No structural route may call the two loads equal; a stated or assumed
    /// equality fact still can, and is consulted before this ever is.
    DifferentVersions,
    /// The recorded history decides neither. Every other route may speak.
    Undecided,
}

/// The one memoized question every consumer of the load history asks.
///
/// Both halves of the answer come from one pair of cell-source walks, so
/// asking for the refutation after asking for the equality costs a memo
/// lookup rather than a second traversal.
pub(in crate::kernel) fn recorded_load_history(
    left_memory: &SharedCMemory,
    right_memory: &SharedCMemory,
    pointer: &Pointer,
    kind: LoadKind,
    assumptions: &PureFactContext,
) -> LoadHistory {
    // The same (snapshot, snapshot, pointer) triple is asked thousands of
    // times per proof. A proven equality stays true as new first-wins DAG
    // edges are recorded: the edges only add faithful derivations of already
    // existing snapshots. Cache those positive answers independently of the
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
    let derivation_generation = c_memory_derivation_generation();
    // A completed refusal concerns the unordered pair of snapshots. Keep
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
    left_memory: &SharedCMemory,
    right_memory: &SharedCMemory,
    pointer: &Pointer,
    kind: LoadKind,
    assumptions: &PureFactContext,
) -> LoadHistory {
    if let Some(common) = one_snapshot_equality_evidence(left_memory, right_memory) {
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
/// snapshot cell provides, or else the load of the oldest snapshot the walk
/// proves the cell unchanged from, named by the assumption-free naming walk
/// so that facts spelled with that older name apply exactly.
pub(crate) fn resolve_load_along_memory_derivations(
    memory: &SharedCMemory,
    pointer: &Pointer,
    kind: LoadKind,
    assumptions: &PureFactContext,
) -> Option<Bitvector32Term> {
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
            MemoryDagCell::Unwritten { node, .. } => crate::kernel::eval::load_variable_for_term(
                &Bitvector32Term::MemoryLoad(node, Box::new(pointer.clone()), kind),
            )
            .map(|(variable, _)| Bitvector32Term::Variable(variable)),
        }
    });
    EXPLICIT_DAG_CHECK.with(|flag| flag.set(previous));
    result
}

/// Rewrites `proposition` with each registered load variable replaced by the
/// form [`resolve_load_along_memory_derivations`] decides for it from its
/// origin snapshot under `assumptions`. Returns `None` when nothing changes.
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
        let Some(Bitvector32Term::MemoryLoad(origin, pointer, kind)) =
            crate::kernel::registered_load_origin_term_for_variable(&variable)
        else {
            continue;
        };
        let Some(form) =
            resolve_load_along_memory_derivations(&origin, &pointer, kind, assumptions)
        else {
            continue;
        };
        if form == Bitvector32Term::Variable(variable) {
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
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    let _assumptions_id_scope = assumptions.enter_id_scope();
    let previous = EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true));
    let result = with_extended_dag_bridging(|| {
        if atomic_loads_equal_along_memory_derivations(left, right, assumptions) {
            return true;
        }
        let resolves_to = |load: &Bitvector32Term, value: &Bitvector32Term| {
            let Bitvector32Term::MemoryLoad(memory, pointer, kind) = load else {
                return false;
            };
            let bytes = crate::kernel::load_term_access_width(memory, pointer, *kind);
            matches!(
                memory_dag_cell_source(memory, pointer, bytes, assumptions, true)
                    .and_then(|cell| cell.resolved_value(pointer, *kind)),
                Some(crate::kernel::integer32_c_value!(resolved))
                    if resolved == *value
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
    pointer: Pointer,
    kind: LoadKind,
}

thread_local! {
    static DAG_LOAD_EQUALITY_POSITIVE_MEMO: std::cell::RefCell<
        std::collections::HashMap<DagLoadEqualityMemoKey, AtomicMemoryLoadEqualityEvidence>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    /// The two answers that are not an equality, keyed by derivation
    /// generation: `true` is a store between the snapshots, `false` is a
    /// history that decides nothing.
    static DAG_LOAD_EQUALITY_UNPROVEN_MEMO: std::cell::RefCell<
        std::collections::HashMap<(u64, DagLoadEqualityMemoKey), bool>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

const DAG_LOAD_EQUALITY_MEMO_LIMIT: usize = 200_000;

/// Searches the finite graph of recorded effects connecting two memory
/// snapshots, regardless of what the effects wrote. Used for properties that
/// survive writes, such as loadability of a still-present range.
pub(crate) fn c_memories_connected_by_effects(
    before: &CMemory,
    after: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    // A walk over the write effects (`CMemoryMutatesOnly`,
    // `CMemoryEffectSummary`) filed under each memory it reaches, in either
    // direction, not over every proposition fact. A memory reached is the
    // target when it is the target's canonical equal.
    if c_memories_canonically_equal(before, after) {
        return true;
    }
    let mut seen = std::collections::HashSet::from([before.clone()]);
    let mut frontier = vec![before.clone()];
    while let Some(current) = frontier.pop() {
        for fact in assumptions.memory_effect_facts_naming(&current) {
            let (Proposition::CMemoryMutatesOnly {
                before: step_before,
                after: step_after,
                ..
            }
            | Proposition::CMemoryEffectSummary {
                before: step_before,
                after: step_after,
                ..
            }) = fact
            else {
                continue;
            };
            let other = if step_before == &current {
                step_after
            } else {
                step_before
            };
            if seen.insert(other.clone()) {
                if c_memories_canonically_equal(other, after) {
                    return true;
                }
                frontier.push(other.clone());
            }
        }
    }
    false
}

/// Address inequality frames a load only when the two typed accesses fit
/// inside the gap it proves. Keep explicit range separation available even
/// when an address-only comparison cannot establish that gap.
pub(crate) fn write_access_is_disjoint_from_load(
    write: &Pointer,
    write_bytes: u32,
    read: &Pointer,
    read_bytes: u32,
    assumptions: &PureFactContext,
) -> bool {
    if write_bytes == 0 || read_bytes == 0 {
        return false;
    }
    if write.blocks_proven_distinct(read) {
        return true;
    }
    use crate::kernel::reasoning::{AccessByteOverlap, access_byte_overlap};
    let overlap = access_byte_overlap(write, write_bytes, read, read_bytes, assumptions);
    if overlap == AccessByteOverlap::Overlaps {
        return false;
    }
    (overlap == AccessByteOverlap::Separate
        && pointers_proven_distinct_for_memory_resolution(write, read, assumptions))
        || assumptions.ranges_directly_disjoint_from_access(
            &[CMemoryRange::new_with_element_width(
                write.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
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
    /// The effect facts `c_memory_load_is_directly_unchanged` examined.
    static DIRECT_UNCHANGED_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

fn c_memory_load_is_directly_unchanged(
    before: &CMemory,
    after: &CMemory,
    pointer: &Pointer,
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
    // every proposition fact. Its other end may still be any snapshot that
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
                Proposition::CMemoryMutatesOnly {
                    before: effect_before,
                    after: effect_after,
                    writes,
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
                                crate::kernel::eval::load_access_width_at_address_or_widest(
                                    pointer,
                                )
                                .max(kind.byte_width()),
                                assumptions,
                            )
                        })
                }
                Proposition::CMemoryEffectSummary {
                    before: effect_before,
                    after: effect_after,
                    mutable_ranges,
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
                Proposition::CHeapAllocationFreed {
                    before: effect_before,
                    after: effect_after,
                    allocation_base,
                    bytes,
                } => {
                    effect_before == before
                        && memories_directly_match_for_pointer_load(
                            effect_after,
                            after,
                            pointer,
                            assumptions,
                        )
                        && heap_allocation_proven_separate_from_pointer(
                            allocation_base,
                            bytes,
                            pointer,
                            assumptions,
                        )
                }
                _ => false,
            };
            if proved {
                crate::kernel::record_implicit_reasoning_provenance(assumptions, proposition);
            }
            proved
        })
}

pub(in crate::kernel) fn memories_directly_match_for_pointer_load(
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if memories_match_for_pointer_load(left, right, pointer) {
        return true;
    }
    // Two snapshots that name the cell by one version hold the same
    // cell: every hop the naming walk crossed is a write proven (without
    // assumptions) to miss the cell. This is how a fact carried unchanged
    // through earlier steps, and so still named at its mint version, meets an
    // effect summary whose `before` is the later live snapshot.
    if !pointer.block.is_local_block()
        && let (Some(left_version), Some(right_version)) = (
            cell_version_point(
                &crate::kernel::intern_c_memory(left.clone()),
                pointer,
                crate::kernel::load_access_width_or_widest(
                    &crate::kernel::intern_c_memory(left.clone()),
                    pointer,
                ),
            ),
            cell_version_point(
                &crate::kernel::intern_c_memory(right.clone()),
                pointer,
                crate::kernel::load_access_width_or_widest(
                    &crate::kernel::intern_c_memory(right.clone()),
                    pointer,
                ),
            ),
        )
        && left_version == right_version
    {
        return true;
    }
    if pointer.block.is_local_block()
        || !left
            .blocks
            .iter()
            .filter(|(block, _)| block.is_havoc_block() || block.is_call_havoc_block())
            .eq(right
                .blocks
                .iter()
                .filter(|(block, _)| block.is_havoc_block() || block.is_call_havoc_block()))
        || left.blocks.get(&pointer.block) != right.blocks.get(&pointer.block)
    {
        return false;
    }
    // Every arm below decides whether the cell's *address* is a different
    // address from the load's, and that is not the question this function
    // asks: it is deciding whether the two snapshots hold one value for this
    // load, and a cell at `p + 1` holding one byte is a different address
    // from `p` while being the second byte a four-byte read there returns.
    // `1a3b2701` put the byte question in front of the three sibling
    // comparisons; this is the fourth, and the constant-offset arm —
    // `pointer_byte_offset_from_base(...) != 0` — is the plainest statement of
    // the confusion, calling a cell four bytes into an eight-byte read
    // separate from it.
    let load_bytes = crate::kernel::load_access_width_or_widest(
        &crate::kernel::intern_c_memory(left.clone()),
        pointer,
    );
    differing_cell_pointers_possibly_aliasing(left, right, &pointer.block)
        .into_iter()
        .all(|cell| {
            differing_cell_bytes_miss_the_load(left, right, &cell, pointer, load_bytes, assumptions)
                && (cell.blocks_proven_distinct(pointer)
                || pointer_offsets_with_common_base_proven_distinct(&cell, pointer, assumptions)
                || pointers_proven_distinct_for_memory_resolution(&cell, pointer, assumptions)
                || pointer_byte_offset_from_base(&cell, pointer)
                    .and_then(|offset| offset.as_const())
                    .is_some_and(|offset| offset != 0)
                || assumptions.ranges_directly_disjoint_from_pointer(
                    &[CMemoryRange::new(
                        cell.clone(),
                        Bitvector32Term::Constant(0),
                        Bitvector32Term::Constant(1),
                    )],
                    pointer,
                )
                // Last: the same composition rule the mutates-only arm above
                // and the tracker's `Store` arm spend, so the three agree.
                || owned_composition_store_separated_evidence(&cell, differing_cell_byte_width(left, right, &cell), pointer, load_bytes, assumptions).is_some())
        })
}

/// The cells the two snapshots disagree about that a load in `block` could be
/// reading: its own block, and every other block not proven distinct from it.
/// A differently spelled block is not a different object, so the caller must
/// still discharge each of these cells by offset or by separation evidence.
fn differing_cell_pointers_possibly_aliasing(
    left: &CMemory,
    right: &CMemory,
    block: &PointerBlock,
) -> BTreeSet<Pointer> {
    left.cells
        .keys()
        .chain(right.cells.keys())
        .filter(|pointer| pointer.block.observable_by_load(block))
        .filter(|pointer| left.cells.get(pointer) != right.cells.get(pointer))
        .cloned()
        .collect()
}

/// Whether `materialized` holds, at `pointer`, exactly the `kind` read of
/// `pointer` that `symbolic` holds: a cell whose value is that read, taken
/// from a snapshot that agrees with `symbolic` there.
///
/// The cell answers for the read only when it is the read: the value is of
/// the read's kind and is itself a load of that kind. A cell of another width
/// holds other bytes than the read returns, and one of the other signedness
/// holds another number.
fn memory_materializes_atomic_load(
    materialized: &CMemory,
    symbolic: &CMemory,
    pointer: &Pointer,
    kind: LoadKind,
) -> bool {
    let Some(value) = materialized.known_value(pointer) else {
        return false;
    };
    kind.reads_value(&value)
        && matches!(
            value,
            CValue::Int8(Bitvector32Term::MemoryLoad(source, source_pointer, source_kind))
                | CValue::Int16(Bitvector32Term::MemoryLoad(source, source_pointer, source_kind))
                | CValue::Int32(Bitvector32Term::MemoryLoad(source, source_pointer, source_kind))
                | CValue::UInt8(Bitvector32Term::MemoryLoad(source, source_pointer, source_kind))
                | CValue::UInt16(Bitvector32Term::MemoryLoad(source, source_pointer, source_kind))
                | CValue::UInt32(Bitvector32Term::MemoryLoad(source, source_pointer, source_kind))
                if source_pointer.as_ref() == pointer
                    && source_kind == kind
                    && memories_match_for_pointer_load(&source, symbolic, pointer)
        )
}

/// Certifies the narrow frame rule used by execution proofs for ordinary C
/// conditions. Address-dependent loads are transported from the inside out;
/// other proposition forms must be re-established explicitly.
pub(crate) fn prove_c_condition_fact_transport(
    fact: &Proposition,
    after: &CMemory,
    assumptions: &PureFactContext,
) -> Option<Theorem> {
    prove_c_condition_fact_transport_with_assumptions(fact, after, Some((assumptions, false)))
}

pub(crate) fn prove_c_condition_fact_direct_transport(
    fact: &Proposition,
    after: &CMemory,
    assumptions: &PureFactContext,
) -> Option<Theorem> {
    prove_c_condition_fact_transport_with_assumptions(fact, after, Some((assumptions, true)))
}

/// Constructs condition-transport authority from the exact contextual facts
/// consumed by its bounded check. The explicit source remains the innermost
/// premise so consumers can distinguish it from frame or equality evidence.
pub(crate) fn c_condition_fact_transport_theorem(
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
pub(crate) fn c_condition_fact_transport_parts<'a>(
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
pub(crate) fn c_condition_fact_transport_target_in_context<'a>(
    theorem: &'a Theorem,
    source: &Proposition,
    assumptions: &PureFactContext,
) -> Option<&'a Proposition> {
    let (premises, target) = c_condition_fact_transport_parts(theorem, source)?;
    premises
        .into_iter()
        .all(|premise| assumptions.proves_exact(premise))
        .then_some(target)
}

fn prove_c_condition_fact_transport_with_assumptions(
    fact: &Proposition,
    after: &CMemory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<Theorem> {
    // Per-arm returns, no shared conclusion local: this function sits in
    // transport recursion, and a by-value `Proposition` local overflows the
    // expansion stack.
    match fact {
        Proposition::ConditionIs(condition, value) => {
            let (transported, premises) = crate::kernel::collect_reasoning_provenance(|| {
                crate::kernel::capture_implicit_reasoning_provenance(|| {
                    transport_framed_atomic_condition(condition, after, assumptions)
                })
            });
            let transported = transported?;
            if &transported == condition {
                return None;
            }
            // As with target-directed transport, provenance is a candidate
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
                if transport_framed_atomic_condition(condition, after, Some((&restricted, direct)))
                    != Some(transported.clone())
                {
                    return None;
                }
            }
            Some(c_condition_fact_transport_theorem(
                fact,
                Proposition::ConditionIs(transported, *value),
                premises,
            ))
        }
        _ => None,
    }
}

/// Rewrites subterms of a condition fact that equal a certified store's
/// value into loads from that store's post-memory, so a fact written in
/// pre-store terms can be transported across the store. The rewriting is
/// definitional: a certified store guarantees `load(after, pointer)` equals
/// the stored value.
pub(crate) fn rewrite_condition_through_certified_stores(
    fact: &Proposition,
    transitions: &(impl ExecutionFactSource + ?Sized),
) -> Proposition {
    let mut equations = Vec::new();
    for transition in transitions.fact_iter() {
        let Some(store) = &transition.certified_store else {
            continue;
        };
        let value_term = match &store.value {
            CValue::Int8(term) => term.clone(),
            CValue::Int16(term)
            | CValue::Int32(term)
            | CValue::UInt8(term)
            | CValue::UInt16(term)
            | CValue::UInt32(term) => term.clone(),
            _ => continue,
        };
        // The store's value is the read of its own kind at its own address,
        // as a word: a 32-bit read's word is its `Int32` read's (rule K5).
        let Some(kind) = LoadKind::of_value(&store.value).map(LoadKind::word_kind) else {
            continue;
        };
        equations.push((
            canonicalize_atomic_loads(&value_term),
            Bitvector32Term::memory_read(
                crate::kernel::intern_c_memory(store.after.clone()),
                store.pointer.clone(),
                kind,
            ),
        ));
    }
    if equations.is_empty() {
        return fact.clone();
    }
    fn rewrite_term(
        term: &Bitvector32Term,
        equations: &[(Bitvector32Term, Bitvector32Term)],
    ) -> Bitvector32Term {
        let canonical = canonicalize_atomic_loads(term);
        for (value, load) in equations {
            if &canonical == value {
                return load.clone();
            }
        }
        match term {
            binary_term!(Bits32 @ format32, Add, left, right) => binary_node!(
                @ *format32,
                Add,
                Box::new(rewrite_term(left, equations)),
                Box::new(rewrite_term(right, equations)),
            ),
            binary_term!(Bits32 @ format32, Subtract, left, right) => binary_node!(
                @ *format32,
                Subtract,
                Box::new(rewrite_term(left, equations)),
                Box::new(rewrite_term(right, equations)),
            ),
            binary_term!(Bits32 @ format32, Multiply, left, right) => binary_node!(
                @ *format32,
                Multiply,
                Box::new(rewrite_term(left, equations)),
                Box::new(rewrite_term(right, equations)),
            ),
            other => other.clone(),
        }
    }
    let Proposition::ConditionIs(condition, value) = fact else {
        return fact.clone();
    };
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        (
            Box::new(rewrite_term(left, &equations)),
            Box::new(rewrite_term(right, &equations)),
        )
    };
    let rewritten = match condition {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left,
            right,
        } => {
            let (left, right) = binary(left, right);
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            }
        }
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left,
            right,
        } => {
            let (left, right) = binary(left, right);
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            }
        }
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        } => {
            let (left, right) = binary(left, right);
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left,
                right,
            }
        }
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        } => {
            let (left, right) = binary(left, right);
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            }
        }
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        } => {
            let (left, right) = binary(left, right);
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left,
                right,
            }
        }
        _ => return fact.clone(),
    };
    Proposition::ConditionIs(rewritten, *value)
}

/// Canonicalizes every load in a term for structural comparison: cached
/// cells resolve to their values and remaining loads use the canonical
/// memory for their pointer.
pub(crate) fn canonicalize_atomic_loads(term: &Bitvector32Term) -> Bitvector32Term {
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
        std::collections::HashMap<crate::kernel::SharedCMemory, CMemory>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    static ATOMIC_LOADS_CACHE: std::cell::RefCell<
        std::collections::HashMap<Bitvector32Term, Bitvector32Term>,
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

pub(crate) fn clear_provenance_memos() {
    DAG_LOAD_EQUALITY_POSITIVE_MEMO.with(|memo| memo.borrow_mut().clear());
    DAG_LOAD_EQUALITY_UNPROVEN_MEMO.with(|memo| memo.borrow_mut().clear());
}

pub(crate) fn clear_canonical_form_caches() {
    DEEP_MEMORY_CACHE.with(|cache| cache.borrow_mut().clear());
    ATOMIC_LOADS_CACHE.with(|cache| cache.borrow_mut().clear());
    // The resource tracker's per-snapshot version memos are canonical-form
    // caches too: they answer which point a term's name embeds.
    crate::kernel::resource_tracker::clear_version_memos();
}

/// Recursive `Hash` and `Eq` implementations make a whole-term cache key
/// unsafe at arbitrary depth. This iterative preflight controls only whether
/// memoization is used; canonicalization itself always traverses the complete
/// term. Embedded snapshots hash by interned identity, so only the explicit
/// term and pointer-offset structure matters here.
pub(crate) fn term_is_shallow_structural_cache_key(term: &Bitvector32Term) -> bool {
    const MAX_RECURSIVE_KEY_DEPTH: usize = 256;
    enum Node<'a> {
        Term(&'a Bitvector32Term, usize),
        Condition(&'a ConditionTerm, usize),
        Offset(&'a PointerOffsetTerm, usize),
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
                Bitvector32Term::Constant(_)
                | Bitvector32Term::UInt32Constant(_)
                | Bitvector32Term::Variable(_)
                | Bitvector32Term::Int64Constant(_)
                | Bitvector32Term::UInt64Constant(_)
                | Bitvector32Term::MachineIntegerConstant(_) => {}
                Bitvector32Term::MemoryLoad(_, pointer, _) => {
                    pending.push(Node::Offset(&pointer.offset, depth + 1));
                }
                Bitvector32Term::PointerAddress(pointer, _) => {
                    pending.push(Node::Offset(&pointer.offset, depth + 1));
                }
                crate::kernel::binary_machine_term!(left, right) => {
                    pending.push(Node::Term(right, depth + 1));
                    pending.push(Node::Term(left, depth + 1));
                }
                Bitvector32Term::Float32Binary { left, right, .. }
                | Bitvector32Term::Float64Binary { left, right, .. } => {
                    pending.push(Node::Term(right, depth + 1));
                    pending.push(Node::Term(left, depth + 1));
                }
                crate::kernel::unary_machine_term!(value) => {
                    pending.push(Node::Term(value, depth + 1));
                }
                Bitvector32Term::BoolCast { value, .. } => {
                    pending.push(Node::Condition(value, depth + 1));
                }
                Bitvector32Term::If {
                    condition,
                    then_term,
                    else_term,
                } => {
                    pending.push(Node::Term(else_term, depth + 1));
                    pending.push(Node::Term(then_term, depth + 1));
                    pending.push(Node::Condition(condition, depth + 1));
                }
                Bitvector32Term::RangeFold {
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
                Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                    pending.extend(
                        arguments
                            .iter()
                            .map(|argument| Node::Term(argument, depth + 1)),
                    );
                }
                Bitvector32Term::ClickFunctionApplication { .. }
                | Bitvector32Term::AlgebraicMatch { .. }
                | Bitvector32Term::IntegerToMachine { .. } => {}
            },
            Node::Condition(condition, depth) => match condition {
                ConditionTerm::PointerValueEqual(_, _) => return false,

                ConditionTerm::AlgebraicEqual(_, _) => return false,
                ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {}
                crate::kernel::integer_comparison_condition!(_, _) => return false,
                crate::kernel::binary_bitvector_condition!(left, right) => {
                    pending.push(Node::Term(right, depth + 1));
                    pending.push(Node::Term(left, depth + 1));
                }
                ConditionTerm::Float32(float_condition)
                | ConditionTerm::Float64(float_condition) => match float_condition {
                    CFloatCondition::Comparison { left, right, .. } => {
                        pending.push(Node::Term(right, depth + 1));
                        pending.push(Node::Term(left, depth + 1));
                    }
                    CFloatCondition::Classification { value, .. } => {
                        pending.push(Node::Term(value, depth + 1));
                    }
                },
                ConditionTerm::PointerOffsetEqual(left, right) => {
                    pending.push(Node::Offset(right, depth + 1));
                    pending.push(Node::Offset(left, depth + 1));
                }
                ConditionTerm::PointerEqual(left, right) => {
                    pending.push(Node::Offset(&right.offset, depth + 1));
                    pending.push(Node::Offset(&left.offset, depth + 1));
                }
                // As a word-valued Click application, whose arguments are
                // keyed by the application's interned identity.
                ConditionTerm::BoolApplication(_) => {}
                ConditionTerm::BoolIf {
                    condition,
                    then_condition,
                    else_condition,
                } => {
                    pending.push(Node::Condition(else_condition, depth + 1));
                    pending.push(Node::Condition(then_condition, depth + 1));
                    pending.push(Node::Condition(condition, depth + 1));
                }
                ConditionTerm::BoolEqual(left, right) => {
                    pending.push(Node::Condition(right, depth + 1));
                    pending.push(Node::Condition(left, depth + 1));
                }
                ConditionTerm::BoolLoad(_, pointer) => {
                    pending.push(Node::Offset(&pointer.offset, depth + 1));
                }
            },
            Node::Offset(offset, depth) => match offset {
                PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
                PointerOffsetTerm::Add(left, right) => {
                    pending.push(Node::Offset(right, depth + 1));
                    pending.push(Node::Offset(left, depth + 1));
                }
                PointerOffsetTerm::Int32Scaled { value, .. }
                | PointerOffsetTerm::Int64Scaled { value, .. } => {
                    pending.push(Node::Term(value, depth + 1));
                }
            },
        }
    }
    true
}

enum AtomicCanonicalizationTask<'a> {
    Visit(&'a Bitvector32Term),
    VisitCondition(&'a ConditionTerm),
    VisitOffset(&'a PointerOffsetTerm),
    RebuildBinary(BitvectorBinaryOp),
    RebuildUnary(BitvectorUnaryOp),
    RebuildConditionBinary(BitvectorComparisonOp),
    RebuildFloatCondition {
        is_float64: bool,
        condition: CFloatCondition,
        term_count: usize,
    },
    RebuildPointerOffsetEqual,
    RebuildPointerEqual {
        left_block: PointerBlock,
        right_block: PointerBlock,
    },
    RebuildOffsetAdd,
    RebuildInt32Scaled(i64),
    RebuildInt64Scaled {
        byte_width: i64,
        unsigned: bool,
    },
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

/// The integer a snapshot's own cell at `pointer` gives a `kind` read there,
/// when the cell is exactly that read and holds something other than `load`
/// itself. A cell of another kind holds other bytes or another number than
/// the read returns, so it answers nothing.
fn cell_integer_for_read(
    memory: &CMemory,
    pointer: &Pointer,
    kind: LoadKind,
    load: &Bitvector32Term,
) -> Option<Bitvector32Term> {
    let CExpressionOutcome::Value(cell) = memory.load(pointer) else {
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
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    let origin = |term: &Bitvector32Term| match term {
        Bitvector32Term::Variable(variable) => {
            crate::kernel::eval::registered_load_origin_term_for_variable(variable)
        }
        Bitvector32Term::MemoryLoad(..) => Some(term.clone()),
        _ => None,
    };
    let (Some(left), Some(right)) = (origin(left), origin(right)) else {
        return false;
    };
    if !matches!(
        (&left, &right),
        (
            Bitvector32Term::MemoryLoad(_, _, LoadKind::Bits64),
            Bitvector32Term::MemoryLoad(_, _, LoadKind::Bits64)
        )
    ) {
        return false;
    }
    crate::kernel::canonical_term(&left) == crate::kernel::canonical_term(&right)
        && !crate::kernel::reasoning::load_equality_refuted_by_history(&left, &right, assumptions)
}

/// Check a wide read against its recorded value under explicitly selected
/// premises. The typed memory walk must preserve the complete eight-byte
/// access across every effect; it cannot infer a value from a partial store.
pub(crate) fn wide_read_has_recorded_value(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    let origin = |term: &Bitvector32Term| match term {
        Bitvector32Term::Variable(variable) => {
            crate::kernel::eval::registered_load_origin_term_for_variable(variable)
        }
        Bitvector32Term::MemoryLoad(..) => Some(term.clone()),
        _ => None,
    };
    let left_origin = origin(left);
    let right_origin = origin(right);
    // A load identity can occur in several model arms. A producer records
    // the complete load expression it just named, independently of the name's
    // first live origin. Check those selected observations, then retain the
    // original route for facts whose earlier origin is the useful one.
    let latest = |term: &Bitvector32Term| match term {
        Bitvector32Term::Variable(variable) => {
            crate::kernel::eval::latest_wide_load_observation(variable)
        }
        Bitvector32Term::MemoryLoad(..) => Some(term.clone()),
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
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    left_origin: Option<&Bitvector32Term>,
    right_origin: Option<&Bitvector32Term>,
    assumptions: &PureFactContext,
) -> bool {
    if left_origin.is_none() && right_origin.is_none() {
        return false;
    }
    if left_origin
        .iter()
        .chain(right_origin.iter())
        .any(|term| !matches!(term, Bitvector32Term::MemoryLoad(_, _, LoadKind::Bits64)))
    {
        return false;
    }
    // Wide reads do not enter the int32 congruence graph. Two spellings of
    // one address can nevertheless read the same eight bytes: first check
    // the selected pointer equality, then retain both reads' memory history.
    // A cached read may name an earlier snapshot than its surface expression,
    // so a shared current snapshot is sufficient but not necessary.
    if let (
        Some(Bitvector32Term::MemoryLoad(left_memory, left_pointer, LoadKind::Bits64)),
        Some(Bitvector32Term::MemoryLoad(right_memory, right_pointer, LoadKind::Bits64)),
    ) = (left_origin, right_origin)
        && crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
            left_pointer,
            right_pointer,
            assumptions,
        )
    {
        if left_memory == right_memory {
            return true;
        }
        if let (Some(left_cell), Some(right_cell)) = (
            bounded_recorded_cell_source(left_memory, left_pointer, 8, assumptions, 64),
            bounded_recorded_cell_source(right_memory, right_pointer, 8, assumptions, 64),
        ) && left_cell.node() == right_cell.node()
        {
            return true;
        }
    }
    let stored_value_matches = |read: Option<&Bitvector32Term>, other: &Bitvector32Term| {
        let Some(Bitvector32Term::MemoryLoad(memory, pointer, LoadKind::Bits64)) = read else {
            return false;
        };
        // A simple read-value normalization must not scan the whole path.
        // Longer frames need an explicit intervening proof step.
        let (producer, resolution) =
            bounded_recorded_cell_resolution(memory, pointer, 8, assumptions, 64);
        let value = resolution.as_ref().and_then(|(cell, _)| {
            cell.resolved_value(pointer, LoadKind::Bits64).or_else(|| {
                // The cheap history classifier may stop at a store whose address
                // uses a recorded pointer-load identity. Check that one endpoint
                // with the full pointer matcher; never search earlier writes or
                // accept an overlapping store of a different width.
                let step = cell.node().derivation()?;
                let CMemoryDerivation::Store {
                    pointer: write,
                    value,
                    ..
                } = step.as_ref()
                else {
                    return None;
                };
                (LoadKind::Bits64.reads_value(value)
                    && crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
                        write,
                        pointer,
                        assumptions,
                    ))
                .then(|| value.clone())
            })
        });
        // Compare only a complete typed word in the current native-width graph.
        let equal = match value.as_ref().map(CValue::numeric_value) {
            Some(CValue::Int64(word) | CValue::UInt64(word)) => {
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
                                CellWalkStop::CommonSnapshot => "common snapshot reached",
                                CellWalkStop::RetainedValue => {
                                    "retained typed value before cache forgetting"
                                }
                                CellWalkStop::OldestRecorded => "oldest recorded snapshot reached",
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
    left: &Bitvector32Term,
    right: &Bitvector32Term,
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
    let origin = |term: &Bitvector32Term| match term {
        Bitvector32Term::Variable(variable) => {
            crate::kernel::eval::registered_load_origin_term_for_variable(variable)
        }
        Bitvector32Term::MemoryLoad(..) => Some(term.clone()),
        _ => None,
    };
    let stored_value_matches = |read: Option<Bitvector32Term>, other: &Bitvector32Term| {
        let Some(Bitvector32Term::MemoryLoad(memory, pointer, kind)) = read else {
            return false;
        };
        if !matches!(
            kind,
            LoadKind::Int8 | LoadKind::UInt8 | LoadKind::Int16 | LoadKind::UInt16 | LoadKind::Int32
        ) {
            return false;
        }
        let (_, resolution) =
            bounded_recorded_cell_resolution(&memory, &pointer, kind.byte_width(), assumptions, 64);
        let Some(value) = resolution.and_then(|(cell, _)| cell.resolved_value(&pointer, kind))
        else {
            return false;
        };
        let word = match value {
            CValue::Bool(word)
            | CValue::Int8(word)
            | CValue::Int16(word)
            | CValue::Int32(word)
            | CValue::UInt8(word)
            | CValue::UInt16(word)
            | CValue::UInt32(word) => word,
            _ => return false,
        };
        &word == other
            || assumptions.decide(&ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(word),
                right: Box::new(other.clone()),
            }) == Some(true)
    };
    stored_value_matches(origin(left), right) || stored_value_matches(origin(right), left)
}

/// Whether the read of `value_type` at `pointer` in `memory` ends, by the
/// same bounded walk read against the cited conditions only, at a store that
/// wrote its whole width: that read is of written bytes.
pub(crate) fn read_is_of_a_recorded_store(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
    assumptions: &PureFactContext,
) -> bool {
    let Some(kind) = LoadKind::of_type(value_type) else {
        return false;
    };
    let memory = crate::kernel::intern_c_memory_ref(memory);
    let (_, resolution) =
        bounded_recorded_cell_resolution(&memory, pointer, kind.byte_width(), assumptions, 64);
    matches!(
        resolution,
        Some((ref cell @ MemoryDagCell::Stored { .. }, _)) if cell.resolved_value(pointer, kind).is_some()
    )
}

/// Deep, assumption-free canonical form for a term: every load resolves its
/// cached cell or canonicalizes its snapshot and pointer, at every depth,
/// including inside conditionals, folds, and pointer offsets. Two forms
/// of the same value produced from different memory snapshots canonicalize
/// identically whenever the difference is representational. The walk is
/// over the term and the values its loads resolve to, each recorded before
/// the snapshot that holds it, so it is finite with no depth cut.
pub(super) fn canonicalize_atomic_loads_deep(term: &Bitvector32Term) -> Bitvector32Term {
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
                    Bitvector32Term::Constant(_)
                    | Bitvector32Term::UInt32Constant(_)
                    | Bitvector32Term::Variable(_)
                    | Bitvector32Term::Int64Constant(_)
                    | Bitvector32Term::UInt64Constant(_)
                    | Bitvector32Term::MachineIntegerConstant(_) => results.push(term.clone()),
                    Bitvector32Term::PointerAddress(_, _) => results.push(term.clone()),
                    Bitvector32Term::MemoryLoad(memory, pointer, kind) => {
                        let kind = *kind;
                        let canonical_pointer = canonicalize_pointer_loads(pointer);
                        let resolved =
                            cell_integer_for_read(memory, &canonical_pointer, kind, term)
                                .or_else(|| cell_integer_for_read(memory, pointer, kind, term));
                        let Some(mut value) = resolved else {
                            // Name the cell by its version before restricting
                            // the snapshot: the restriction is a fresh intern
                            // with no derivation, so a version walk over it
                            // could not cross anything. Walking the original
                            // snapshot lets two loads of one unwritten cell at
                            // different points share one canonical form.
                            let version = cell_version_point(
                                memory,
                                &canonical_pointer,
                                crate::kernel::load_term_access_width(
                                    memory,
                                    &canonical_pointer,
                                    kind,
                                ),
                            );
                            let version = version.as_ref().unwrap_or(memory);
                            results.push(Bitvector32Term::MemoryLoad(
                                canonical_projected_load_memory(version, &canonical_pointer),
                                Box::new(canonical_pointer),
                                kind,
                            ));
                            continue;
                        };

                        // A materialized cell may itself contain a load from
                        // another snapshot. Follow that root-load chain here
                        // rather than recursively entering one Rust frame per
                        // cell. Composite recorded values re-enter the normal
                        // structural worklist below.
                        loop {
                            let Bitvector32Term::MemoryLoad(next_memory, next_pointer, next_kind) =
                                &value
                            else {
                                results.push(canonicalize_atomic_loads_deep(&value));
                                break;
                            };
                            let next_kind = *next_kind;
                            let canonical_pointer = canonicalize_pointer_loads(next_pointer);
                            let resolved = cell_integer_for_read(
                                next_memory,
                                &canonical_pointer,
                                next_kind,
                                &value,
                            )
                            .or_else(|| {
                                cell_integer_for_read(next_memory, next_pointer, next_kind, &value)
                            });
                            if let Some(next) = resolved {
                                value = next;
                                continue;
                            }
                            let version = cell_version_point(
                                next_memory,
                                &canonical_pointer,
                                crate::kernel::load_term_access_width(
                                    next_memory,
                                    &canonical_pointer,
                                    next_kind,
                                ),
                            );
                            let version = version.as_ref().unwrap_or(next_memory);
                            results.push(Bitvector32Term::MemoryLoad(
                                canonical_projected_load_memory(version, &canonical_pointer),
                                Box::new(canonical_pointer),
                                next_kind,
                            ));
                            break;
                        }
                    }
                    Bitvector32Term::If {
                        condition,
                        then_term,
                        else_term,
                    } => {
                        tasks.push(AtomicCanonicalizationTask::RebuildIf);
                        tasks.push(AtomicCanonicalizationTask::Visit(else_term));
                        tasks.push(AtomicCanonicalizationTask::Visit(then_term));
                        tasks.push(AtomicCanonicalizationTask::VisitCondition(condition));
                    }
                    Bitvector32Term::RangeFold {
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
                    Bitvector32Term::PureFunctionApplication { name, arguments } => {
                        tasks.push(AtomicCanonicalizationTask::RebuildPureFunction {
                            name: name.clone(),
                            argument_count: arguments.len(),
                        });
                        for argument in arguments.iter().rev() {
                            tasks.push(AtomicCanonicalizationTask::Visit(argument));
                        }
                    }
                    // A `Bool`'s cast is kept as built, as the `Bool` forms are.
                    Bitvector32Term::ClickFunctionApplication { .. }
                    | Bitvector32Term::AlgebraicMatch { .. }
                    | Bitvector32Term::BoolCast { .. }
                    | Bitvector32Term::IntegerToMachine { .. } => results.push(term.clone()),
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
                ConditionTerm::AlgebraicEqual(_, _) | ConditionTerm::PointerValueEqual(..) => {
                    condition_results.push(condition.clone())
                }
                crate::kernel::integer_comparison_condition!(_, _) => {
                    condition_results.push(condition.clone())
                }
                ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {
                    condition_results.push(condition.clone())
                }
                // `Bool` values are kept as built, as algebraic equalities are.
                condition if condition.is_bool_value_form() => {
                    condition_results.push(condition.clone())
                }
                ConditionTerm::Float32(float_condition) => {
                    let term_count = match float_condition {
                        CFloatCondition::Comparison { .. } => 2,
                        CFloatCondition::Classification { .. } => 1,
                    };
                    tasks.push(AtomicCanonicalizationTask::RebuildFloatCondition {
                        is_float64: false,
                        condition: float_condition.clone(),
                        term_count,
                    });
                    match float_condition {
                        CFloatCondition::Comparison { left, right, .. } => {
                            tasks.push(AtomicCanonicalizationTask::Visit(right));
                            tasks.push(AtomicCanonicalizationTask::Visit(left));
                        }
                        CFloatCondition::Classification { value, .. } => {
                            tasks.push(AtomicCanonicalizationTask::Visit(value));
                        }
                    }
                }
                ConditionTerm::Float64(float_condition) => {
                    let term_count = match float_condition {
                        CFloatCondition::Comparison { .. } => 2,
                        CFloatCondition::Classification { .. } => 1,
                    };
                    tasks.push(AtomicCanonicalizationTask::RebuildFloatCondition {
                        is_float64: true,
                        condition: float_condition.clone(),
                        term_count,
                    });
                    match float_condition {
                        CFloatCondition::Comparison { left, right, .. } => {
                            tasks.push(AtomicCanonicalizationTask::Visit(right));
                            tasks.push(AtomicCanonicalizationTask::Visit(left));
                        }
                        CFloatCondition::Classification { value, .. } => {
                            tasks.push(AtomicCanonicalizationTask::Visit(value));
                        }
                    }
                }
                ConditionTerm::PointerOffsetEqual(left, right) => {
                    tasks.push(AtomicCanonicalizationTask::RebuildPointerOffsetEqual);
                    tasks.push(AtomicCanonicalizationTask::VisitOffset(right));
                    tasks.push(AtomicCanonicalizationTask::VisitOffset(left));
                }
                ConditionTerm::PointerEqual(left, right) => {
                    tasks.push(AtomicCanonicalizationTask::RebuildPointerEqual {
                        left_block: left.block.clone(),
                        right_block: right.block.clone(),
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
            AtomicCanonicalizationTask::VisitOffset(offset) => match offset {
                PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {
                    offset_results.push(offset.clone())
                }
                PointerOffsetTerm::Add(left, right) => {
                    tasks.push(AtomicCanonicalizationTask::RebuildOffsetAdd);
                    tasks.push(AtomicCanonicalizationTask::VisitOffset(right));
                    tasks.push(AtomicCanonicalizationTask::VisitOffset(left));
                }
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    tasks.push(AtomicCanonicalizationTask::RebuildInt32Scaled(*byte_width));
                    tasks.push(AtomicCanonicalizationTask::Visit(value));
                }
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => {
                    tasks.push(AtomicCanonicalizationTask::RebuildInt64Scaled {
                        byte_width: *byte_width,
                        unsigned: *unsigned,
                    });
                    tasks.push(AtomicCanonicalizationTask::Visit(value));
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
                let smart =
                    op.is_float() || matches!(op, BitvectorUnaryOp::MachineIntegerCast { .. });
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
                    ConditionTerm::Float64(rebuilt)
                } else {
                    ConditionTerm::Float32(rebuilt)
                });
            }
            AtomicCanonicalizationTask::RebuildPointerOffsetEqual => {
                let right = offset_results.pop().expect("visited right pointer offset");
                let left = offset_results.pop().expect("visited left pointer offset");
                condition_results.push(ConditionTerm::PointerOffsetEqual(
                    Box::new(left),
                    Box::new(right),
                ));
            }
            AtomicCanonicalizationTask::RebuildPointerEqual {
                left_block,
                right_block,
            } => {
                let right = offset_results.pop().expect("visited right pointer offset");
                let left = offset_results.pop().expect("visited left pointer offset");
                condition_results.push(ConditionTerm::PointerEqual(
                    Box::new(Pointer {
                        block: left_block,
                        offset: left,
                    }),
                    Box::new(Pointer {
                        block: right_block,
                        offset: right,
                    }),
                ));
            }
            AtomicCanonicalizationTask::RebuildOffsetAdd => {
                let right = offset_results.pop().expect("visited right pointer offset");
                let left = offset_results.pop().expect("visited left pointer offset");
                offset_results.push(PointerOffsetTerm::add(left, right));
            }
            AtomicCanonicalizationTask::RebuildInt32Scaled(byte_width) => {
                let value = results.pop().expect("visited scaled term");
                offset_results.push(PointerOffsetTerm::scale_int32(value, byte_width));
            }
            AtomicCanonicalizationTask::RebuildInt64Scaled {
                byte_width,
                unsigned,
            } => {
                let value = results.pop().expect("visited scaled term");
                offset_results.push(PointerOffsetTerm::scale_int64(value, byte_width, unsigned));
            }
            AtomicCanonicalizationTask::RebuildIf => {
                let else_term = results.pop().expect("visited else term");
                let then_term = results.pop().expect("visited then term");
                let condition = condition_results.pop().expect("visited condition");
                results.push(Bitvector32Term::If {
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
                results.push(Bitvector32Term::RangeFold {
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
                results.push(Bitvector32Term::PureFunctionApplication { name, arguments });
            }
        }
    }
    assert_eq!(results.len(), 1, "canonicalization produces one term");
    assert!(condition_results.is_empty());
    assert!(offset_results.is_empty());
    results.pop().unwrap()
}

/// Canonicalizes the loads inside a pointer's offset.
pub(super) fn canonicalize_pointer_loads(pointer: &Pointer) -> Pointer {
    enum OffsetTask<'a> {
        Visit(&'a PointerOffsetTerm),
        RebuildAdd,
    }
    let mut tasks = vec![OffsetTask::Visit(&pointer.offset)];
    let mut results = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            OffsetTask::Visit(offset) => match offset {
                PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {
                    results.push(offset.clone())
                }
                PointerOffsetTerm::Add(left, right) => {
                    tasks.push(OffsetTask::RebuildAdd);
                    tasks.push(OffsetTask::Visit(right));
                    tasks.push(OffsetTask::Visit(left));
                }
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    results.push(PointerOffsetTerm::scale_int32(
                        canonicalize_atomic_loads_deep(value),
                        *byte_width,
                    ));
                }
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => results.push(PointerOffsetTerm::scale_int64(
                    canonicalize_atomic_loads_deep(value),
                    *byte_width,
                    *unsigned,
                )),
            },
            OffsetTask::RebuildAdd => {
                let right = results.pop().expect("visited right offset");
                let left = results.pop().expect("visited left offset");
                results.push(PointerOffsetTerm::add(left, right));
            }
        }
    }
    Pointer {
        block: pointer.block.clone(),
        offset: results.pop().expect("canonicalization produces one offset"),
    }
}

/// Compares two condition facts operandwise under memory-resolution
/// equality, so forms that differ only in provably-irrelevant cached
/// cells compare equal.
pub(crate) fn c_condition_facts_equivalent_for_memory_resolution(
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
    let operands = match (left, right) {
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            },
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: c,
                right: d,
            },
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            },
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: c,
                right: d,
            },
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            },
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: c,
                right: d,
            },
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            },
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: c,
                right: d,
            },
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left: a,
                right: b,
            },
            ConditionTerm::Compare {
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

    fn var(id: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(id))
    }

    fn less_than(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::signed_less_than(left, right), true)
    }

    #[test]
    fn condition_fact_operands_use_graph_with_snapshot_scope() {
        let _session = crate::kernel::VerificationSession::enter();
        let before = crate::kernel::intern_c_memory(CMemory::new().with_block("fact-graph", 8));
        let pointer = |index| Pointer {
            block: "fact-graph".into(),
            offset: PointerOffsetTerm::scale_int32(index, 4),
        };
        let load = |memory: &SharedCMemory, index| {
            Bitvector32Term::Variable(crate::kernel::load_variable_for_cell_with_origin(
                memory,
                &pointer(index),
                crate::kernel::LoadKind::Int32,
                4,
                memory,
            ))
        };
        let (a, b) = (var(91), var(92));
        let after = crate::kernel::intern_c_memory(before.memory().clone().store(
            pointer(b.clone()),
            CValue::Int32(Bitvector32Term::Constant(9)),
        ));
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let source = less_than(sum(load(&before, a.clone())), var(93));
        let target = less_than(sum(load(&before, b.clone())), var(93));
        let later = less_than(sum(load(&after, b.clone())), var(93));
        let premise = ConditionTerm::equal(a, b.clone());
        let parent = PureFactContext::new();
        let branch = parent.clone().assume_condition(premise.clone(), true);
        let _scope = branch.enter_id_scope();

        PureFactContext::reset_bitvector_equality_index_fact_visits();
        assert!(c_condition_facts_equivalent_for_memory_resolution(
            &source, &target, &branch,
        ));
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(!c_condition_facts_equivalent_for_memory_resolution(
            &source, &later, &branch,
        ));
        assert!(!c_condition_facts_equivalent_for_memory_resolution(
            &source, &target, &parent,
        ));
        let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(premise, true));
        assert!(!c_condition_facts_equivalent_for_memory_resolution(
            &source, &target, &withdrawn,
        ));
        let false_target = Proposition::ConditionIs(
            ConditionTerm::signed_less_than(sum(load(&before, b.clone())), var(93)),
            false,
        );
        assert!(!c_condition_facts_equivalent_for_memory_resolution(
            &source,
            &false_target,
            &branch,
        ));
        let equal_target = Proposition::ConditionIs(
            ConditionTerm::equal(sum(load(&before, b.clone())), var(93)),
            true,
        );
        assert!(!c_condition_facts_equivalent_for_memory_resolution(
            &source,
            &equal_target,
            &branch,
        ));
        let right_premise = ConditionTerm::equal(var(93), var(94));
        let both = branch.assume_condition(right_premise.clone(), true);
        let target_right = less_than(sum(load(&before, b.clone())), var(94));
        assert!(c_condition_facts_equivalent_for_memory_resolution(
            &source,
            &target_right,
            &both,
        ));
        let equal_source = Proposition::ConditionIs(
            ConditionTerm::equal(sum(load(&before, var(91))), var(93)),
            true,
        );
        let equal_target =
            Proposition::ConditionIs(ConditionTerm::equal(sum(load(&before, b)), var(94)), true);
        assert!(c_condition_facts_equivalent_for_memory_resolution(
            &equal_source,
            &equal_target,
            &both,
        ));
        let right_withdrawn =
            both.without_exact_fact(&Proposition::ConditionIs(right_premise, true));
        assert!(!c_condition_facts_equivalent_for_memory_resolution(
            &source,
            &target_right,
            &right_withdrawn,
        ));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../scaling_tests/kernel/memory_provenance/condition_fact_graph_equivalence_tests.rs"
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
            let store = fact.certified_store_data()?;
            let value = match store.value.numeric_value() {
                CValue::PointerInteger(_) => unreachable!("numeric projection"),
                CValue::Int8(term) => term.clone(),
                CValue::Bool(term)
                | CValue::Int16(term)
                | CValue::Int32(term)
                | CValue::UInt8(term)
                | CValue::UInt16(term)
                | CValue::UInt32(term)
                | CValue::Int64(term)
                | CValue::UInt64(term)
                | CValue::Int128(term)
                | CValue::UInt128(term) => term.clone(),
                CValue::Void
                | CValue::Pointer(_)
                | CValue::Parameter(_)
                | CValue::Float32(_)
                | CValue::Float64(_) => {
                    return None;
                }
            };
            // What the store wrote is the read of its own kind there, as a
            // word (rule K5).
            let kind = LoadKind::of_value(&store.value)?.word_kind();
            Some(Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(Bitvector32Term::memory_read(
                        crate::kernel::intern_c_memory(store.after.clone()),
                        store.pointer.clone(),
                        kind,
                    )),
                    right: Box::new(value),
                },
                true,
            ))
        })
        .collect()
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
                CValue::Void => return None,
                value => value.byte_width(),
            };
            Some(Proposition::CMemoryLoadable {
                memory: store.after.clone(),
                base: store.pointer.clone(),
                bytes: Bitvector32Term::Constant(byte_width),
                wide: false,
            })
        })
        .collect()
}

pub(crate) fn c_condition_fact_memories(fact: &Proposition) -> Vec<CMemory> {
    let Proposition::ConditionIs(condition, _) = fact else {
        return Vec::new();
    };
    let mut memories = Vec::new();
    collect_condition_memories(condition, &mut memories);
    memories
        .into_iter()
        .map(|memory| memory.as_ref().clone())
        .collect()
}

fn collect_condition_memories(condition: &ConditionTerm, memories: &mut Vec<SharedCMemory>) {
    let mut collect_binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        collect_bitvector_memories(left, memories);
        collect_bitvector_memories(right, memories);
    };
    match condition {
        ConditionTerm::PointerValueEqual(left, right) => {
            for pointer in left.pointers().chain(right.pointers()) {
                if let PointerBlock::PureFunctionApplication(application) = &pointer.block
                    && let Some(bits) = application.integer_address_bits()
                {
                    collect_bitvector_memories(bits, memories);
                }
                collect_pointer_offset_memories(&pointer.offset, memories);
            }
        }

        ConditionTerm::AlgebraicEqual(left, right) => {
            left.for_each_bitvector_term(|term| collect_bitvector_memories(term, memories));
            right.for_each_bitvector_term(|term| collect_bitvector_memories(term, memories));
        }
        crate::kernel::binary_bitvector_condition!(left, right) => collect_binary(left, right),
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            float_condition
                .for_each_bitvector_term(|term| collect_bitvector_memories(term, memories));
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_pointer_offset_memories(left, memories);
            collect_pointer_offset_memories(right, memories);
        }
        ConditionTerm::PointerEqual(left, right) => {
            for pointer in [left, right] {
                if let PointerBlock::PureFunctionApplication(application) = &pointer.block
                    && let Some(bits) = application.integer_address_bits()
                {
                    collect_bitvector_memories(bits, memories);
                }
                if let PointerBlock::Symbolic(variable) = &pointer.block
                    && let Some((origin, _)) =
                        crate::kernel::eval::registered_load_origin_for_variable(variable)
                    && !memories.contains(&origin)
                {
                    memories.push(origin);
                }
                collect_pointer_offset_memories(&pointer.offset, memories);
            }
        }
        ConditionTerm::Constant(_)
        | ConditionTerm::Variable(_)
        | crate::kernel::integer_comparison_condition!(_, _) => {}
        // As a word-valued Click application.
        ConditionTerm::BoolApplication(_) => {}
        ConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => {
            for condition in [condition, then_condition, else_condition] {
                collect_condition_memories(condition, memories);
            }
        }
        ConditionTerm::BoolEqual(left, right) => {
            collect_condition_memories(left, memories);
            collect_condition_memories(right, memories);
        }
        ConditionTerm::BoolLoad(memory, pointer) => {
            if !memories.contains(memory) {
                memories.push(memory.clone());
            }
            collect_pointer_offset_memories(&pointer.offset, memories);
        }
    }
}

fn collect_pointer_offset_memories(offset: &PointerOffsetTerm, memories: &mut Vec<SharedCMemory>) {
    offset.for_each_scaled_value(|value| collect_bitvector_memories(value, memories));
}

fn collect_bitvector_memories(term: &Bitvector32Term, memories: &mut Vec<SharedCMemory>) {
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::UInt32Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_)
        | Bitvector32Term::Variable(_) => {}
        Bitvector32Term::PointerAddress(_, _) => {}
        Bitvector32Term::MemoryLoad(memory, _, _) => {
            if !memories.contains(memory) {
                memories.push(memory.clone());
            }
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_memories(condition, memories);
            collect_bitvector_memories(then_term, memories);
            collect_bitvector_memories(else_term, memories);
        }
        Bitvector32Term::RangeFold {
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
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_memories(argument, memories);
            }
        }
        Bitvector32Term::ClickFunctionApplication { .. } => {}
        Bitvector32Term::IntegerToMachine { .. } => {}
        Bitvector32Term::BoolCast { value, .. } => collect_condition_memories(value, memories),
        Bitvector32Term::AlgebraicMatch { arms, .. } => {
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

fn transport_framed_atomic_condition(
    condition: &ConditionTerm,
    after: &CMemory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<ConditionTerm> {
    if crate::kernel::assumptions::reasoning_interrupted() {
        return None;
    }
    Some(match condition {
        // Do not claim a snapshot bridge through an opaque algebraic value.
        ConditionTerm::PointerValueEqual(left, right) => ConditionTerm::PointerValueEqual(
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
        ConditionTerm::AlgebraicEqual(_, _) => return None,
        ConditionTerm::Float32(float_condition) => {
            ConditionTerm::Float32(float_condition.try_map_bitvector_terms(|term| {
                transport_framed_atomic_bitvector(term, after, assumptions)
            })?)
        }
        ConditionTerm::Float64(float_condition) => {
            ConditionTerm::Float64(float_condition.try_map_bitvector_terms(|term| {
                transport_framed_atomic_bitvector(term, after, assumptions)
            })?)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => ConditionTerm::pointer_offset_equal(
            transport_framed_atomic_pointer_offset(left, after, assumptions)?,
            transport_framed_atomic_pointer_offset(right, after, assumptions)?,
        ),
        ConditionTerm::PointerEqual(left, right) => ConditionTerm::pointer_equal(
            transport_framed_atomic_pointer(left, after, assumptions)?,
            transport_framed_atomic_pointer(right, after, assumptions)?,
        ),
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => return None,
        // Mathematical integers carry no snapshot-dependent loads, so this
        // memory transport path has no authority to rewrite them.
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
    value: &CPointerValue,
    after: &CMemory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<CPointerValue> {
    // Only reconstructed complete words need their read designation moved
    // alongside their numeric address. Ordinary pointers keep their origin.
    let reconstructed_word = value.pointer().integer_address_bits().is_some();
    value.try_map_pointers(|pointer| {
        if reconstructed_word && let Some(read) = pointer.as_loaded_value() {
            // Use the complete word's cached version, as its read producer
            // does, so unrelated history is not traversed for its designation.
            let after = crate::kernel::intern_c_memory_ref(after);
            let version = cell_version_point(&after, &read.defining_address, C_POINTER_BYTE_WIDTH)
                .unwrap_or(after);
            let mut target = Pointer::loaded_value(&version, &read.defining_address);
            target.offset = pointer.offset.clone();
            if assumptions.is_some_and(|(context, _)| {
                complete_pointer_reads_equal_across_frame(pointer, &target, context)
            }) {
                return Some(target);
            }
        }
        transport_framed_atomic_pointer(pointer, after, assumptions)
    })
}

fn transport_framed_atomic_pointer(
    pointer: &Pointer,
    after: &CMemory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<Pointer> {
    let block = if let PointerBlock::Symbolic(variable) = &pointer.block {
        // An opaque pointer-typed read puts its load identity in the block,
        // rather than in an offset within the storage object's provenance.
        // Transport that identity using the same checked load-frame rule as
        // scalar load variables. Ordinary symbolic pointers have no producer
        // metadata and stay unchanged.
        match transport_framed_atomic_bitvector(
            &Bitvector32Term::Variable(*variable),
            after,
            assumptions,
        )? {
            Bitvector32Term::Variable(variable) => PointerBlock::Symbolic(variable),
            _ => return None,
        }
    } else if let PointerBlock::PureFunctionApplication(application) = &pointer.block
        && let Some(bits) = application.integer_address_bits()
    {
        // Numeric pointer reconstruction is a pure function of its complete
        // word. Carry loads inside that word across the same checked frame
        // as offset loads; cloning the block would retain the old snapshot.
        Pointer::integer_address(transport_framed_atomic_bitvector(bits, after, assumptions)?).block
    } else {
        pointer.block.clone()
    };
    Some(Pointer {
        block,
        offset: transport_framed_atomic_pointer_offset(&pointer.offset, after, assumptions)?,
    })
}

fn transport_framed_atomic_pointer_offset(
    offset: &PointerOffsetTerm,
    after: &CMemory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<PointerOffsetTerm> {
    if crate::kernel::assumptions::reasoning_interrupted() {
        return None;
    }
    Some(match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => offset.clone(),
        PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::add(
            transport_framed_atomic_pointer_offset(left, after, assumptions)?,
            transport_framed_atomic_pointer_offset(right, after, assumptions)?,
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => PointerOffsetTerm::scale_int32(
            transport_framed_atomic_bitvector(value, after, assumptions)?,
            *byte_width,
        ),
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } => PointerOffsetTerm::scale_int64(
            transport_framed_atomic_bitvector(value, after, assumptions)?,
            *byte_width,
            *unsigned,
        ),
    })
}

fn transport_framed_atomic_bitvector(
    term: &Bitvector32Term,
    after: &CMemory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<Bitvector32Term> {
    if crate::kernel::assumptions::reasoning_interrupted() {
        return None;
    }
    Some(match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::UInt32Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_) => term.clone(),
        Bitvector32Term::PointerAddress(_, _) => term.clone(),
        Bitvector32Term::Variable(variable) => {
            // A load variable transports as the load it represents:
            // when frame evidence rewrites that load to the post-effect
            // snapshot, the fact is rewritten with the post-point load
            // variable. Content-addressed construction gives the same variable
            // to any later lowering at that snapshot. A defining equation
            // in the ambient assumptions carries the mint-time form,
            // whose live snapshot the frame checks can actually relate to
            // `after`; the registry's canonicalized form is the
            // fallback.
            // The registry's origin is the first live snapshot the variable
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
                    Bitvector32Term::Variable(renamed)
                } else {
                    term.clone()
                }
            } else {
                term.clone()
            }
        }
        Bitvector32Term::MemoryLoad(memory, pointer, kind) => {
            let transported_pointer = Pointer {
                block: pointer.block.clone(),
                offset: transport_framed_atomic_pointer_offset(
                    &pointer.offset,
                    after,
                    assumptions,
                )?,
            };
            if memories_match_for_pointer_load(memory, after, pointer)
                || memory_materializes_atomic_load(after, memory, pointer, *kind)
                || assumptions.is_some_and(|(assumptions, direct)| {
                    if direct {
                        c_memory_load_is_directly_unchanged(
                            memory,
                            after,
                            pointer,
                            *kind,
                            assumptions,
                        )
                    } else {
                        let left = Bitvector32Term::MemoryLoad(
                            memory.clone(),
                            Box::new(pointer.as_ref().clone()),
                            *kind,
                        );
                        let right = Bitvector32Term::MemoryLoad(
                            crate::kernel::intern_c_memory(after.clone()),
                            Box::new(transported_pointer.clone()),
                            *kind,
                        );
                        checked_atomic_load_equality(&left, &right, assumptions)
                    }
                })
            {
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(after.clone()),
                    Box::new(transported_pointer),
                    *kind,
                )
            } else {
                term.clone()
            }
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => Bitvector32Term::If {
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
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => Bitvector32Term::RangeFold {
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
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            Bitvector32Term::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| transport_framed_atomic_bitvector(argument, after, assumptions))
                    .collect::<Option<Vec<_>>>()?,
            }
        }
        Bitvector32Term::BoolCast { to, value } => Bitvector32Term::BoolCast {
            to: *to,
            value: Box::new(transport_framed_atomic_condition(
                value,
                after,
                assumptions,
            )?),
        },
        Bitvector32Term::ClickFunctionApplication { .. }
        | Bitvector32Term::AlgebraicMatch { .. }
        | Bitvector32Term::IntegerToMachine { .. } => term.clone(),
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

pub(crate) fn c_pointer_offsets_proven_equal_for_effect(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
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
    offset: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> PointerOffsetTerm {
    enum Task {
        Visit(PointerOffsetTerm),
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
                match offset {
                    PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {
                        results.push(offset)
                    }
                    PointerOffsetTerm::Add(left, right) => {
                        tasks.push(Task::RebuildAdd);
                        tasks.push(Task::Visit(*right));
                        tasks.push(Task::Visit(*left));
                    }
                    PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                        results.push(PointerOffsetTerm::scale_int32(
                            normalize_exact_memory_loads_in_bitvector(&value, assumptions),
                            byte_width,
                        ));
                    }
                    PointerOffsetTerm::Int64Scaled {
                        value,
                        byte_width,
                        unsigned,
                    } => {
                        results.push(PointerOffsetTerm::scale_int64(
                            normalize_exact_memory_loads_in_bitvector(&value, assumptions),
                            byte_width,
                            unsigned,
                        ));
                    }
                }
            }
            Task::RebuildAdd => {
                let right = results.pop().expect("visited right pointer offset");
                let left = results.pop().expect("visited left pointer offset");
                results.push(PointerOffsetTerm::add(left, right));
            }
        }
    }
    results
        .pop()
        .expect("normalization produces one pointer offset")
}

enum ExactLoadNormalizationTask {
    Visit(Bitvector32Term),
    RebuildBinary(BitvectorBinaryOp),
    RebuildUnary(BitvectorUnaryOp),
    RebuildIf(ConditionTerm),
    RebuildPureFunction { name: String, argument_count: usize },
    LeaveLoad(Bitvector32Term),
}

fn normalize_exact_memory_loads_in_bitvector_iterative(
    term: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> Bitvector32Term {
    #[allow(clippy::boxed_local)]
    fn push_binary(
        tasks: &mut Vec<ExactLoadNormalizationTask>,
        operator: BitvectorBinaryOp,
        left: Box<Bitvector32Term>,
        right: Box<Bitvector32Term>,
    ) {
        tasks.push(ExactLoadNormalizationTask::RebuildBinary(operator));
        tasks.push(ExactLoadNormalizationTask::Visit(*right));
        tasks.push(ExactLoadNormalizationTask::Visit(*left));
    }

    #[allow(clippy::boxed_local)]
    fn push_unary(
        tasks: &mut Vec<ExactLoadNormalizationTask>,
        operator: BitvectorUnaryOp,
        value: Box<Bitvector32Term>,
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
                    Bitvector32Term::MachineIntegerCast {
                        value,
                        source,
                        destination,
                    } => push_unary(
                        &mut tasks,
                        BitvectorUnaryOp::MachineIntegerCast {
                            source,
                            destination,
                        },
                        value,
                    ),

                    Bitvector32Term::Constant(_)
                    | Bitvector32Term::UInt32Constant(_)
                    | Bitvector32Term::Int64Constant(_)
                    | Bitvector32Term::UInt64Constant(_)
                    | Bitvector32Term::MachineIntegerConstant(_)
                    | Bitvector32Term::Variable(_) => results.push(term),
                    Bitvector32Term::Binary {
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
                    Bitvector32Term::Float32Negate(value) => {
                        push_unary(&mut tasks, BitvectorUnaryOp::Float32Negate, value)
                    }
                    Bitvector32Term::Float64Negate(value) => {
                        push_unary(&mut tasks, BitvectorUnaryOp::Float64Negate, value)
                    }
                    Bitvector32Term::Float32Binary {
                        operator,
                        left,
                        right,
                    } => push_binary(
                        &mut tasks,
                        BitvectorBinaryOp::Float32(operator),
                        left,
                        right,
                    ),
                    Bitvector32Term::Float64Binary {
                        operator,
                        left,
                        right,
                    } => push_binary(
                        &mut tasks,
                        BitvectorBinaryOp::Float64(operator),
                        left,
                        right,
                    ),
                    Bitvector32Term::Int64From32(value) => {
                        push_unary(&mut tasks, BitvectorUnaryOp::Int64From32, value)
                    }
                    Bitvector32Term::UInt64From32(value) => {
                        push_unary(&mut tasks, BitvectorUnaryOp::UInt64From32, value)
                    }
                    Bitvector32Term::UInt32From64(value) => {
                        push_unary(&mut tasks, BitvectorUnaryOp::UInt32From64, value)
                    }
                    Bitvector32Term::Int64FromUInt32(value) => {
                        push_unary(&mut tasks, BitvectorUnaryOp::Int64FromUInt32, value)
                    }
                    Bitvector32Term::UInt64FromInt32(value) => {
                        push_unary(&mut tasks, BitvectorUnaryOp::UInt64FromInt32, value)
                    }
                    Bitvector32Term::UInt64FromInt64(value) => {
                        push_unary(&mut tasks, BitvectorUnaryOp::UInt64FromInt64, value)
                    }
                    Bitvector32Term::Unary {
                        format,
                        op,
                        operand: value,
                    } => push_unary(&mut tasks, BitvectorUnaryOp::Machine(format, op), value),
                    Bitvector32Term::If {
                        condition,
                        then_term,
                        else_term,
                    } => {
                        tasks.push(ExactLoadNormalizationTask::RebuildIf(*condition));
                        tasks.push(ExactLoadNormalizationTask::Visit(*else_term));
                        tasks.push(ExactLoadNormalizationTask::Visit(*then_term));
                    }
                    Bitvector32Term::RangeFold { .. } | Bitvector32Term::BoolCast { .. } => {
                        results.push(term)
                    }
                    Bitvector32Term::PureFunctionApplication { name, arguments } => {
                        let argument_count = arguments.len();
                        tasks.push(ExactLoadNormalizationTask::RebuildPureFunction {
                            name,
                            argument_count,
                        });
                        for argument in arguments.into_iter().rev() {
                            tasks.push(ExactLoadNormalizationTask::Visit(argument));
                        }
                    }
                    Bitvector32Term::ClickFunctionApplication { .. }
                    | Bitvector32Term::AlgebraicMatch { .. }
                    | Bitvector32Term::IntegerToMachine { .. } => results.push(term),
                    Bitvector32Term::PointerAddress(_, _) => results.push(term),
                    load @ Bitvector32Term::MemoryLoad(_, _, _) => {
                        if !active_loads.insert(load.clone()) {
                            results.push(load);
                            continue;
                        }
                        let Bitvector32Term::MemoryLoad(memory, pointer, kind) = &load else {
                            unreachable!()
                        };
                        // The snapshot's own cell answers only a read of its
                        // kind: an `int32` cell is not a byte read's value.
                        let resolved = match memory.known_value(pointer) {
                            Some(CValue::Int32(value))
                                if *kind == LoadKind::Int32 && value != load =>
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
                results.push(Bitvector32Term::If {
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
                results.push(Bitvector32Term::PureFunctionApplication { name, arguments });
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
    term: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> Bitvector32Term {
    normalize_exact_memory_loads_in_bitvector_iterative(term, assumptions)
}

#[cfg(test)]
mod exact_load_normalization_tests {
    use super::*;

    fn load_chain(length: usize, tail: u32) -> Bitvector32Term {
        let pointer = Pointer {
            block: "normalization-load-chain".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        (0..length).fold(Bitvector32Term::Constant(tail), |value, _| {
            let memory = CMemory::new().store(pointer.clone(), CValue::Int32(value));
            Bitvector32Term::MemoryLoad(
                intern_c_memory(memory),
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Int32,
            )
        })
    }

    fn nested_add(length: usize, tail: Bitvector32Term) -> Bitvector32Term {
        (0..length).fold(tail, |term, _| {
            binary_node!(
                Int32,
                Add,
                Box::new(Bitvector32Term::Constant(0)),
                Box::new(term)
            )
        })
    }

    /// A snapshot's own cell answers a load term only when the cell is that
    /// read: a word cell is not the value of a byte read at its address, and
    /// a signed byte cell is not the value of an unsigned byte read. Every
    /// route that resolves a load against the snapshot it names — exact-load
    /// normalization, the deep canonical form, and the materialized-load
    /// frame — asks the same question, so one table pins all of them.
    #[test]
    fn a_snapshot_cell_answers_only_a_read_of_its_own_kind() {
        use crate::kernel::LoadKind;
        let pointer = Pointer {
            block: "kind-checked-cell".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let load = |memory: &CMemory, kind| {
            Bitvector32Term::MemoryLoad(
                intern_c_memory(memory.clone()),
                Box::new(pointer.clone()),
                kind,
            )
        };
        let word = CMemory::new().with_block("kind-checked-cell", 4).store(
            pointer.clone(),
            CValue::Int32(Bitvector32Term::Constant(256)),
        );
        let signed_byte = CMemory::new().with_block("kind-checked-cell", 4).store(
            pointer.clone(),
            CValue::Int8(Bitvector32Term::Constant(u32::MAX)),
        );
        let context = PureFactContext::new();
        for (memory, own, other, value) in [
            (
                &word,
                LoadKind::Int32,
                LoadKind::UInt8,
                Bitvector32Term::Constant(256),
            ),
            (
                &signed_byte,
                LoadKind::Int8,
                LoadKind::UInt8,
                Bitvector32Term::Constant(u32::MAX),
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
        let source = CMemory::new().with_block("kind-checked-cell", 4);
        let materialized = source
            .clone()
            .store(pointer.clone(), CValue::Int8(load(&source, LoadKind::Int8)));
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
            Bitvector32Term::Constant(29)
        );

        let offset = (0..80).fold(
            PointerOffsetTerm::Int32Scaled {
                value: Box::new(load_chain(80, 7)),
                byte_width: 4,
            },
            |offset, _| {
                PointerOffsetTerm::Add(Box::new(PointerOffsetTerm::Constant(0)), Box::new(offset))
            },
        );
        assert_eq!(
            normalize_exact_memory_loads_in_pointer_offset(&offset, &PureFactContext::new()),
            PointerOffsetTerm::Constant(28)
        );
    }
}

#[cfg(test)]
#[test]
fn effect_pointer_equality_retains_exact_loads_and_explicit_offset_facts() {
    let pointer = Pointer {
        block: "effect-offset".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(7)));
    let loaded = PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::MemoryLoad(
            intern_c_memory(memory),
            Box::new(pointer),
            crate::kernel::LoadKind::Int32,
        )),
        byte_width: 4,
    };
    assert!(c_pointer_offsets_proven_equal_for_effect(
        &loaded,
        &PointerOffsetTerm::Constant(28),
        &PureFactContext::new(),
    ));
    assert!(!c_pointer_offsets_proven_equal_for_effect(
        &loaded,
        &PointerOffsetTerm::Constant(32),
        &PureFactContext::new(),
    ));

    let left = PointerOffsetTerm::Variable(Variable(901));
    let right = PointerOffsetTerm::Variable(Variable(902));
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_offset_equal(left.clone(), right.clone()),
        true,
    );
    assert!(c_pointer_offsets_proven_equal_for_effect(
        &left, &right, &facts
    ));
    assert!(!c_pointer_offsets_proven_equal_for_effect(
        &left,
        &right,
        &PureFactContext::new()
    ));
    assert!(!c_pointer_offsets_proven_equal_for_effect(
        &left,
        &PointerOffsetTerm::Variable(Variable(903)),
        &facts,
    ));
}

#[cfg(test)]
#[test]
fn effect_pointer_equality_does_not_use_general_context_inconsistency() {
    // Surface planning; only this test reaches it from inside the kernel.
    use crate::surface::planning::proposition_search::PropositionSearch;
    let left = PointerOffsetTerm::Variable(Variable(911));
    let right = PointerOffsetTerm::Variable(Variable(912));
    let facts = PureFactContext::new().assume_condition(ConditionTerm::Constant(false), true);
    let goal = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(left.clone(), right.clone()),
        true,
    );
    assert!(
        facts.proves(&goal),
        "the old general fallback could close this query"
    );
    assert!(!c_pointer_offsets_proven_equal_for_effect(
        &left, &right, &facts
    ));
}

#[cfg(test)]
#[test]
fn effect_pointer_equality_stops_at_the_verification_deadline() {
    let offset = PointerOffsetTerm::Constant(0);
    crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        assert!(!c_pointer_offsets_proven_equal_for_effect(
            &offset,
            &offset,
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
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let pointer = Pointer {
        block: "cell".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
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
    condition: &ConditionTerm,
) -> Option<ConditionTerm> {
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        (
            Box::new(canonicalize_atomic_loads_deep(left)),
            Box::new(canonicalize_atomic_loads_deep(right)),
        )
    };
    Some(match condition {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left,
            right,
        } => {
            let (left, right) = binary(left, right);
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            }
        }
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left,
            right,
        } => {
            let (left, right) = binary(left, right);
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            }
        }
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        } => {
            let (left, right) = binary(left, right);
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left,
                right,
            }
        }
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        } => {
            let (left, right) = binary(left, right);
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            }
        }
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        } => {
            let (left, right) = binary(left, right);
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
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
/// overflow the stack. The fact's snapshot handles may differ from the
/// effect's endpoints by bookkeeping (materialized cells, recorded locals);
/// what the chain needs is agreement on the loaded cell, which the
/// directly-match check decides per pointer with havoc-marker parity.
#[inline(never)]
fn directly_matched_effect_endpoint(
    effect_side: &CMemory,
    side: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    memories_directly_match_for_pointer_load(effect_side, side, pointer, assumptions)
}

#[cfg(test)]
mod opaque_pointer_frame_tests {
    use super::*;

    #[test]
    fn complete_pointer_domains_follow_numeric_storage_equality_only() {
        let _session = crate::kernel::VerificationSession::enter();
        let [a, b, c, d] = [1, 2, 3, 4].map(|id| Pointer::symbolic(Variable(9_880_450 + id)));
        let memory = intern_c_memory(CMemory::new());
        let left = Pointer::loaded_value(&memory, &a);
        let right = Pointer::loaded_value(&memory, &d);
        let address_equality = |a: &Pointer, b: &Pointer| {
            ConditionTerm::uint64_equal(
                Bitvector32Term::pointer_address(a.clone()),
                Bitvector32Term::pointer_address(b.clone()),
            )
        };
        let numbers_only =
            PureFactContext::new().assume_condition(address_equality(&left, &right), true);
        assert!(!pointer_read_designations_equal(
            &left,
            &right,
            &numbers_only
        ));
        let mut same_storage = PureFactContext::new();
        for (a, b) in [(&a, &b), (&c, &d), (&b, &c)] {
            same_storage = same_storage.assume_condition(address_equality(a, b), true);
        }
        assert!(pointer_read_designations_equal(
            &left,
            &right,
            &same_storage
        ));
        assert!(pointer_read_extents_equal(&left, &right, &same_storage));
        let overwritten = intern_c_memory(
            memory
                .memory()
                .clone()
                .store(a.offset_by_bytes(4), CValue::UInt32(0u32.into())),
        );
        let changed = Pointer::loaded_value(&overwritten, &d);
        assert!(!pointer_read_designations_equal(
            &left,
            &changed,
            &same_storage
        ));
        assert!(!pointer_read_extents_equal(&left, &changed, &same_storage));
    }

    #[test]
    fn complete_pointer_read_addresses_follow_a_shared_unchanged_source() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer::symbolic(Variable(9_880_490));
        let base = intern_c_memory(CMemory::new());
        let left = intern_c_memory(base.memory().clone().store(
            field.offset_by_bytes(8),
            CValue::UInt64(Bitvector32Term::UInt64Constant(1)),
        ));
        let right = intern_c_memory(base.memory().clone().store(
            field.offset_by_bytes(16),
            CValue::UInt64(Bitvector32Term::UInt64Constant(2)),
        ));
        let a = Pointer::loaded_value(&left, &field);
        let b = Pointer::loaded_value(&right, &field);
        let context = PureFactContext::new();
        assert!(pointer_read_designations_equal(&a, &b, &context));
        assert!(pointer_read_extents_equal(&a, &b, &context));
        assert!(complete_pointer_reads_equal_across_frame(&a, &b, &context));
        let changed = intern_c_memory(
            base.memory()
                .clone()
                .store(field.offset_by_bytes(4), CValue::UInt32(0u32.into())),
        );
        assert!(!complete_pointer_reads_equal_across_frame(
            &a,
            &Pointer::loaded_value(&changed, &field),
            &context,
        ));
    }

    #[test]
    fn complete_pointer_read_addresses_use_exact_retained_typed_producers() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer::symbolic(Variable(9_880_491));
        let base = CMemory::new();
        let left = intern_c_memory(base.clone().store(
            field.offset_by_bytes(8),
            CValue::UInt64(Bitvector32Term::UInt64Constant(1)),
        ));
        let right = intern_c_memory(base.store(
            field.offset_by_bytes(16),
            CValue::UInt64(Bitvector32Term::UInt64Constant(2)),
        ));
        let cell_bits = |memory: &SharedCMemory| {
            Bitvector32Term::MemoryLoad(memory.clone(), Box::new(field.clone()), LoadKind::Int32)
        };
        let read = |memory: &SharedCMemory| Pointer::loaded(&cell_bits(memory)).unwrap();
        let a = read(&left);
        let b = read(&right);
        // A pointer read names its typed producer's exact definition.
        for value in [&a, &b] {
            let definition = value.as_loaded_value().expect("a typed pointer read");
            assert_eq!(definition.defining_address, field);
            assert_eq!(definition.displacement, PointerOffsetTerm::Constant(0));
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
        let changed = intern_c_memory(
            right
                .memory()
                .clone()
                .store(field.offset_by_bytes(4), CValue::UInt32(0u32.into())),
        );
        let c = read(&changed);
        assert!(c.as_loaded_value().is_some());
        assert!(!complete_pointer_reads_equal_across_frame(&a, &c, &context));
    }

    #[test]
    fn complete_pointer_domain_uses_explicit_whole_header_separation() {
        let _session = crate::kernel::VerificationSession::enter();
        let header = Pointer::symbolic(Variable(9_880_410));
        let field = header.clone().offset_by_bytes(8);
        let buffer = Pointer::symbolic(Variable(9_880_411));
        let before = intern_c_memory(CMemory::new());
        let after = intern_c_memory(before.memory().clone().store(
            buffer.clone().offset_by_bytes(4),
            CValue::Int32(7u32.into()),
        ));
        let read = |snapshot: &SharedCMemory| Pointer::loaded_value(snapshot, &field);
        let separation = |header_words: u32| Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(CMemoryRange::new(
                header.clone(),
                0u32.into(),
                header_words.into(),
            ))),
            right: Box::new(CResource::Memory(CMemoryRange::new(
                buffer.clone(),
                0u32.into(),
                8u32.into(),
            ))),
        };
        let empty = PureFactContext::new();
        let context = empty.clone().assume_proposition(separation(4));
        assert!(!pointer_read_designations_equal(
            &read(&before),
            &read(&after),
            &empty
        ));
        assert!(pointer_read_designations_equal(
            &read(&before),
            &read(&after),
            &context
        ));
        assert!(pointer_read_extents_equal(
            &read(&before),
            &read(&after),
            &context
        ));
        let too_short = empty.assume_proposition(separation(1));
        assert!(!pointer_read_designations_equal(
            &read(&before),
            &read(&after),
            &too_short
        ));
        let overwritten = intern_c_memory(
            after
                .memory()
                .clone()
                .store(field.clone().offset_by_bytes(4), CValue::Int32(0u32.into())),
        );
        assert!(!pointer_read_designations_equal(
            &read(&before),
            &read(&overwritten),
            &context
        ));
        assert!(!pointer_read_extents_equal(
            &read(&before),
            &read(&overwritten),
            &context
        ));
    }

    #[test]
    fn copied_pointer_value_uses_explicit_whole_header_separation() {
        let _session = crate::kernel::VerificationSession::enter();
        let header = Pointer::symbolic(Variable(9_880_420));
        let field = header.clone().offset_by_bytes(8);
        let buffer = Pointer::symbolic(Variable(9_880_421));
        let target = Pointer::symbolic(Variable(9_880_422));
        let stored = CPointerValue::new(target.clone(), CType::Int32Pointer).with_extent(Some(
            SubobjectExtent {
                start: target,
                width: 4u32.into(),
            },
        ));
        let memory = intern_c_memory(
            CMemory::new()
                .store(field.clone(), CValue::Pointer(stored.clone()))
                .store(
                    buffer.clone().offset_by_bytes(4),
                    CValue::Int32(7u32.into()),
                ),
        );
        let read = |memory: &SharedCMemory| {
            CPointerValue::from_read(
                stored.pointer().clone(),
                CType::Int32Pointer,
                memory,
                &field,
            )
        };
        let separation = |words: u32| Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(CMemoryRange::new(
                header.clone(),
                0u32.into(),
                words.into(),
            ))),
            right: Box::new(CResource::Memory(CMemoryRange::new(
                buffer.clone(),
                0u32.into(),
                8u32.into(),
            ))),
        };
        let empty = PureFactContext::new();
        assert!(!empty.pointer_designations_match(&read(&memory), &stored));
        let context = empty.clone().assume_proposition(separation(4));
        assert!(context.pointer_designations_match(&read(&memory), &stored));
        let too_short = empty.assume_proposition(separation(1));
        assert!(!too_short.pointer_designations_match(&read(&memory), &stored));
        let partial = intern_c_memory(
            memory
                .memory()
                .clone()
                .store(field.clone().offset_by_bytes(4), CValue::Int32(0u32.into())),
        );
        assert!(!context.pointer_designations_match(&read(&partial), &stored));
    }

    fn setup() -> (Pointer, Pointer, Pointer, Proposition, Proposition) {
        let field = Pointer {
            block: PointerBlock::Concrete("local:opaque-frame".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let write = Pointer::symbolic(Variable(9_880_001));
        let argument = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(128),
        };
        let alias = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(write.clone(), argument.clone()),
            true,
        );
        let separation = Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                field.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
                8,
            ))),
            right: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                argument.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
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
        let step = CMemoryDerivation::Store {
            base: intern_c_memory(CMemory::default()),
            pointer: write.clone(),
            value: CValue::Int32(Bitvector32Term::Constant(7)),
        };
        let proof = typed_store_separated_ranges_evidence(&write, 4, &field, 8, &assumptions)
            .expect("one exact alias must select the stated range separation");
        assert!(proof.checks(&step, &field, 8, &assumptions));
        for missing in [alias, separation] {
            assert!(!proof.checks(&step, &field, 8, &assumptions.without_exact_fact(&missing)));
        }
        let wrong_step = CMemoryDerivation::Store {
            base: intern_c_memory(CMemory::default()),
            pointer: field.clone(),
            value: CValue::Int32(Bitvector32Term::Constant(7)),
        };
        assert!(!proof.checks(&wrong_step, &field, 8, &assumptions));
    }

    #[test]
    fn bounded_pointer_read_preserves_value_across_forgotten_cache() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(128),
        };
        let possible_write = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(
                Bitvector32Term::Variable(Variable(9_880_201)),
                4,
            ),
        };
        let stored = Pointer::symbolic(Variable(9_880_202));
        let memory = CMemory::new().store(
            field.clone(),
            CValue::typed_pointer(stored.clone(), CType::Int32Pointer),
        );
        let memory =
            memory.without_possible_aliasing_cells(&possible_write, 4, &PureFactContext::new());
        let snapshot = intern_c_memory(memory);
        assert!(matches!(
            snapshot.derivation().as_deref(),
            Some(CMemoryDerivation::CellsForgotten { .. })
        ));
        let read = Pointer::loaded_value(&snapshot, &field);
        let context = PureFactContext::new();
        context
            .equality_graph
            .register_pointer_read_definition(&read, &snapshot, &field);
        assert!(pointer_read_has_recorded_value(&read, &stored, &context));
        let read_from = |memory| {
            let snapshot = intern_c_memory(memory);
            let read = Pointer::loaded_value(&snapshot, &field);
            context
                .equality_graph
                .register_pointer_read_definition(&read, &snapshot, &field);
            read
        };
        let replacement = Pointer::symbolic(Variable(9_880_203));
        let changed = read_from(snapshot.memory().clone().store(
            field.clone(),
            CValue::typed_pointer(replacement.clone(), CType::Int32Pointer),
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
                snapshot
                    .memory()
                    .clone()
                    .store(address, CValue::Int32(Bitvector32Term::Constant(7))),
            );
            assert!(!pointer_read_has_recorded_value(
                &changed, &stored, &context
            ));
        }
    }

    #[test]
    fn opaque_pointer_transport_requires_unchanged_field_bytes() {
        let (field, _, argument, _, separation) = setup();
        let before = intern_c_memory(CMemory::default().with_block("local:opaque-frame", 8));
        let read =
            Bitvector32Term::MemoryLoad(before.clone(), Box::new(field.clone()), LoadKind::Int32);
        let variable = crate::kernel::eval::load_variable_for_term(&read)
            .unwrap()
            .0;
        let pointer = Pointer::symbolic(variable);
        let source = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pointer.clone(), argument.clone()),
            true,
        );
        let assumptions = PureFactContext::new()
            .assume_proposition(source.clone())
            .assume_proposition(separation.clone());
        let after = before
            .memory()
            .clone()
            .store(pointer, CValue::Int32(Bitvector32Term::Constant(7)));
        let theorem = prove_c_condition_fact_transport(&source, &after, &assumptions)
            .expect("unchanged pointer identity transports across an aliased store");
        assert!(
            c_condition_fact_transport_target_in_context(&theorem, &source, &assumptions).is_some()
        );
        assert!(
            c_condition_fact_transport_target_in_context(
                &theorem,
                &source,
                &assumptions.without_exact_fact(&separation)
            )
            .is_none()
        );
        let changed = before
            .memory()
            .clone()
            .store(field, CValue::pointer(argument));
        assert!(prove_c_condition_fact_transport(&source, &changed, &assumptions).is_none());
    }

    #[test]
    fn wide_alias_reads_reconnect_each_endpoints_own_projection() {
        let _session = crate::kernel::VerificationSession::enter();
        let left_pointer = Pointer::symbolic(Variable(9_880_610));
        let right_pointer = Pointer::symbolic(Variable(9_880_611));
        let alias = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(left_pointer.clone(), right_pointer.clone()),
            true,
        );
        let context = PureFactContext::new().assume_proposition(alias.clone());
        let source = intern_c_memory(
            CMemory::new()
                .with_block_without_derivation("local:projection-left", 4)
                .with_block_without_derivation("local:projection-right", 4),
        );
        // These projections retain different irrelevant local declarations.
        // Neither changes the bytes observable through either symbolic pointer.
        let left_memory = intern_c_memory(
            CMemory::new().with_block_without_derivation("local:projection-left", 4),
        );
        let right_memory = intern_c_memory(
            CMemory::new().with_block_without_derivation("local:projection-right", 4),
        );
        record_canonical_load_projection(&source, &left_memory, &left_pointer);
        record_canonical_load_projection(&source, &right_memory, &right_pointer);
        let left = Bitvector32Term::MemoryLoad(
            left_memory,
            Box::new(left_pointer.clone()),
            LoadKind::Bits64,
        );
        let right = Bitvector32Term::MemoryLoad(
            right_memory.clone(),
            Box::new(right_pointer.clone()),
            LoadKind::Bits64,
        );
        assert!(wide_read_has_recorded_value(&left, &right, &context));
        assert!(wide_read_has_recorded_value(&right, &left, &context));
        assert!(!wide_read_has_recorded_value(
            &left,
            &right,
            &context.without_exact_fact(&alias),
        ));
        let narrow = Bitvector32Term::MemoryLoad(
            right_memory,
            Box::new(right_pointer.clone()),
            LoadKind::Int32,
        );
        assert!(!wide_read_has_recorded_value(&left, &narrow, &context));
        let overwritten_source = intern_c_memory(source.memory().clone().store(
            right_pointer.clone(),
            CValue::UInt64(Bitvector32Term::UInt64Constant(7)),
        ));
        let overwritten = Bitvector32Term::MemoryLoad(
            canonical_projected_load_memory(&overwritten_source, &right_pointer),
            Box::new(right_pointer),
            LoadKind::Bits64,
        );
        assert!(!wide_read_has_recorded_value(&left, &overwritten, &context));
    }

    #[test]
    fn wide_value_uses_retained_projection_source_and_rejects_overwrites() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(
                Bitvector32Term::Variable(Variable(9_880_401)),
                4,
            ),
        };
        let write = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(
                Bitvector32Term::Variable(Variable(9_880_402)),
                4,
            ),
        };
        let alias = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(write.clone(), address.clone()),
            true,
        );
        let context = PureFactContext::new().assume_proposition(alias.clone());
        let value = Bitvector32Term::UInt64Constant(42);
        let source = intern_c_memory(
            CMemory::new()
                .with_block("local:wide-unrelated", 4)
                .store(
                    Pointer {
                        block: PointerBlock::Concrete("local:wide-unrelated".into()),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    CValue::Int32(Bitvector32Term::Constant(1)),
                )
                .store(write.clone(), CValue::UInt64(value.clone())),
        );
        let projected = canonical_projected_load_memory(&source, &address);
        assert_ne!(projected, source);
        let direct = Bitvector32Term::MemoryLoad(
            source.clone(),
            Box::new(address.clone()),
            LoadKind::Bits64,
        );
        let read =
            Bitvector32Term::MemoryLoad(projected, Box::new(address.clone()), LoadKind::Bits64);
        assert!(wide_read_has_recorded_value(&direct, &value, &context));
        assert!(wide_read_has_recorded_value(&read, &value, &context));
        assert!(!wide_read_has_recorded_value(
            &read,
            &value,
            &context.without_exact_fact(&alias)
        ));
        let projected_read = |memory| {
            let source = intern_c_memory(memory);
            Bitvector32Term::MemoryLoad(
                canonical_projected_load_memory(&source, &address),
                Box::new(address.clone()),
                LoadKind::Bits64,
            )
        };
        let replacement = Bitvector32Term::UInt64Constant(7);
        let changed = projected_read(
            source
                .memory()
                .clone()
                .store(write.clone(), CValue::UInt64(replacement.clone())),
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
                    .store(at, CValue::Int32(Bitvector32Term::Constant(7))),
            );
            assert!(!wide_read_has_recorded_value(&changed, &value, &context));
        }
        let unknown = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(
                Bitvector32Term::Variable(Variable(9_880_403)),
                4,
            ),
        };
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
                .store(unknown, CValue::Int32(Bitvector32Term::Constant(7))),
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
        let field = Pointer::symbolic(Variable(9_880_490));
        let bits = Bitvector32Term::UInt64Constant(17);
        let number = CValue::UInt64(bits.clone());
        let word = number
            .clone()
            .complete_word(Pointer::symbolic(Variable(9_880_491)));
        let context = PureFactContext::new();
        let same_value = || {
            crate::kernel::reasoning::c_values_proven_equal_for_memory_resolution(
                &word, &number, &context,
            )
        };
        assert!(!same_value());
        let memory = intern_c_memory(CMemory::new().store(field.clone(), word.clone()));
        let read = Bitvector32Term::MemoryLoad(memory, Box::new(field), LoadKind::Bits64);
        assert!(wide_read_has_recorded_value(&read, &bits, &context));
        assert!(wide_read_has_recorded_value(&bits, &read, &context));
        assert!(!same_value());
    }

    #[test]
    fn recovered_wide_word_uses_current_equality_closure() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(128),
        };
        let parent = Pointer::symbolic(Variable(9_880_501));
        let alias = Pointer::symbolic(Variable(9_880_502));
        let equality = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(parent.clone(), alias.clone()),
            true,
        );
        let context = PureFactContext::new().assume_proposition(equality.clone());
        let stored = Bitvector32Term::PointerAddress(
            Box::new(parent),
            crate::kernel::AddressObjectClass::NONE,
        );
        let wanted = Bitvector32Term::PointerAddress(
            Box::new(alias),
            crate::kernel::AddressObjectClass::NONE,
        );
        assert_ne!(stored, wanted);
        assert!(context.uint64_values_known_equal(&stored, &wanted));
        let memory = intern_c_memory(CMemory::new().store(field.clone(), CValue::UInt64(stored)));
        let read = Bitvector32Term::MemoryLoad(memory, Box::new(field), LoadKind::Bits64);
        assert!(wide_read_has_recorded_value(&read, &wanted, &context));
        assert!(wide_read_has_recorded_value(&wanted, &read, &context));
        let (proved, diagnostics) = capture_read_resolutions(|| {
            wide_read_has_recorded_value(&read, &wanted, &context.without_exact_fact(&equality))
        });
        assert!(!proved);
        assert_eq!(diagnostics.len(), 1);
        let diagnostic = &diagnostics[0];
        assert_eq!(diagnostic.reason, "step affects the read's bytes");
        assert!(diagnostic.recovered.is_some());
        assert!(!diagnostic.equal);
        assert_eq!(diagnostic.expected, wanted);
        assert_eq!(diagnostic.stopped_at.as_ref(), Some(&diagnostic.producer));
        let mut labels = crate::surface::proof_diagnostics::render::SnapshotLabels::ambient();
        let rendered = crate::surface::proof_diagnostics::render::render_read_resolution(
            diagnostic,
            &mut labels,
        );
        assert!(rendered.contains("recovered word equality:"), "{rendered}");
        assert!(
            rendered.contains("equality check: not proved"),
            "{rendered}"
        );
        assert!(
            rendered.contains("producer source: snapshot#"),
            "{rendered}"
        );
        assert!(!rendered.contains("…"), "{rendered}");
        assert!(wide_read_has_recorded_value(&read, &wanted, &context));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/memory_provenance/opaque_pointer_frame_tests.rs");
    }
}

#[cfg(test)]
mod canonical_numeric_run_tests {
    use super::*;
    use crate::kernel::primitives::{CellRun, IndexIntervals, RunValueMode};

    #[test]
    fn deep_canonicalization_rewrites_noncanonical_numeric_run_addresses() {
        let _session = crate::kernel::VerificationSession::enter();
        let index_cell = Pointer {
            block: "canonical-index".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let source = intern_c_memory(CMemory::new().with_block("canonical-index", 4).store(
            index_cell.clone(),
            CValue::Int32(Bitvector32Term::Constant(8)),
        ));
        let base = Pointer {
            block: "canonical-run".into(),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::MemoryLoad(
                    source.clone(),
                    Box::new(index_cell),
                    LoadKind::Int32,
                )),
                byte_width: 1,
            },
        };
        let canonical_base = canonicalize_pointer_loads(&base);
        assert_ne!(canonical_base, base);
        let mut holes = IndexIntervals::default();
        holes.insert(3);
        let run = CellRun::new(base, 1, CType::UInt8, 8, source, holes);
        let mut memory = CMemory::new();
        std::sync::Arc::make_mut(&mut memory.cells).add_run(run.clone());
        let canonical = canonical_c_memory_deep(&memory);
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
        include!("../scaling_tests/kernel/memory_provenance/canonical_numeric_run_tests.rs");
    }
}

#[cfg(test)]
mod pointer_store_endpoint_tests {
    use super::*;

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/memory_provenance/pointer_store_endpoint_tests.rs");
    }
}

#[cfg(test)]
mod wide_range_reader_tests {
    use super::*;
    // Resource comparison may see two unequal native endpoints or mixed kinds.
    #[test]
    fn wide_resource_matching_refuses_signed_endpoint_comparison() {
        let base = Pointer::symbolic(Variable(984_200));
        let wide = CMemoryRange::new_wide(
            base.clone(),
            Bitvector32Term::UInt64Constant(0),
            Bitvector32Term::UInt64Constant(1 << 33),
            4,
        );
        let other = CMemoryRange::new_wide(
            base.clone(),
            Bitvector32Term::UInt64Constant(0),
            Bitvector32Term::UInt64Constant(2 << 33),
            4,
        );
        let narrow = CMemoryRange::new(base, 0u32.into(), 1u32.into());
        let facts = PureFactContext::new();
        assert!(c_resources_directly_match(
            &CResource::Memory(wide.clone()),
            &CResource::Memory(wide.clone()),
            &facts
        ));
        for right in [other, narrow] {
            assert!(!c_resources_directly_match(
                &CResource::Memory(wide.clone()),
                &CResource::Memory(right),
                &facts
            ));
        }
    }
}

#[cfg(test)]
mod borrow_partition_tests {
    use super::*;
    use crate::kernel::loans::{LoanLedger, LoanViewBinding};

    fn range(id: u64) -> CMemoryRange {
        CMemoryRange::new(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(id)),
            },
            0u32.into(),
            1u32.into(),
        )
    }

    fn resources() -> (ResourceContext, ResourceContext, CMemoryRange, CMemoryRange) {
        let write = range(901_001);
        let read = range(901_002);
        let view = CResourceFact::view_memory(read.clone());
        let bare = ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own_memory(write.clone()))
            .unchecked_with_fact(view.clone());
        let support = bare.occurrences_for_fact(&view)[0];
        let ledger = LoanLedger::new();
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
        let bound = bare.clone().with_loan_dependency(
            support,
            LoanViewBinding {
                loan: opening.loan,
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
        let proposition = Proposition::CResourceComposition(bound.clone());
        let context = PureFactContext::new().assume_proposition(proposition.clone());
        let witness =
            typed_store_separated_ranges_evidence(write.base(), 4, read.base(), 4, &context)
                .unwrap();
        let step = CMemoryDerivation::Store {
            base: intern_c_memory(CMemory::new()),
            pointer: write.base().clone(),
            value: CValue::Int32(1u32.into()),
        };
        assert!(witness.checks(&step, read.base(), 4, &context));
        let missing = PureFactContext::new()
            .assume_proposition(Proposition::CResourceComposition(bare.clone()));
        assert!(
            typed_store_separated_ranges_evidence(write.base(), 4, read.base(), 4, &missing)
                .is_none()
        );
        assert!(!witness.checks(&step, read.base(), 4, &missing));
        // Retain the candidate index but withdraw its authority.
        let mut withdrawn = context.clone();
        withdrawn.resource_compositions = withdrawn.resource_compositions.without_value(&bound);
        assert!(!witness.checks(&step, read.base(), 4, &withdrawn));
        assert!(
            typed_store_separated_ranges_evidence(write.base(), 4, read.base(), 4, &withdrawn)
                .is_none()
        );
        assert!(!witness.checks(&step, read.base(), 8, &context));
        let overlapping = context.assume_condition(
            ConditionTerm::pointer_equal(write.base().clone(), read.base().clone()),
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
        let occurrence = bound.occurrences_for_fact(&CResourceFact::view_memory(read.clone()))[0];
        let removed = bound
            .clone()
            .without_bound_view_occurrence(occurrence, bound.loan_dependency(occurrence).unwrap())
            .unwrap()
            .unchecked_with_fact(CResourceFact::view_memory(read.clone()));
        assert!(!removed.proves_borrow_partition_separate(&write, &read));
    }

    #[test]
    fn borrow_partition_binding_journal_tracks_branches_and_ignores_repeated_binding() {
        let (bare, bound, _, read) = resources();
        let occurrence = bound.occurrences_for_fact(&CResourceFact::view_memory(read))[0];
        let binding = bound.loan_dependency(occurrence).unwrap().clone();
        let initial =
            crate::kernel::loans::LoanViewBindings::from_state(bare.loan_dependency_state());
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
        include!("../scaling_tests/kernel/memory_provenance/borrow_partition_tests.rs");
    }
}

#[cfg(test)]
mod reversed_history_queries {
    use super::*;

    fn changed_history(size: usize) -> (SharedCMemory, SharedCMemory, Pointer) {
        let pointer = Pointer {
            block: format!("reversed-history-{size}").into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = CMemory::new()
            .with_block(format!("reversed-history-{size}"), (size as u32 + 2) * 4)
            .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(0)));
        let mut after = before
            .clone()
            .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(1)));
        for index in 1..=size {
            after = after.store(
                pointer.offset_by_bytes(index as u32 * 4),
                CValue::Int32(Bitvector32Term::Constant(index as u32)),
            );
        }
        (intern_c_memory(before), intern_c_memory(after), pointer)
    }

    #[test]
    fn reversed_refusal_keeps_its_context_and_read_width() {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer {
            block: "conditional-history".into(),
            offset: PointerOffsetTerm::scale_int32(
                Bitvector32Term::Variable(Variable(9_840_000)),
                4,
            ),
        };
        let read_index = Bitvector32Term::Variable(Variable(9_840_001));
        let write_index = Bitvector32Term::Variable(Variable(9_840_002));
        let pointer = base.offset_by_elements(read_index.clone(), 4);
        crate::kernel::eval::declare_load_access_width(&pointer, 4);
        let write = base.offset_by_elements(write_index.clone(), 4);
        let weak = PureFactContext::new();
        let strong = weak.clone().assume_condition(
            ConditionTerm::signed_less_than(read_index, write_index),
            true,
        );
        let before = CMemory::new().with_block("conditional-history", 64);
        let after = before.clone().store_with_context(
            write,
            CValue::Int32(Bitvector32Term::Constant(9)),
            &strong,
        );
        let before = intern_c_memory(before);
        let after = intern_c_memory(after);
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
        include!("../scaling_tests/kernel/memory_provenance/reversed_history_queries.rs");
    }
}

#[cfg(test)]
mod direct_unchanged_scaling_tests {
    use super::*;

    fn cell(block: &str) -> Pointer {
        Pointer {
            block: PointerBlock::from(block),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    fn value(index: usize) -> CValue {
        CValue::UInt32(Bitvector32Term::UInt32Constant(index as u32))
    }

    /// `c_memories_connected_by_effects` walks the effects filed under the
    /// memories it reaches. It once collected every write effect among the
    /// proposition facts and searched them with `Vec::contains`, so each
    /// loadability fallback paid for every call the path had made.
    #[test]
    fn effect_connection_ignores_unrelated_effect_facts() {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let start = CMemory::new().store(cell("target"), value(1));
            let middle = start.clone().with_block("call-havoc:0", 0);
            let end = middle.clone().with_block("call-havoc:1", 0);
            let summary = |before: &CMemory, after: &CMemory| Proposition::CMemoryEffectSummary {
                before: before.clone(),
                after: after.clone(),
                mutable_ranges: Vec::new(),
            };
            let facts = (0..size)
                .fold(PureFactContext::new(), |facts, index| {
                    let base =
                        CMemory::new().store(cell(&format!("unrelated-{index}")), value(index));
                    let next = base
                        .clone()
                        .store(cell(&format!("unrelated-{index}")), value(index + 1));
                    facts.assume_proposition(summary(&base, &next))
                })
                .assume_proposition(summary(&start, &middle))
                .assume_proposition(summary(&middle, &end));
            let (connected, work) = crate::instrumentation::measure_deterministic_work(|| {
                c_memories_connected_by_effects(&start, &end, &facts)
            });
            assert!(connected, "two recorded calls connect the snapshots");
            samples.push((size, work));
        }
        let (_, smallest) = samples[0];
        assert!(
            samples.iter().all(|(_, work)| *work == smallest),
            "the effect connection grew with unrelated effect facts: {samples:?}"
        );
    }

    /// The route carrying a loadable fact across recorded effects to a later
    /// snapshot reads the loadable facts filed under the base's block, not
    /// every proposition fact. Across the gate it never proved a fact
    /// another route had not, so this pins its miss: a stated fact at a
    /// snapshot no effect connects is the one candidate it reads.
    #[test]
    fn carried_loadability_ignores_unrelated_loadable_facts() {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let loadable = |memory: &CMemory, base: Pointer| Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base,
                bytes: Bitvector32Term::Constant(4),
                wide: false,
            };
            // The queried snapshot holds no target object, so no other
            // route carries the fact.
            let stated = CMemory::new().with_block("target", 4);
            let queried = CMemory::new();
            let facts = (0..size)
                .fold(PureFactContext::new(), |facts, index| {
                    facts.assume_proposition(loadable(&stated, cell(&format!("unrelated-{index}"))))
                })
                .assume_proposition(loadable(&stated, cell("target")));
            CARRIED_LOADABLE_VISITS.with(|visits| visits.set(0));
            let carried = facts.proves_atomic_without_search(&loadable(&queried, cell("target")));
            assert!(!carried, "no effect connects the two snapshots");
            samples.push((size, CARRIED_LOADABLE_VISITS.with(std::cell::Cell::get)));
        }
        let (_, smallest) = samples[0];
        assert!(smallest > 0, "the carried route read no fact: {samples:?}");
        assert!(
            samples.iter().all(|(_, visits)| *visits == smallest),
            "carried loadability read unrelated loadable facts (size, facts read): {samples:?}"
        );
    }

    /// `c_memory_load_is_directly_unchanged` reads the effect facts filed
    /// under its `before` memory. It once scanned every proposition fact, so
    /// each load check after a long run of calls paid for every earlier
    /// call's effect summary. Its work must not grow with unrelated effects.
    #[test]
    fn a_direct_unchanged_check_ignores_unrelated_effect_facts() {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let target = cell("target");
            // A call stands between the snapshots: the direct check cannot
            // match its havoc away, and only the call's effect summary, whose
            // one mutable range is in another object, shows the target cell
            // unchanged.
            let before = CMemory::new()
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
                let base = CMemory::new().store(cell(&format!("unrelated-{index}")), value(index));
                facts.assume_proposition(Proposition::CMemoryEffectSummary {
                    before: base.clone(),
                    after: base
                        .clone()
                        .store(cell(&format!("unrelated-{index}")), value(index + 1)),
                    mutable_ranges: Vec::new(),
                })
            });
            let facts = facts.assume_proposition(Proposition::CMemoryEffectSummary {
                before: before.clone(),
                after: after.clone(),
                mutable_ranges: vec![CMemoryRange::new(
                    written.clone(),
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Constant(1),
                )],
            });
            DIRECT_UNCHANGED_VISITS.with(|visits| visits.set(0));
            let (unchanged, work) = crate::instrumentation::measure_deterministic_work(|| {
                c_memory_load_is_directly_unchanged(
                    &before,
                    &after,
                    &target,
                    LoadKind::Int32,
                    &facts,
                )
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
