use super::*;
use crate::kernel::MachineCastSpelling;
use crate::kernel::{BooleanOperandView, CompareRelation};
use crate::kernel::{OffsetTree, OffsetView};
use crate::kernel::{bits32_constant, int64_constant, native_constant, uint64_constant};

fn retained_cell_conversion(source: &ExecutionValue, value: ProgramValue) -> ExecutionValue {
    if source.shared().is_some_and(|root| {
        root.ty() == &KernelType::Bool
            || matches!(root.ty(), KernelType::Algebraic(_))
            || FloatOperandView::from_shared(root).is_some()
    }) && value.program_type() == source.program_type()
    {
        // Same-type cell conversion leaves Boolean, algebraic and float values unchanged.
        source.clone()
    } else if source.shared().is_some() {
        source.retain_checked_pointer(value)
    } else {
        value.into()
    }
}

#[derive(Default)]
struct MemoryLoadAliasCache {
    resolution_equal: BTreeMap<(u64, Address), bool>,
    resolution_distinct: BTreeMap<(u64, Address), bool>,
    equal: BTreeMap<(u64, Address), bool>,
}

impl MemoryLoadAliasCache {
    fn resolution_equal(
        &mut self,
        pointer: &Address,
        stored_pointer: &Address,
        assumptions: &PureFactContext,
    ) -> bool {
        *self
            .resolution_equal
            .entry((assumptions.memo_fingerprint(), stored_pointer.clone()))
            .or_insert_with(|| {
                pointers_proven_equal_for_memory_resolution(pointer, stored_pointer, assumptions)
            })
    }

    fn resolution_distinct(
        &mut self,
        pointer: &Address,
        stored_pointer: &Address,
        assumptions: &PureFactContext,
    ) -> bool {
        *self
            .resolution_distinct
            .entry((assumptions.memo_fingerprint(), stored_pointer.clone()))
            .or_insert_with(|| {
                pointers_proven_distinct_for_memory_resolution(pointer, stored_pointer, assumptions)
            })
    }

    fn equal(
        &mut self,
        pointer: &Address,
        stored_pointer: &Address,
        assumptions: &PureFactContext,
    ) -> bool {
        *self
            .equal
            .entry((assumptions.memo_fingerprint(), stored_pointer.clone()))
            .or_insert_with(|| {
                pointers_proven_equal_by_reasoning(pointer, stored_pointer, assumptions)
            })
    }
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(in crate::kernel) fn evaluate_memory_load_paths(
    memory: &SymbolicMemory,
    pointer: Address,
    value_type: ProgramType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    has_external_read_resource: bool,
    volatile: bool,
    source: Option<&LoadSourceId>,
    byte_order: Option<ByteOrder>,
) -> Vec<ExpressionPath> {
    evaluate_retained_memory_load_paths(
        &ProgramPoint::of_memory(memory),
        pointer,
        value_type,
        facts,
        obligations,
        assumptions,
        has_external_read_resource,
        volatile,
        source,
        byte_order,
        false,
    )
    .into_iter()
    .map(ExecutionValuePath::into_native)
    .collect()
}

#[allow(clippy::too_many_arguments)]
pub(in crate::kernel) fn evaluate_retained_memory_load_paths(
    point: &ProgramPoint,
    pointer: Address,
    value_type: ProgramType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    has_external_read_resource: bool,
    volatile: bool,
    source: Option<&LoadSourceId>,
    byte_order: Option<ByteOrder>,
    uses_recorded_point: bool,
) -> Vec<ExecutionValuePath> {
    let memory = point.memory();
    let origin = uses_recorded_point.then_some(point);
    let _assumptions_id_scope = assumptions.enter_id_scope();
    if has_pending_reallocation_for_pointer(memory, &pointer) {
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::RuntimeError(RuntimeError::UnresolvedAllocationOutcome),
            facts,
            obligations,
        }];
    }
    let mut alias_cache = MemoryLoadAliasCache::default();
    // Function reads have an exact load-variable identity, including when
    // reading a borrowed callback table in an ordinary statement proof.
    let observed = (!volatile
        && (assumptions.should_require_owned_expression_loads()
            || matches!(value_type, ProgramType::FunctionPointer(_))))
    .then(|| (crate::kernel::intern_memory_ref(memory), pointer.clone()));
    let word_storage = (!volatile
        && matches!(value_type, ProgramType::Int64 | ProgramType::UInt64))
    .then(|| pointer.clone());
    let mut paths = evaluate_retained_memory_load_paths_with_alias_cache(
        memory,
        pointer,
        value_type,
        facts,
        obligations,
        assumptions,
        has_external_read_resource,
        if volatile {
            LoadPurpose::VolatileProgram
        } else {
            LoadPurpose::Program
        },
        &mut alias_cache,
        source,
        byte_order,
        origin,
        Some(point),
    );
    if let Some(address) = word_storage {
        for path in &mut paths {
            if let ExpressionOutcome::Value(value) = &mut path.outcome {
                *value = retained_cell_conversion(
                    value,
                    complete_loaded_word(
                        value.native().into_owned(),
                        memory,
                        Some(point),
                        &address,
                    ),
                );
            }
        }
    }
    if let Some(observed) = observed {
        for path in &mut paths {
            let ExpressionOutcome::Value(value) = &path.outcome else {
                continue;
            };
            let Some(value) = value.pointer() else {
                continue;
            };
            // A checked, nonvolatile C read supplies its complete current-cell
            // equation. Ordinary observations do not publish this evidence.
            // The read is named by its version point, as the source place
            // lowers, so the equation states what a written read of it means.
            let read = Address::canonical_read(&observed.0, Some(point), &observed.1);
            path.facts.push(
                if matches!(value.program_type(), ProgramType::FunctionPointer(_)) {
                    ExecutionPureFact::checked_pointer_read_equation(value.clone(), read)
                } else {
                    ExecutionPureFact::logical_read_equation(value.clone(), read)
                },
            );
            let mut read_facts = ExecutionFacts::new();
            if let Some(variable) = typed_pointer_read_variable(value.address())
                && let Some(load) =
                    crate::kernel::equality_graph::logical_pointer_read_term(value.address())
            {
                // Build the selected evidence in a fresh stream, without
                // searching or rewriting unrelated incoming path facts.
                record_load_variable_defining_fact_with_source_and_pointer(
                    variable,
                    load,
                    &mut read_facts,
                    source,
                    Some(value.address()),
                );
            }
            for mut fact in read_facts {
                if let Some(GeneratedLoadBinding::Exact {
                    observed_pointer_read,
                    ..
                }) = fact.generated_load_binding.as_deref_mut()
                {
                    *observed_pointer_read = Some(observed.clone());
                }
                path.facts.push(fact);
            }
        }
    }
    paths
}

/// The paths of one *specification* load: a read written in a contract, an
/// invariant, or a proof step, rather than a read the C program performs.
///
/// A specification load denotes the value one named state holds at one
/// pointer. It is not a step of the program, so it has no branch to take: an
/// alias it cannot resolve leaves the load term unresolved rather than
/// splitting into the cases a C execution would have to choose between. The
/// one-term spec load rule already governs the non-symbolic spec path in
/// `crate::kernel::spec`; this is the same rule on the symbolic one.
pub(in crate::kernel) fn evaluate_spec_memory_load_paths(
    memory: &SymbolicMemory,
    pointer: Address,
    value_type: ProgramType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<ExpressionPath> {
    let _assumptions_id_scope = assumptions.enter_id_scope();
    if has_pending_reallocation_for_pointer(memory, &pointer) {
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::RuntimeError(RuntimeError::UnresolvedAllocationOutcome),
            facts,
            obligations,
        }];
    }
    let mut alias_cache = MemoryLoadAliasCache::default();
    evaluate_memory_load_paths_with_alias_cache(
        memory,
        pointer,
        value_type,
        facts,
        obligations,
        assumptions,
        false,
        LoadPurpose::Validity,
        &mut alias_cache,
        None,
        // A specification load denotes a state's cell, not a C access;
        // it has no byte view of a wider cell.
        None,
    )
}

/// Construct the value of a logical read using the shared typed load model.
/// No C access occurs and no validity evidence is introduced.
#[cfg(test)]
pub(in crate::kernel) fn evaluate_logical_memory_load_paths(
    memory: &SymbolicMemory,
    pointer: Address,
    value_type: ProgramType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<ExpressionPath> {
    evaluate_logical_memory_load_paths_in_view(
        memory,
        pointer,
        value_type,
        facts,
        obligations,
        assumptions,
        None,
    )
}

/// Read a cell from the view at the supplied program point.
pub(in crate::kernel) fn evaluate_logical_memory_load_paths_at(
    point: &ProgramPoint,
    pointer: Address,
    value_type: ProgramType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<ExpressionPath> {
    // Indexed ordinary versions are selected before this compatibility
    // route. Symbolic Boolean and float reads can name the observation
    // point directly, and an integer read takes the version the point
    // indexes select (`ProgramPoint::read_version`). Other residual reads
    // still use legacy selection.
    let origin = (value_type == ProgramType::Bool
        || KernelFloatType::from_program_type(value_type).is_some()
        || MachineIntegerType::from_program_type(value_type).is_some())
    .then_some(point);
    evaluate_logical_memory_load_paths_in_view(
        point.memory(),
        pointer,
        value_type,
        facts,
        obligations,
        assumptions,
        origin,
    )
}

fn evaluate_logical_memory_load_paths_in_view(
    memory: &SymbolicMemory,
    pointer: Address,
    value_type: ProgramType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    origin: Option<&ProgramPoint>,
) -> Vec<ExpressionPath> {
    let mut paths = evaluate_logical_memory_load_paths_unbridged(
        memory,
        pointer.clone(),
        value_type,
        facts,
        obligations,
        assumptions,
        origin,
    );
    retain_indexed_scalar_cell_value(memory, &pointer, value_type, assumptions, &mut paths);
    #[cfg(test)]
    if let [path] = paths.as_slice()
        && let ExpressionOutcome::Value(value) = &path.outcome
    {
        super::typed_reads::record(memory, &pointer, value);
    }
    paths
}

/// A typed read whose version was selected from the execution path.
pub(in crate::kernel) fn evaluate_indexed_read(
    version: ProgramPoint,
    origin: &ProgramPoint,
    pointer: Address,
    value_type: ProgramType,
    mut facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
) -> ExpressionPath {
    if let ProgramType::Parameter(parameter) = value_type {
        let value = AlgebraicTermNode::parameter_load_at(version.clone(), pointer, parameter);
        if let Some(stored) = version.indexed_stored_value() {
            let (ProgramValue::Parameter(read), ProgramValue::Parameter(stored)) =
                (&value, stored.native())
            else {
                unreachable!("indexed opaque store");
            };
            facts.push(ExecutionPureFact {
                logical_read_equation: true,
                ..ExecutionPureFact::certified(Proposition::condition_is(
                    OldConditionTerm::AlgebraicEqual(read.clone(), stored.clone()),
                    true,
                ))
            });
        }
        return ExpressionPath {
            outcome: ExpressionOutcome::Value(value),
            facts,
            obligations,
        };
    }
    if value_type.is_pointer() {
        let stored = version.indexed_stored_value().map(|store| {
            let ProgramValue::Pointer(stored) = store.native().numeric_value() else {
                unreachable!("indexed pointer store");
            };
            // A store at another pointee type of the same category answers
            // this load; the stored value is the read's value at its type.
            stored.clone().with_type(value_type)
        });
        record_load_access_width(version.memory(), &pointer, value_type.byte_width());
        let read = Pointer::from_point_read(version, value_type, &pointer);
        if let Some(stored) = stored {
            facts.push(ExecutionPureFact::logical_pointer_value_equation(
                stored,
                read.clone(),
            ));
        }
        let value = ProgramValue::Pointer(read);
        return ExpressionPath {
            outcome: ExpressionOutcome::Value(value),
            facts,
            obligations,
        };
    }
    if value_type == ProgramType::Bool {
        let ProgramValue::Bool(stored) = version
            .indexed_stored_value()
            .expect("indexed Boolean store")
            .native()
            .numeric_value()
        else {
            unreachable!("indexed Boolean store");
        };
        let stored = OldConditionTerm::truth_of_bool_word(stored);
        let read = OldConditionTerm::boolean_cell_read(version, pointer.clone());
        facts.push(ExecutionPureFact {
            logical_read_equation: true,
            ..ExecutionPureFact::certified(Proposition::condition_is(
                OldConditionTerm::bool_equal(read.clone(), stored),
                true,
            ))
        });
        return ExpressionPath {
            outcome: ExpressionOutcome::Value(ProgramValue::of_bool(read)),
            facts,
            obligations,
        };
    }
    let stored = version.indexed_integer_store_bits().cloned();
    let entry_word =
        stored.is_none() && matches!(value_type, ProgramType::Int64 | ProgramType::UInt64);
    let kind = LoadKind::of_type(value_type).expect("indexed integer read");
    let format = MachineIntegerType::from_program_type(value_type).expect("indexed integer read");
    read_observations::record_at(&version, &pointer, kind, origin, value_type.byte_width());
    let read = crate::kernel::OldMachineTerm::read_named(version, pointer.clone(), kind);
    let value = match value_type {
        ProgramType::Int8 => ProgramValue::Int8(read.clone()),
        ProgramType::UInt8 => ProgramValue::UInt8(read.clone()),
        ProgramType::Int16 => ProgramValue::Int16(read.clone()),
        ProgramType::UInt16 => ProgramValue::UInt16(read.clone()),
        ProgramType::Int32 => ProgramValue::Int32(read.clone()),
        ProgramType::UInt32 => ProgramValue::UInt32(read.clone()),
        ProgramType::Int64 => ProgramValue::Int64(read.clone()),
        ProgramType::UInt64 => ProgramValue::UInt64(read.clone()),
        ProgramType::Int128 => ProgramValue::Int128(read.clone()),
        ProgramType::UInt128 => ProgramValue::UInt128(read.clone()),
        _ => unreachable!("indexed integer read"),
    };
    // Retain the read and publish its exact store equation separately.
    if let Some(stored) = stored {
        let equation = match value_type {
            ProgramType::Int128 => wide_integer_comparison_condition(
                ComparisonOperator::Equal,
                &value,
                &ProgramValue::Int128(stored),
            )
            .expect("typed signed 128-bit store"),
            ProgramType::UInt128 => wide_integer_comparison_condition(
                ComparisonOperator::Equal,
                &value,
                &ProgramValue::UInt128(stored),
            )
            .expect("typed unsigned 128-bit store"),
            _ => OldConditionTerm::machine_compare(format, CompareRelation::Equal, read, stored),
        };
        facts.push(ExecutionPureFact {
            logical_read_equation: true,
            ..ExecutionPureFact::certified(Proposition::condition_is(equation, true))
        });
    }
    // The selected entry supplies the numeric bits. A complete load still
    // carries the pointer representation of the observed cell.
    let value = if entry_word {
        complete_loaded_word(value, origin.memory(), Some(origin), &pointer)
    } else {
        value
    };
    ExpressionPath {
        outcome: ExpressionOutcome::Value(value),
        facts,
        obligations,
    }
}

/// The value of Surface `exact(place)` (`design/exact-reads.md`): the read
/// of the `value_type` cell at `pointer` named by `memory` itself. Unlike
/// [`evaluate_logical_memory_load_paths`], it runs no version walk and
/// returns no value the cell holds, and it consults no facts, so the term
/// depends only on the memory and the address (fact-stable). A pointer
/// read's address, provenance and bounds owner are the same exact read
/// ([`Pointer::from_read`]). It adds no facts and grants no access.
pub(in crate::kernel) fn evaluate_exact_logical_memory_load_paths(
    point: ProgramPoint,
    pointer: Address,
    value_type: ProgramType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
) -> Vec<ExpressionPath> {
    let outcome = match exact_logical_read_value(point, &pointer, value_type) {
        Some(value) => ExpressionOutcome::Value(value),
        None => ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch {
            pointer,
            value_type,
            stored: None,
        }),
    };
    vec![ExpressionPath {
        outcome,
        facts,
        obligations,
    }]
}

/// [`evaluate_exact_logical_memory_load_paths`]'s value: the exact read
/// constructor evaluation uses for an explicitly selected scalar cell.
fn exact_logical_read_value(
    point: ProgramPoint,
    pointer: &Address,
    value_type: ProgramType,
) -> Option<ProgramValue> {
    if let Some(format) = KernelFloatType::from_program_type(value_type) {
        return Some(format.value(float_read_term(point, pointer, format)));
    }
    if !logical_read_names_its_version(value_type) {
        return None;
    }
    if value_type.is_pointer() {
        record_load_access_width(point.memory(), pointer, value_type.byte_width());
        return Some(ProgramValue::Pointer(Pointer::from_point_read(
            point.for_exact_read(),
            value_type,
            pointer,
        )));
    }
    let point = point.for_exact_read();
    record_load_access_width(point.memory(), pointer, value_type.byte_width());
    let value = if value_type == ProgramType::Bool {
        ProgramValue::of_bool(OldConditionTerm::boolean_cell_read(
            point.clone(),
            pointer.clone(),
        ))
    } else {
        let kind = LoadKind::of_type(value_type)?;
        read_observations::record_at(&point, pointer, kind, &point, value_type.byte_width());
        let bits = crate::kernel::OldMachineTerm::read_named(point.clone(), pointer.clone(), kind);
        ProgramValue::from_bitvector_term(value_type, bits)?
    };
    Some(complete_loaded_word(
        value,
        point.memory(),
        Some(&point),
        pointer,
    ))
}

fn float_read_term(
    point: ProgramPoint,
    pointer: &Address,
    format: KernelFloatType,
) -> OldMachineTerm {
    crate::kernel::OldMachineTerm::read_named(
        point.for_exact_read(),
        pointer.clone(),
        format.load_kind(),
    )
}

fn point_named_float_load(
    source: &ProgramPoint,
    pointer: &Address,
    value_type: ProgramType,
) -> Option<OldMachineTerm> {
    let format = KernelFloatType::from_program_type(value_type)?;
    source
        .has_certified_read_view()
        .then(|| float_read_term(source.clone(), pointer, format))
}

/// Give a new symbolic float read the point where the read was taken.
/// Alias-resolution views may discard cached cells while answering a load.
fn point_named_symbolic_float_read(
    origin: Option<&ProgramPoint>,
    pointer: &Address,
    value_type: ProgramType,
) -> Option<ProgramValue> {
    let origin = origin?;
    let read = point_named_float_load(origin, pointer, value_type)?;
    record_load_access_width(origin.memory(), pointer, value_type.byte_width());
    ProgramValue::from_bitvector_term(value_type, read)
}

fn point_named_symbolic_read(
    origin: Option<&ProgramPoint>,
    pointer: &Address,
    value_type: ProgramType,
) -> Option<ProgramValue> {
    let point = origin?;
    if value_type == ProgramType::Bool && point.has_certified_read_view() {
        return exact_logical_read_value(point.clone(), pointer, value_type);
    }
    if MachineIntegerType::from_program_type(value_type).is_some()
        && let Some(version) = point.read_version(pointer, value_type)
    {
        let kind = LoadKind::of_type(value_type)?;
        return Some(crate::kernel::cell_run_value(
            value_type,
            crate::kernel::OldMachineTerm::read_named(version, pointer.clone(), kind),
        ));
    }
    point_named_symbolic_float_read(Some(point), pointer, value_type)
}

fn evaluate_logical_memory_load_paths_unbridged(
    memory: &SymbolicMemory,
    pointer: Address,
    value_type: ProgramType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    origin: Option<&ProgramPoint>,
) -> Vec<ExpressionPath> {
    let symbolic_value = |facts: &mut ExecutionFacts| {
        point_named_symbolic_read(origin, &pointer, value_type).or_else(|| {
            canonicalized_symbolic_load_value_with_identity(
                memory,
                origin,
                &pointer,
                value_type,
                facts,
                assumptions,
                None,
                LoadPurpose::Logical,
            )
        })
    };
    // The read keeps the address it was written with: lowering is
    // fact-stable (`docs/internals/raise-lower-principle.md`). A value stored under
    // another spelling of an equal address reaches the read through the
    // equality graph, which equates them.
    // Version-named reads already stay symbolic. Sending them through C
    // evaluation for a pure-function proposition would resolve aliases from
    // facts and substitute the selected cell's value.
    if (assumptions.should_keep_spec_loads_symbolic()
        && !logical_read_names_its_version(value_type))
        || assumptions.should_force_symbolic_external_loads()
    {
        let _assumptions_id_scope = assumptions.enter_id_scope();
        // Logical reads denote state cells. Forward a forced-symbolic
        // request to the typed producer without performing a C read.
        let paths = evaluate_retained_memory_load_paths_with_alias_cache(
            memory,
            pointer.clone(),
            value_type,
            facts,
            obligations,
            assumptions,
            assumptions.should_force_symbolic_external_loads(),
            LoadPurpose::Logical,
            &mut MemoryLoadAliasCache::default(),
            None,
            None,
            origin,
            origin,
        );
        let mut paths: Vec<_> = paths
            .into_iter()
            .map(ExecutionValuePath::into_native)
            .collect();
        for path in &mut paths {
            // An invalid typed read still denotes a logical value. The C
            // evaluator's refusal is retained only by checked evaluation.
            if matches!(path.outcome, ExpressionOutcome::RuntimeError(_))
                && let Some(value) = symbolic_value(&mut path.facts)
            {
                path.outcome = ExpressionOutcome::Value(value);
            }
            if let ExpressionOutcome::Value(value) = &mut path.outcome {
                *value = complete_loaded_word(value.clone(), memory, origin, &pointer);
            }
            path.facts
                .retain(|fact| !is_load_variable_defining_fact(fact.proposition()));
        }
        return paths;
    }
    let mut facts = facts;
    // A read of an integer cell is the read at its version, whatever the
    // cell holds: the read-over-write authority (`read_over_write_value`)
    // relates it to the stored value. A cell seeded with its own read holds
    // that read's name, which is the read.
    let named = logical_read_names_its_version(value_type);
    let value = memory
        .known_union_value(&pointer, value_type)
        .filter(|value| !named && value_type.accepts(value))
        .or_else(|| {
            memory
                .known_value(&pointer)
                .filter(|stored| !named || holds_its_own_read(stored, &pointer))
                // A value that does not name its version is the stored one,
                // reached through an address based on a pointer read as
                // through the pointer memory shows stored there.
                .or_else(|| {
                    (!named)
                        .then(|| stored_pointer_address(&pointer))
                        .flatten()
                        .and_then(|address| memory.known_value(&address))
                })
                .and_then(|stored| {
                    let complete_pointer = matches!(&stored, ProgramValue::Pointer(_))
                        || matches!(&stored, ProgramValue::Int32(OldMachineTerm::Variable(variable))
                        if registered_load_kind_for_variable(variable) == Some(LoadKind::Int32)
                            && registered_load_bytes_for_variable(variable)
                                == Some(crate::kernel::C_POINTER_BYTE_WIDTH));
                    canonicalized_pointer_value_from_int_cell(
                        memory,
                        &pointer,
                        &stored,
                        value_type,
                        &mut facts,
                        assumptions,
                        None,
                        LoadPurpose::Logical,
                        origin,
                    )
                    .or_else(|| value_type.read_cell(&stored))
                    .inspect(|value| {
                        if let ProgramValue::Pointer(value) = value {
                            record_pointer_read_observation(value.address(), memory, &pointer);
                            let current = Address::canonical_read(
                                &crate::kernel::intern_memory_ref(memory),
                                origin,
                                &pointer,
                            );
                            if complete_pointer {
                                // The cached value was selected under this path's
                                // premises. Carry its current-cell equation with
                                // the result, rather than treating a global read
                                // observation as evidence in another context.
                                facts.push(ExecutionPureFact::logical_read_equation(
                                    value.clone(),
                                    current,
                                ));
                            }
                        }
                    })
                })
        })
        .or_else(|| symbolic_value(&mut facts));
    facts.retain(|fact| !is_load_variable_defining_fact(fact.proposition()));
    value
        .into_iter()
        .map(|value| ExpressionPath {
            outcome: ExpressionOutcome::Value(complete_loaded_word(
                value, memory, origin, &pointer,
            )),
            facts: facts.clone(),
            obligations: obligations.clone(),
        })
        .collect()
}

/// Whether a read of static storage at `pointer` need not split on the cell
/// at `stored_pointer`: a seeded read of that cell's own address (a pointer
/// parameter's pointee at entry, say) holds the value its bytes have had
/// since that read, so where the two addresses meet the read of `pointer`
/// returns it anyway. Static storage holds no entry contents of its own
/// (function entry declares it empty); before, its own seeded cell answered
/// the read and no such alias was asked.
fn entry_observation_of_other_storage(
    pointer: &Address,
    stored_pointer: &Address,
    stored_value: &ProgramValue,
) -> bool {
    pointer.base.is_static_storage_block()
        && stored_pointer.base != pointer.base
        && holds_its_own_read(stored_value, stored_pointer)
}

/// Whether a cell was seeded with a read of its own address. The retained
/// descriptor supplies its version; a legacy pointer carrier may still name it.
fn holds_its_own_read(stored: &ProgramValue, pointer: &Address) -> bool {
    crate::kernel::spec::program_value_bitvector_term(stored)
        .and_then(|term| viewed_as_memory_load(&term))
        .is_some_and(
            |term| matches!(term, OldMachineTerm::MemoryLoad(_, address, _) if *address == *pointer),
        )
}

fn retained_cell_holds_its_own_read(value: &ExecutionValue, pointer: &Address) -> bool {
    use crate::kernel::execution_value::storage_keys::AddressKey;
    let native_read = |word| {
        matches!(
            viewed_as_memory_load(word),
            Some(OldMachineTerm::MemoryLoad(_, cell, _)) if *cell == *pointer
        )
    };
    let Some(root) = value.shared() else {
        return holds_its_own_read(value.native_payload().expect("native cell"), pointer);
    };
    match root.node() {
        KernelTermNode::MemoryLoad { address, .. } => {
            AddressKey::native(pointer) == AddressKey::shared(address)
        }
        KernelTermNode::FloatRead(read) => {
            AddressKey::native(pointer) == AddressKey::shared(read.parts().1)
        }
        KernelTermNode::Variable(variable) if value.program_type() != ProgramType::Bool => {
            native_read(&OldMachineTerm::Variable(*variable))
        }
        KernelTermNode::ImportedScalar(input) => native_read(input.value()),
        _ => root.retained_machine_input().is_some_and(native_read),
    }
}

/// Whether a `bytes`-wide read at `pointer` overlaps a stored slice's cell
/// that starts elsewhere: a cell at an 8-aligned constant offset in the
/// read's own block (a slice's ABI alignment) whose 16 bytes meet the read's.
/// The read's own address is the exact lookup's. At most three exact lookups
/// by address, whatever the memory holds. A read at a symbolic offset, or
/// beside a misaligned slice cell, is a symbolic read of its own bytes, which
/// states nothing about the slice's words.
fn reads_inside_slice_cell(memory: &SymbolicMemory, pointer: &Address, bytes: u32) -> bool {
    let OffsetView::Constant(offset) = pointer.offset.view() else {
        return false;
    };
    let reach = i64::from(crate::kernel::WIDE_POINTER_BYTE_WIDTH);
    let alignment = i64::from(crate::kernel::C_POINTER_BYTE_WIDTH);
    let (Some(lowest), Some(end)) = (
        offset.checked_sub(reach - 1),
        offset.checked_add(i64::from(bytes.max(1))),
    ) else {
        return false;
    };
    // Constant work, independent of the memory, charges nothing: a load
    // that finds no slice cell is charged what it was before.
    let first = lowest.div_euclid(alignment) * alignment;
    let first = if first < lowest {
        first + alignment
    } else {
        first
    };
    (first..end)
        .step_by(alignment as usize)
        .filter(|start| *start != offset)
        .any(|start| {
            // A run holds scalar slots only, so the concrete cells suffice.
            matches!(
                memory
                    .cells
                    .concrete()
                    .get(&pointer.with_offset(AddressOffset::constant(start)))
                    .map(StoredMemoryValue::native),
                Some(ProgramValue::Pointer(stored)) if stored.is_wide()
            )
        })
}

/// Whether a logical read of a `value_type` cell lowers to the read at the
/// cell's version rather than to a value the cell holds
/// (`docs/internals/raise-lower-principle.md`). Integer, pointer and slice cells keep their
/// read identities; abstract values still read their stored value. A slice
/// cell's read is the slice its load decodes to ([`symbolic_slice_read`]).
fn logical_read_names_its_version(value_type: ProgramType) -> bool {
    matches!(
        value_type,
        ProgramType::Bool
            | ProgramType::Int8
            | ProgramType::UInt8
            | ProgramType::Int16
            | ProgramType::UInt16
            | ProgramType::Int32
            | ProgramType::UInt32
            | ProgramType::Int64
            | ProgramType::UInt64
    ) || value_type.is_pointer()
        || value_type.is_slice_pointer()
}

/// A selected footprint supplies an equal address, not a replacement read
/// term or access permission. Retain its stored word as a path-local equation.
fn retain_indexed_scalar_cell_value(
    memory: &SymbolicMemory,
    pointer: &Address,
    value_type: ProgramType,
    assumptions: &PureFactContext,
    paths: &mut [ExpressionPath],
) {
    if !matches!(value_type, ProgramType::Int32 | ProgramType::UInt32) {
        return;
    }
    let [path] = paths else { return };
    let ExpressionOutcome::Value(value) = &path.outcome else {
        return;
    };
    let Some(read) = crate::kernel::spec::program_value_bitvector_term(value) else {
        return;
    };
    let address = logical_memory_load_address(memory, pointer.clone(), value_type, assumptions);
    if address == *pointer {
        return;
    }
    let Some(stored) = memory
        .known_value(&address)
        .and_then(|value| value_type.read_cell(&value))
        .and_then(|value| crate::kernel::spec::program_value_bitvector_term(&value))
    else {
        return;
    };
    if read != stored {
        path.facts.push(ExecutionPureFact {
            logical_read_equation: true,
            ..ExecutionPureFact::certified(Proposition::condition_is(
                OldConditionTerm::equal(read, stored),
                true,
            ))
        });
    }
}

/// Use a published footprint only to select coordinates for this logical
/// address. Equality of the address grants no access or state transport.
fn logical_memory_load_address(
    memory: &SymbolicMemory,
    pointer: Address,
    value_type: ProgramType,
    assumptions: &PureFactContext,
) -> Address {
    // Only opaque model pointers and external pointers with an admitted
    // cross-block alias can need another spelling. Wide scalar loads need
    // the cached coordinate because their equalities do not use int32 load
    // congruence. Keep ordinary and loaded-pointer reads on their fast path.
    let model_pointer = match &pointer.base {
        AddressBase::Symbolic(variable) if !crate::kernel::is_load_variable(variable) => true,
        AddressBase::ExternalArgument
            if matches!(value_type, ProgramType::Int64 | ProgramType::UInt64)
                && assumptions.equality_graph.pointer_is_classed(&pointer.base) =>
        {
            false
        }
        _ => return pointer,
    };
    // Preserve an existing exact cell before choosing coordinates through
    // a proved alias. An unfold may have named this cell at a model pointer
    // before its body introduced the equality to the C parameter.
    if memory.known_value(&pointer).is_some() {
        return pointer;
    }
    let coordinate = assumptions
        .composition_object_resources
        .memory_address_spelling(&pointer, assumptions);
    // An uncached footprint only supplies coordinates for a model pointer.
    // External pointers keep their own spelling unless a cell was found.
    if model_pointer {
        coordinate.unwrap_or(pointer)
    } else {
        coordinate
            .filter(|spelling| memory.known_value(spelling).is_some())
            .unwrap_or(pointer)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum LoadPurpose {
    Program,
    VolatileProgram,
    Logical,
    Validity,
}

fn has_pending_reallocation_for_pointer(memory: &SymbolicMemory, pointer: &Address) -> bool {
    memory
        .heap
        .pending_reallocations
        .values()
        .any(|pending| pending.old_pointer.base == pointer.base)
}

/// The shared load evaluator behind both entry points above.
///
/// `branches_on_unresolved_aliases` decides what an alias this load cannot
/// decide does: split the load into the two cases a C execution would have to
/// choose between, or leave the load term unresolved.
///
/// A C read is a step of the program. It observes one of those cases, and the
/// execution carries that case's condition with it, so it must branch. A
/// specification read is not a step: it denotes the value the named state
/// holds, and the load term over that state already *is* that value.
/// Leaving the term unresolved is therefore sound wherever splitting was —
/// each case's value equals the load term under that case's condition, so the
/// term is what the cases agree on, and it asserts strictly less than either of
/// them. It is also the only correct answer under a binder: a fold body is
/// evaluated once for every item of its range at once, and "this item aliases
/// the cell the program just wrote" is not a fact about any particular item.
///
/// Each undecided cell splits off its aliasing case and leaves the distinct
/// case, the same load over the memory without that cell, to the next turn
/// of this loop. The cases are the ones a recursion per cell produced, in
/// the same order, on one stack frame.
#[allow(clippy::too_many_arguments)]
fn evaluate_memory_load_paths_with_alias_cache(
    memory: &SymbolicMemory,
    pointer: Address,
    value_type: ProgramType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    has_external_read_resource: bool,
    purpose: LoadPurpose,
    alias_cache: &mut MemoryLoadAliasCache,
    source: Option<&LoadSourceId>,
    byte_order: Option<ByteOrder>,
) -> Vec<ExpressionPath> {
    evaluate_retained_memory_load_paths_with_alias_cache(
        memory,
        pointer,
        value_type,
        facts,
        obligations,
        assumptions,
        has_external_read_resource,
        purpose,
        alias_cache,
        source,
        byte_order,
        None,
        None,
    )
    .into_iter()
    .map(ExecutionValuePath::into_native)
    .collect()
}

#[allow(clippy::too_many_arguments)]
fn evaluate_retained_memory_load_paths_with_alias_cache(
    memory: &SymbolicMemory,
    pointer: Address,
    value_type: ProgramType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    has_external_read_resource: bool,
    purpose: LoadPurpose,
    alias_cache: &mut MemoryLoadAliasCache,
    source: Option<&LoadSourceId>,
    byte_order: Option<ByteOrder>,
    origin: Option<&ProgramPoint>,
    site: Option<&ProgramPoint>,
) -> Vec<ExecutionValuePath> {
    let mut distinct_case = None;
    let mut paths = evaluate_retained_memory_load_case(
        memory,
        memory,
        pointer.clone(),
        value_type,
        facts,
        obligations,
        assumptions,
        has_external_read_resource,
        purpose,
        alias_cache,
        source,
        byte_order,
        origin,
        site,
        true,
        &mut distinct_case,
    );
    // The fact set a transported case reads under, kept in place while its
    // id scope is entered: the scope registers its address.
    let mut case_assumptions: Option<PureFactContext> = None;
    // A distinct case's memory is hypothetical: it drops the undecided cell
    // (and its initialization mark) only to name the load's value over the
    // state without it. Whether the bytes the load reads were written is a
    // question about the memory the program holds, which still holds the
    // cell, so every case asks it of the memory the load was read at.
    let original_memory = memory;
    while let Some(case) = distinct_case.take() {
        let DistinctLoadCase {
            memory,
            facts,
            obligations,
            assumptions: prepared,
        } = case;
        if prepared.is_some() {
            case_assumptions = prepared;
        }
        let _case_assumptions_id_scope = case_assumptions
            .as_ref()
            .map(PureFactContext::enter_id_scope);
        // A memory of many undecided cells yields a case per cell, and each
        // carries every earlier case's distinctness facts. Past the budget the
        // remaining case stops splitting: its load term over the memory it
        // reached is the value every further case agrees on, so it stands for
        // them soundly while the pending limit fails the step.
        let splits = !crate::kernel::assumptions::reasoning_interrupted();
        paths.extend(evaluate_retained_memory_load_case(
            &memory,
            original_memory,
            pointer.clone(),
            value_type,
            facts,
            obligations,
            case_assumptions.as_ref().unwrap_or(assumptions),
            has_external_read_resource,
            purpose,
            alias_cache,
            source,
            byte_order,
            origin,
            site,
            splits,
            &mut distinct_case,
        ));
    }
    paths
}

/// The case of a load an undecided cell leaves once its aliasing case is
/// split off: the load over `memory`, which no longer holds that cell, under
/// the case's facts, and under `assumptions` when a transport built a fact
/// set of its own for the load (otherwise the one the load was read under).
struct DistinctLoadCase {
    memory: SymbolicMemory,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: Option<PureFactContext>,
}

/// One turn of [`evaluate_memory_load_paths_with_alias_cache`]: the paths
/// this memory decides, with the distinct case of an undecided cell left in
/// `distinct_case` for the caller. `written` is the memory the load was read
/// at, which every uninitialized-read check asks: `memory` may be a distinct
/// case's, without cells the program wrote. Scalar program reads also use
/// `written` for their symbolic result: reducing a cache must not change the
/// program point named by an unresolved read.
#[allow(clippy::too_many_arguments)]
fn evaluate_retained_memory_load_case(
    memory: &SymbolicMemory,
    written: &SymbolicMemory,
    pointer: Address,
    value_type: ProgramType,
    facts: ExecutionFacts,
    mut obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    has_external_read_resource: bool,
    purpose: LoadPurpose,
    alias_cache: &mut MemoryLoadAliasCache,
    source: Option<&LoadSourceId>,
    byte_order: Option<ByteOrder>,
    origin: Option<&ProgramPoint>,
    site: Option<&ProgramPoint>,
    splits: bool,
    distinct_case: &mut Option<DistinctLoadCase>,
) -> Vec<ExecutionValuePath> {
    let branches_on_unresolved_aliases =
        splits && matches!(purpose, LoadPurpose::Program | LoadPurpose::VolatileProgram);
    // The memory the load is read at stands at the read's site, and a
    // distinct case's memory, which only drops the undecided cell, is a view
    // of that state. A specification load has no site: it is a query whose
    // obligations are only looked up.
    let read_point = site.or(origin).map_or_else(
        crate::kernel::program_point::PathLink::lookup_key,
        |point| point.path_link().clone(),
    );
    let symbolic_value =
        |memory: &SymbolicMemory, facts: &mut ExecutionFacts, assumptions: &PureFactContext| {
            point_named_symbolic_read(origin, &pointer, value_type)
                .map(ExecutionValue::from)
                .or_else(|| {
                    canonicalized_retained_symbolic_load_value_with_identity(
                        memory,
                        site,
                        &pointer,
                        value_type,
                        facts,
                        assumptions,
                        source,
                        purpose,
                    )
                })
        };
    let mut facts = facts;
    if purpose != LoadPurpose::Logical && memory.is_ended_local_address(&pointer) {
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
            facts,
            obligations,
        }];
    }
    // Transport is the exception, not the rule: most loads add no condition
    // fact and must keep reasoning against the *caller's* fact set object.
    // The memo identity of a fact set is the ambient scope its address was
    // registered under (`PureFactContextIdScope`), so cloning it
    // unconditionally handed every query below a fact set no scope names, and
    // the whole load — including the cell scans — then ran memo-cold. Build a
    // new context only when a transport actually lands, and register that one
    // in its own scope.
    let mut load_assumptions: Option<PureFactContext> = None;
    let candidates = if assumptions.should_transport_memory_load_condition_facts() {
        {
            assumptions
                .exact_memory_load_condition_candidates(&pointer)
                .map(|(condition, value)| Proposition::condition_is(condition.clone(), value))
                .collect::<Vec<_>>()
        }
    } else {
        Default::default()
    };
    for source in candidates {
        let Some(theorem) = prove_program_condition_fact_transport(
            &source,
            &ProgramPoint::read_at_optional(&crate::kernel::intern_memory_ref(memory), site),
            assumptions,
        ) else {
            continue;
        };
        let Some(target) =
            program_condition_fact_transport_target_in_context(&theorem, &source, assumptions)
        else {
            continue;
        };
        if target == &source {
            continue;
        }
        let target = target.clone();
        let base = load_assumptions
            .take()
            .unwrap_or_else(|| assumptions.clone());
        load_assumptions = Some(base.assume_proposition(target.clone()));
        let transported = ExecutionPureFact::certified_transport(source, target, theorem);
        if !facts.contains(&transported) {
            facts.push(transported);
        }
    }
    let _load_assumptions_id_scope = load_assumptions
        .as_ref()
        .map(PureFactContext::enter_id_scope);
    // Borrowing the transported context here also freezes it, which is what
    // keeps the scope's registered address describing this exact fact set.
    let assumptions = load_assumptions.as_ref().unwrap_or(assumptions);
    // Construction storage remains unwritten under other possible pointer
    // spellings. Authority alone cannot enable the external-memory shortcut;
    // let ordinary alias resolution find actual writes first.
    let allow_symbolic_external_load = has_external_read_resource
        && (!memory.may_read_uninitialized_object(&pointer, value_type.byte_width())
            || purpose == LoadPurpose::Logical
            || written.has_initialized_bytes_under(&pointer, value_type.byte_width(), assumptions)
            || assumptions.has_memory_read_defined_evidence(
                written,
                &read_point,
                &pointer,
                value_type,
            ));
    // An ordinary external scalar fallback names the written state even
    // when the alias-resolution case is examining a projection of it.
    let reads_written_state = allow_symbolic_external_load
        && pointer.has_symbolic_block()
        && purpose == LoadPurpose::Program
        && value_type.pointee_type().is_none();
    // A typed union overlay is the authoritative view for an exact typed
    // load, including in history-sensitive symbolic-load mode. Selecting
    // the raw load first would reinterpret a copied pointer member as an
    // integer and discard its provenance.
    if let Some(value) = memory.known_retained_union_value(&pointer, value_type) {
        if value_type.accepts(&value.native()) {
            return vec![ExpressionPath {
                outcome: ExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch {
                pointer: pointer.clone(),
                value_type,
                stored: None,
            }),
            facts,
            obligations,
        }];
    }

    // History-sensitive lowering asks for the load identity even when this
    // state has already materialized the cell's concrete value. Checking
    // `known_value` first would collapse `at(mark, field == 11)` to `true` and
    // erase the address needed for later frame transport.
    // An abstract value has no frame history to transport: a stored one is
    // the value, found by the lookups below.
    if allow_symbolic_external_load
        && assumptions.should_force_symbolic_external_loads()
        && !matches!(value_type, ProgramType::Parameter(_))
    {
        let Some(value) = symbolic_value(
            if purpose == LoadPurpose::Program && value_type.pointee_type().is_none() {
                written
            } else {
                memory
            },
            &mut facts,
            assumptions,
        ) else {
            return vec![ExpressionPath {
                outcome: ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                }),
                facts,
                obligations,
            }];
        };
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    // A pointer-typed load of a materialized int32 cell that is not a bare
    // load term (for example a call-havoc variable standing for the framed
    // field) cannot be reinterpreted as a stable pointer form. When the
    // caller permits symbolic external loads, fall through to the symbolic
    // load below — its load-term form relates across states — instead
    // of failing the load.
    let pointer_cell_defers_to_symbolic = |value: &ProgramValue| {
        (matches!(value, ProgramValue::Int32(_))
            || (matches!(value_type, ProgramType::FunctionPointer(_))
                && matches!(
                    value,
                    ProgramValue::Int8(_)
                        | ProgramValue::Int16(_)
                        | ProgramValue::UInt8(_)
                        | ProgramValue::UInt16(_)
                        | ProgramValue::UInt32(_)
                        | ProgramValue::Int64(_)
                        | ProgramValue::UInt64(_)
                )))
            && value_type.is_pointer()
            && has_external_read_resource
            && (assumptions.should_prefer_symbolic_external_loads()
                || matches!(value_type, ProgramType::FunctionPointer(_)))
    };
    // A one-byte C load inside a wider integer cell, including at the cell's
    // own address, reads that cell's little-endian representation. It is
    // decided here, before the exact lookup (whose wider cell would not fit
    // the load) and the whole-memory scan below, by a bounded lookup in the
    // load's own block; a load with no byte view falls through unchanged.
    if value_type.byte_width() == 1
        && let Some(cell) = containing_integer_cell(memory, &pointer, byte_order)
    {
        let outcome = match byte_view_load_value(&cell, value_type) {
            Some(value) => ExpressionOutcome::Value(value.into()),
            None => ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch {
                pointer: pointer.clone(),
                value_type,
                stored: None,
            }),
        };
        return vec![ExpressionPath {
            outcome,
            facts,
            obligations,
        }];
    }
    // An exact materialized cell is already the authoritative value for this
    // non-union pointer. Avoid proving every other symbolic cell distinct
    // before the direct map lookup.
    let names_version =
        purpose == LoadPurpose::Logical && logical_read_names_its_version(value_type);
    // A value that does not name its version is the stored one, reached
    // through an address based on a pointer read as through the pointer
    // memory shows stored there.
    let known = memory.known_retained_value(&pointer).or_else(|| {
        (!names_version)
            .then(|| stored_pointer_address(&pointer))
            .flatten()
            .and_then(|address| memory.known_retained_value(&address))
    });
    // A read of part of a stored slice's cell takes one of its words, which
    // the kernel has no layout for: it refuses, as a thin read of the whole
    // cell does (`design/rust-slice-values.md`, step 2b-ii-a).
    if known.is_none() && reads_inside_slice_cell(memory, &pointer, value_type.byte_width()) {
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch {
                pointer: pointer.clone(),
                value_type,
                stored: None,
            }),
            facts,
            obligations,
        }];
    }
    if let Some(value) =
        known.filter(|value| !names_version || retained_cell_holds_its_own_read(value, &pointer))
    {
        if value.shared().is_some()
            && value.program_type() == value_type
            && matches!(
                value_type,
                ProgramType::Bool
                    | ProgramType::Int32
                    | ProgramType::UInt32
                    | ProgramType::Int64
                    | ProgramType::UInt64
                    | ProgramType::Float32
                    | ProgramType::Float64
            )
        {
            // These same-type reads need no conversion or narrow range facts.
            return vec![ExpressionPath {
                outcome: ExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        let native = value.native();
        if let Some(value) = canonicalized_pointer_value_from_int_cell(
            memory,
            &pointer,
            &native,
            value_type,
            &mut facts,
            assumptions,
            source,
            purpose,
            site,
        ) {
            return vec![ExpressionPath {
                outcome: ExpressionOutcome::Value(value.into()),
                facts,
                obligations,
            }];
        }
        if let Some(converted) = value_type.read_cell(&native) {
            return vec![ExpressionPath {
                outcome: ExpressionOutcome::Value(retained_cell_conversion(&value, converted)),
                facts,
                obligations,
            }];
        }
        if let ProgramType::Parameter(parameter) = value_type
            && let Some(source) = abstract_value_source(memory, &pointer)
        {
            return vec![ExpressionPath {
                outcome: ExpressionOutcome::Value(
                    (AlgebraicTermNode::parameter_cell_load(&source, pointer, parameter)).into(),
                ),
                facts,
                obligations,
            }];
        }
        if !pointer_cell_defers_to_symbolic(&native) {
            return vec![ExpressionPath {
                outcome: ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                }),
                facts,
                obligations,
            }];
        }
    } else if let Some(value) = crate::instrumentation::measure_operation(
        "kernel",
        "memory load",
        "memory load: equal-cell scan",
        || {
            // A cell in a block proven distinct from the load's is never
            // resolution-equal to it, so only the candidates can match, and
            // they are visited in the whole map's order.
            let candidates = AliasCandidates::of_block(&pointer.base);
            let normalized = std::cell::OnceCell::new();
            let point = (reads_written_state
                && !crate::kernel::assumptions::implicit_consulted_premises_capturing()
                && !crate::kernel::assumptions::reasoning_interrupted())
            .then(|| {
                let normalized = normalized.get_or_init(|| {
                    crate::kernel::reasoning::memory_resolution::pointer_with_exact_index_constants(
                        &pointer,
                        assumptions,
                    )
                });
                (&pointer, normalized, assumptions)
            });
            let (found, visited) = memory.cells.find_retained_candidate_by(
                &candidates,
                point,
                |stored_pointer, _| {
                    let equal = alias_cache.resolution_equal(&pointer, stored_pointer, assumptions);
                    // A bounded equality query can retain an alias guard before its
                    // nested separation search reaches a compact resource composition.
                    // Recheck separation at the top-level query before treating that
                    // materialized cell as authoritative. If both hold, the alias guard
                    // describes an unreachable branch and must not manufacture a typed
                    // load from the disjoint cell.
                    equal && !alias_cache.resolution_distinct(&pointer, stored_pointer, assumptions)
                },
                |run| {
                    crate::kernel::reasoning::memory_resolution::run_slots_equal_to_load(
                        run,
                        &pointer,
                        &normalized,
                        assumptions,
                    )
                },
            );
            crate::instrumentation::record_deterministic_work(visited);
            found
        },
    ) {
        if let Some(value) = canonicalized_pointer_value_from_int_cell(
            memory,
            &pointer,
            &value.native(),
            value_type,
            &mut facts,
            assumptions,
            source,
            purpose,
            site,
        ) {
            return vec![ExpressionPath {
                outcome: ExpressionOutcome::Value(value.into()),
                facts,
                obligations,
            }];
        }
        if let Some(converted) = value_type.read_cell(&value.native()) {
            return vec![ExpressionPath {
                outcome: ExpressionOutcome::Value(retained_cell_conversion(&value, converted)),
                facts,
                obligations,
            }];
        }
        if !pointer_cell_defers_to_symbolic(&value.native()) {
            return vec![ExpressionPath {
                outcome: ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                }),
                facts,
                obligations,
            }];
        }
    }

    // Unlike external argument memory, a fresh heap block has a known
    // initialization history. Permission authorizes a read but cannot turn a
    // never-written heap cell into an unconstrained initialized value.
    if purpose != LoadPurpose::Logical
        && memory.is_uninitialized_heap_address(&pointer, value_type.byte_width(), assumptions)
        && !written.has_initialized_bytes_under(&pointer, value_type.byte_width(), assumptions)
        && !assumptions.has_memory_read_defined_evidence(written, &read_point, &pointer, value_type)
    {
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead),
            facts,
            obligations,
        }];
    }

    if purpose != LoadPurpose::Logical && memory.is_deallocated_heap_address(&pointer, assumptions)
    {
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
            facts,
            obligations,
        }];
    }

    let prefers_symbolic = assumptions.should_prefer_symbolic_external_loads();
    if allow_symbolic_external_load && (prefers_symbolic || reads_written_state) {
        if let Some(origin) = origin
            && let Some(version) = origin.entry_cell_version(&pointer, value_type)
        {
            return vec![
                evaluate_indexed_read(version, origin, pointer, value_type, facts, obligations)
                    .map_value(Into::into),
            ];
        }
        if !prefers_symbolic {
            // Preserve the width at the actual access spelling, as the
            // reduction path did before naming the value at the written state.
            record_load_access_width(memory, &pointer, value_type.byte_width());
        }
        let Some(value) = symbolic_value(
            if purpose == LoadPurpose::Program && value_type.pointee_type().is_none() {
                written
            } else {
                memory
            },
            &mut facts,
            assumptions,
        ) else {
            return vec![ExpressionPath {
                outcome: ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                }),
                facts,
                obligations,
            }];
        };
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    let mut memory = memory.clone();
    // The access width belongs to the state the load is read at, not only
    // to the projection of it that the term ends up carrying. Recording it
    // here as well as inside `symbolic_load_value` is what lets a later
    // caller holding the unreduced state ask how many bytes this load
    // reads instead of assuming the widest scalar.
    record_load_access_width(&memory, &pointer, value_type.byte_width());
    let reduction_base = Some(crate::kernel::primitives::intern_derivation_base(
        &mut memory,
    ));
    let cells_before_reduction = memory.cells.len();
    let load_bytes = value_type.byte_width();
    crate::instrumentation::measure_operation(
        "kernel",
        "memory load",
        "memory load: distinct-cell reduction",
        || {
            // Every cell in a block proven distinct from the load's is dropped
            // by this rule (its address is distinct on the first rung and its
            // bytes are `Separate`), so the reduced map is exactly the
            // candidates the rule keeps, built without visiting the rest.
            let candidates = AliasCandidates::of_block(&pointer.base);
            let mut reduced = (*memory.cells).clone();
            let normalized = std::cell::OnceCell::new();
            let visited = reduced.retain_only_candidates_by(
                &candidates,
                |stored_pointer, stored_value| {
                    // Dropping a cell names this load at a state that no longer
                    // records it, so the question is the same byte question
                    // `1a3b2701` put in front of the three state comparisons:
                    // `p + 1` is a different address from `p` under every test the
                    // kernel has while holding the second byte a four-byte read
                    // there returns. The address ladder decides it only where the
                    // bytes it establishes clear both accesses.
                    !(alias_cache.resolution_distinct(&pointer, stored_pointer, assumptions)
                        && access_byte_overlap(
                            stored_pointer,
                            crate::kernel::assumptions::access_extent_of_value(stored_value),
                            &pointer,
                            crate::kernel::AccessExtent::of_type(value_type),
                            assumptions,
                        ) == AccessByteOverlap::Separate)
                },
                |run| {
                    crate::kernel::reasoning::memory_resolution::run_slots_kept_by_load_reduction(
                        run,
                        &pointer,
                        &normalized,
                        load_bytes,
                        assumptions,
                    )
                },
            );
            crate::instrumentation::record_deterministic_work(visited);
            if reduced.len() != cells_before_reduction {
                memory.cells = std::sync::Arc::new(reduced);
            }
        },
    );
    // The returned symbolic load carries the reduced memory state, so
    // other queries must relate it back to its source. Dropping cells
    // provably distinct from the loaded pointer is a no-op for this load,
    // which is exactly the `CellsForgotten` edge; without it the derivation
    // walk dead-ends at this variant.
    //
    // The reduction choice may depend on `assumptions`, and the reduced map
    // may therefore re-intern as a state older than `reduction_base`.
    // That spelling is sound but deliberately gains no fact-free derivation
    // edge: `record_memory_derivation` refuses the backwards edge below.
    // The load judgment remains scoped to this exact assumption context.
    // Ordinary execution retains those facts on its path; an exhaustive
    // structural join can retain the value only when both checked arms reach
    // the same state; and an interface join re-lowers every exported fact in
    // both concrete arms and again at the fact-free successor. Thus an older
    // name is not authority to reuse the reduction in a sibling context.
    // `MemoryLoadAliasCache`'s assumption fingerprint is load-bearing for the
    // same reason. The regression below exercises one cache first under a
    // distinct fact (and observes the ancestor name), then under an aliasing
    // fact (and observes the later stored value).
    if let Some(base) = reduction_base
        && memory.cells.len() != cells_before_reduction
    {
        record_memory_derivation(&mut memory, MemoryDerivation::CellsForgotten { base });
    }

    if pointer.has_symbolic_block() && allow_symbolic_external_load {
        if let Some(origin) = origin
            && let Some(version) = origin.entry_cell_version(&pointer, value_type)
        {
            return vec![
                evaluate_indexed_read(version, origin, pointer, value_type, facts, obligations)
                    .map_value(Into::into),
            ];
        }
        let Some(value) = symbolic_value(&memory, &mut facts, assumptions) else {
            return vec![ExpressionPath {
                outcome: ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                }),
                facts,
                obligations,
            }];
        };
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    // A symbolic index into a run of seeded cells reads the run's slot at
    // that index, whichever slot it is. When the facts place every value of
    // the index on live slots, the value is the run's own load at the
    // index: each slot holds the load of its address in the run's source,
    // and the pointer is one of those addresses. Asking slot by slot instead
    // split the load once per element, recursively, which overflowed the
    // stack for a file-scope array of a thousand elements.
    if let Some(value) = symbolic_index_run_load(
        &memory,
        &pointer,
        value_type,
        &mut facts,
        assumptions,
        source,
        purpose,
    ) {
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::Value(value.into()),
            facts,
            obligations,
        }];
    }
    // A run the load indexes symbolically is never split slot by slot. Its
    // slots are one family of cells the facts did not place the index on; a
    // case per slot would only enumerate the array, and the load term over
    // this state is already the value every such case agrees on.
    let symbolically_indexed_runs = memory
        .cells
        .candidate_runs(&AliasCandidates::of_block(&pointer.base))
        .filter(|run| {
            matches!(
                crate::kernel::reasoning::memory_resolution::run_access(run, &pointer),
                crate::kernel::reasoning::memory_resolution::RunAccess::Scaled { .. }
            )
        })
        .cloned()
        .collect::<Vec<_>>();
    let in_symbolically_indexed_run = |stored_pointer: &Address| {
        symbolically_indexed_runs
            .iter()
            .any(|run| run.live_slot_index(stored_pointer).is_some())
    };
    // A load that does not split has nothing to learn from an undecided
    // alias, so it does not pay for the scan that looks for one either.
    let unresolved = branches_on_unresolved_aliases
        .then(|| {
            crate::instrumentation::measure_operation(
                "kernel",
                "memory load",
                "memory load: unresolved-cell scan",
                || {
                    // The reduction above left only candidate cells (see
                    // `AliasCandidates`), so this scan is already local.
                    crate::instrumentation::record_deterministic_work(memory.cells.len());
                    memory
                        .cells
                        .retained_iter()
                        .find_map(|(stored_pointer, stored_value)| {
                            (stored_pointer != &pointer
                                && !in_symbolically_indexed_run(stored_pointer)
                                && !entry_observation_of_other_storage(
                                    &pointer,
                                    stored_pointer,
                                    &stored_value.native(),
                                )
                                && !alias_cache.resolution_distinct(
                                    &pointer,
                                    stored_pointer,
                                    assumptions,
                                )
                                && !alias_cache.resolution_equal(
                                    &pointer,
                                    stored_pointer,
                                    assumptions,
                                ))
                            .then(|| (stored_pointer.clone(), stored_value.clone()))
                        })
                },
            )
        })
        .flatten();
    if let Some((stored_pointer, stored_value)) = unresolved {
        let mut paths = Vec::new();
        // General equality can resolve an indexed address that the narrower
        // memory resolver leaves open. A proven alias supplies this cell's
        // value; merely skipping its alias branch would lose an initialized
        // cell and eventually report an uninitialized read.
        let known_equal = !assumptions.should_defer_non_exact_condition_reasoning()
            && alias_cache.equal(&pointer, &stored_pointer, assumptions);

        let mut equal_facts = facts.clone();
        if known_equal
            || add_address_offset_equality_execution_pure_facts(
                &mut equal_facts,
                assumptions,
                pointer.offset.clone(),
                stored_pointer.offset.clone(),
                true,
            )
            .is_some()
        {
            let equal_outcome = if let Some(value) = canonicalized_pointer_value_from_int_cell(
                &memory,
                &pointer,
                &stored_value.native(),
                value_type,
                &mut facts,
                assumptions,
                source,
                purpose,
                site,
            ) {
                ExpressionOutcome::Value(value.into())
            } else if let Some(value) = value_type.read_cell(&stored_value.native()) {
                ExpressionOutcome::Value(retained_cell_conversion(&stored_value, value))
            } else {
                ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                })
            };
            paths.push(ExpressionPath {
                outcome: equal_outcome,
                facts: equal_facts,
                obligations: obligations.clone(),
            });
        }
        if known_equal {
            return paths;
        }

        let mut distinct_facts = facts;
        if add_address_offset_equality_execution_pure_facts(
            &mut distinct_facts,
            assumptions,
            pointer.offset.clone(),
            stored_pointer.offset.clone(),
            false,
        )
        .is_some()
        {
            // Two different addresses clear each other's bytes only when the
            // gap the inequality establishes is wide enough for both
            // accesses: two `int32` slots of one array, not a byte cell at
            // `p + 5` against the `int32` at `p + 4k`, which overlap at
            // `k == 1` although the addresses differ. Dropping the cell
            // would let a zeroed allocation answer that load as zero.
            let bytes_clear = access_byte_overlap(
                &stored_pointer,
                crate::kernel::assumptions::access_extent_of_value(&stored_value.native()),
                &pointer,
                crate::kernel::AccessExtent::of_type(value_type),
                assumptions,
            ) == AccessByteOverlap::Separate;
            if bytes_clear {
                // The distinct case is this same load over the memory without
                // that cell. The caller's loop evaluates it next, so a memory
                // with many undecided cells costs one frame, not one per cell.
                *distinct_case = Some(DistinctLoadCase {
                    memory: memory.without_cell(&stored_pointer),
                    facts: distinct_facts,
                    obligations,
                    // The next case is checked under this branch's new
                    // disequality. Extend the current context by that one
                    // condition; do not replay all earlier case facts.
                    assumptions: Some(assumptions.clone().assume_condition(
                        OldConditionTerm::address_offset_equal(
                            pointer.offset.clone(),
                            stored_pointer.offset.clone(),
                        ),
                        false,
                    )),
                });
            } else {
                // The cell may still hold some of the loaded bytes, so the
                // load's value is its load over this state, which keeps
                // the cell, and no further case is split from it.
                let outcome = match symbolic_value(
                    if purpose == LoadPurpose::Program && value_type.pointee_type().is_none() {
                        written
                    } else {
                        &memory
                    },
                    &mut distinct_facts,
                    assumptions,
                ) {
                    Some(value) => ExpressionOutcome::Value(value),
                    None => ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch {
                        pointer: pointer.clone(),
                        value_type,
                        stored: None,
                    }),
                };
                paths.push(ExpressionPath {
                    outcome,
                    facts: distinct_facts,
                    obligations,
                });
            }
        }

        return paths;
    }

    if memory.is_zeroed_heap_address(&pointer, value_type.byte_width(), assumptions) {
        let value = match value_type {
            ProgramType::Int8 => int8(OldMachineTerm::constant(0)),
            ProgramType::Int16 => int16(OldMachineTerm::constant(0)),
            ProgramType::Int32 => int32(OldMachineTerm::constant(0)),
            ProgramType::UInt8 => uint8(OldMachineTerm::constant(0)),
            ProgramType::UInt16 => uint16(OldMachineTerm::constant(0)),
            ProgramType::UInt32 => ProgramValue::UInt32(OldMachineTerm::uint32_constant(0)),
            ProgramType::Int64 => ProgramValue::Int64(OldMachineTerm::int64_constant(0)),
            ProgramType::UInt64 => ProgramValue::UInt64(OldMachineTerm::uint64_constant(0)),
            ProgramType::Int128 => match crate::kernel::program_expression::int128_literal(0) {
                ProgramExpression::Value(value) => value,
                _ => unreachable!("wide literal is a value"),
            },
            ProgramType::UInt128 => match crate::kernel::program_expression::uint128_literal(0) {
                ProgramExpression::Value(value) => value,
                _ => unreachable!("wide literal is a value"),
            },
            ProgramType::Float32 => ProgramValue::Float32(OldMachineTerm::constant(0)),
            ProgramType::Float64 => ProgramValue::Float64(OldMachineTerm::uint64_constant(0)),
            _ if value_type.is_pointer() => {
                ProgramValue::typed_pointer(Address::null(), value_type)
            }
            _ => {
                return vec![ExpressionPath {
                    outcome: ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch {
                        pointer: pointer.clone(),
                        value_type,
                        stored: None,
                    }),
                    facts,
                    obligations,
                }];
            }
        };
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::Value(value.into()),
            facts,
            obligations,
        }];
    }

    if memory.is_loadable_concretely(&pointer, value_type.byte_width()) {
        if let Some(value) = cell_value_recorded_on_path(
            if purpose == LoadPurpose::Program && value_type.pointee_type().is_none() {
                written
            } else {
                &memory
            },
            &pointer,
            value_type,
            &mut facts,
            assumptions,
            source,
            purpose,
            origin,
        ) {
            return vec![ExpressionPath {
                outcome: ExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        let Some(value) = symbolic_value(
            if purpose == LoadPurpose::Program && value_type.pointee_type().is_none() {
                written
            } else {
                &memory
            },
            &mut facts,
            assumptions,
        ) else {
            return vec![ExpressionPath {
                outcome: ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                }),
                facts,
                obligations,
            }];
        };
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    if purpose != LoadPurpose::Logical && !has_external_read_resource {
        let point = read_point.clone();
        let proposition = Proposition::MemoryLoadable {
            memory: memory.clone(),
            point,
            base: pointer.clone(),
            bytes: (OldMachineTerm::constant(value_type.byte_width())).into(),
            wide: false,
        };
        if purpose == LoadPurpose::Validity {
            if add_proof_obligation(&mut obligations, assumptions, proposition).is_none() {
                return Vec::new();
            }
        } else if assumptions.should_defer_non_exact_loadability_obligations() {
            if !assumptions.proves_memory_loadable_for_memory_resolution(
                &memory,
                &read_point,
                &pointer,
                &OldMachineTerm::constant(value_type.byte_width()),
            ) && !assumptions.proves_exact(&proposition)
                && !obligations
                    .iter()
                    .any(|obligation| obligation.proposition() == &proposition)
            {
                obligations.push(ProofObligation::new(proposition));
            }
        } else if add_proof_obligation(&mut obligations, assumptions, proposition).is_none() {
            return Vec::new();
        }
    }

    // Automatic storage is allocated by a declaration, but allocation alone
    // does not initialize it. Once all possibly-aliasing stored cells have
    // been considered above, a local load with no matching cell is an
    // uninitialized read rather than an unconstrained value — unless the
    // bytes it may read were written, by the initialization record or the
    // cells of the memory the load was read at: a store the facts could not
    // place, a havoc or a join forgot the cell's value, never that it was
    // written, and a distinct case dropped a written cell only to name the
    // value; the load then reads an unknown initialized value below. A
    // symbolic offset must not bypass this check: allocation bounds are
    // independent of whether the addressed element has ever been written.
    // The check follows the loadability obligation, which the refused path
    // keeps as a premise: a read that may leave the object is refused for
    // its bound first, and only a read inside it for unwritten bytes.
    if purpose != LoadPurpose::Logical
        && ((pointer.base.is_local_block() && memory.has_block(&pointer.base))
            || memory.may_read_uninitialized_object(&pointer, value_type.byte_width()))
        && !written.has_initialized_bytes_under(&pointer, value_type.byte_width(), assumptions)
        && !assumptions.has_memory_read_defined_evidence(written, &read_point, &pointer, value_type)
    {
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead),
            facts,
            obligations,
        }];
    }

    // Complete call outputs and untouched static words have indexed
    // versions even when their values are unknown. Use the same read as Click.
    if purpose == LoadPurpose::Program
        && let Some(origin) = origin
        && let Some(version) = origin
            .unwritten_static_scalar_version(&pointer, value_type)
            .or_else(|| {
                MachineIntegerType::from_program_type(value_type)?;
                origin.call_output_integer_version(&pointer, LoadKind::of_type(value_type)?)
            })
    {
        return vec![
            evaluate_indexed_read(version, origin, pointer, value_type, facts, obligations)
                .map_value(Into::into),
        ];
    }

    // Query the actual program state. The reduced cache above is a
    // hypothetical view for this read, not another execution transition.
    if let Some(value) = cell_value_recorded_on_path(
        if purpose == LoadPurpose::Program && value_type.pointee_type().is_none() {
            written
        } else {
            &memory
        },
        &pointer,
        value_type,
        &mut facts,
        assumptions,
        source,
        purpose,
        origin,
    ) {
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    let Some(value) = symbolic_value(
        if purpose == LoadPurpose::Program && value_type.pointee_type().is_none() {
            written
        } else {
            &memory
        },
        &mut facts,
        assumptions,
    ) else {
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch {
                pointer: pointer.clone(),
                value_type,
                stored: None,
            }),
            facts,
            obligations,
        }];
    };

    vec![ExpressionPath {
        outcome: ExpressionOutcome::Value(value),
        facts,
        obligations,
    }]
}

/// The state whose value of an abstract type at `pointer` this
/// state holds unchanged: each of the value's int32 words here is that
/// state's load at the same address, as a frame seeds an owned run's
/// words from the run's earlier contents. The value is then that
/// state's load, the term an earlier read or a resource fact names.
pub(in crate::kernel) fn abstract_value_source(
    memory: &SymbolicMemory,
    pointer: &Address,
) -> Option<ProgramPoint> {
    let mut source: Option<ProgramPoint> = None;
    for word in 0..ABSTRACT_VALUE_WIDTH / 4 {
        let address = pointer.offset_by_bytes(word * 4);
        let ProgramValue::Int32(term) = memory.known_value(&address)? else {
            return None;
        };
        let OldMachineTerm::MemoryLoad(loaded, loaded_address, LoadKind::Int32) =
            viewed_as_memory_load(&term)?
        else {
            return None;
        };
        if *loaded_address.address() != address
            || source
                .as_ref()
                .is_some_and(|source| source != loaded.point())
        {
            return None;
        }
        source = Some(loaded.into());
    }
    source
}

/// The value a C read finds for its cell in the recorded history on this
/// path, when no cached cell of `memory` answers it.
///
/// This is the cached-cell read above, asked one state further back: a
/// store at an address the facts could not place when it ran drops the cells
/// it may write, and a path that later learns the store missed this cell
/// (`u != 0` for `buf[u] = 7` and a read of `buf[0]`) reads the value the
/// cell held before it. The answer depends on the path's facts exactly as the
/// distinct-cell reduction above does, and like it is spent only on this
/// path's value; nothing is named by it. Only a program read asks: a
/// specification read denotes the named state's value, and a volatile one
/// may observe a write no recorded step made.
#[allow(clippy::too_many_arguments)]
fn cell_value_recorded_on_path(
    memory: &SymbolicMemory,
    pointer: &Address,
    value_type: ProgramType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
    origin: Option<&ProgramPoint>,
) -> Option<ExecutionValue> {
    if purpose != LoadPurpose::Program {
        return None;
    }
    let at = crate::kernel::intern_memory_ref(memory);
    let Some(value) = crate::kernel::resource_tracker::cell_value_on_path(
        &at,
        pointer,
        value_type.byte_width(),
        assumptions,
    ) else {
        // Static storage holds no entry placeholder: a cell the path's facts
        // carry unwritten back to function entry reads its entry load.
        let (entry, root) =
            crate::kernel::resource_tracker::static_cell_unwritten_since_entry_on_path(
                &at,
                pointer,
                value_type.byte_width(),
                assumptions,
            )?;
        if ProgramPoint::supports_static_entry_version(pointer, value_type)
            && let Some(version) = origin.and_then(|point| {
                point
                    .static_entry_matching_resolved_read(pointer, value_type, &entry)
                    .or_else(|| {
                        point.static_entry_matching_resolved_read(pointer, value_type, &root)
                    })
            })
        {
            let path = evaluate_indexed_read(
                version.clone(),
                &version,
                pointer.clone(),
                value_type,
                ExecutionFacts::new(),
                Vec::new(),
            );
            if let ExpressionOutcome::Value(value) = path.outcome {
                facts.extend_shared(&path.facts);
                return Some(value.into());
            }
        }
        return canonicalized_retained_symbolic_load_value_with_identity(
            entry.memory(),
            origin,
            pointer,
            value_type,
            facts,
            assumptions,
            source,
            purpose,
        );
    };
    if let Some(value) = canonicalized_pointer_value_from_int_cell(
        memory,
        pointer,
        &value.native(),
        value_type,
        facts,
        assumptions,
        source,
        purpose,
        origin,
    ) {
        return Some(value.into());
    }
    value_type
        .read_cell(&value.native())
        .map(|converted| retained_cell_conversion(&value, converted))
}

/// The state whose read of the whole pointer cell at `pointer` `memory`
/// still holds: both four-byte halves are held as that state's reads of
/// them. A held lower half alone says nothing about the upper four bytes,
/// so it never names the pointer. This reads only the two cells' contents.
fn held_pointer_cell_state(
    memory: &SymbolicMemory,
    pointer: &Address,
    lower_state: &SharedMemory,
) -> Option<SharedMemory> {
    let upper = pointer.offset_by_bytes(4);
    let ProgramValue::Int32(OldMachineTerm::MemoryLoad(state, address, LoadKind::Int32)) =
        memory.known_value(&upper)?
    else {
        return None;
    };
    (state.shared_memory() == lower_state && *address == upper).then(|| lower_state.clone())
}

/// Reinterprets a cached scalar read as a pointer while retaining its selected
/// descriptor. Complete-pointer frame evidence remains separate from the
/// numeric prefix. Only the legacy volatile route still allocates a name.
fn canonicalized_pointer_value_from_int_cell(
    memory: &SymbolicMemory,
    pointer: &Address,
    value: &ProgramValue,
    value_type: ProgramType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
    site: Option<&ProgramPoint>,
) -> Option<ProgramValue> {
    value_type.pointee_type()?;
    // `prefix_read`: the state and cell the cached prefix reads. A pointer
    // covers the whole eight-byte cell, so it is never named by the prefix's
    // own version, which a four-byte walk may select across a write to the
    // cell's upper bytes (`held_pointer_cell_state`).
    let mut prefix_read = None;
    let (fresh, defining_load) = match value {
        ProgramValue::Int8(bits @ OldMachineTerm::MemoryLoad(..)) => {
            return Some(ProgramValue::Int8(canonical_scalar_read(bits)));
        }
        ProgramValue::Int16(bits @ OldMachineTerm::MemoryLoad(..)) => {
            return Some(ProgramValue::Int16(canonical_scalar_read(bits)));
        }
        ProgramValue::Int32(bits @ OldMachineTerm::MemoryLoad(..)) => {
            if purpose == LoadPurpose::VolatileProgram {
                let fresh = load_variable_for_term(bits)?.0;
                (Some(fresh), registered_load_term_for_variable(&fresh))
            } else {
                if let OldMachineTerm::MemoryLoad(state, address, _) = bits {
                    prefix_read = Some((state.shared_memory().clone(), address.as_ref().clone()));
                }
                (None, Some(canonical_scalar_read(bits)))
            }
        }
        ProgramValue::Int32(OldMachineTerm::Variable(variable)) if is_load_variable(variable) => (
            (purpose == LoadPurpose::VolatileProgram).then_some(*variable),
            registered_load_term_for_variable(variable),
        ),
        _ => return None,
    };
    // The selected cached value already names its defining read. An address
    // alias may spell that cell with a different symbolic storage block; it
    // must not rebase the same pointer value onto that caller spelling.
    // The descriptor names the pointer value, not an offset in the
    // storage object containing it. Fresh storage provenance must not
    // manufacture disjointness from the actual pointee.
    // The cached scalar was read at `defining_load`'s address. When that is
    // not provably this cell, it is a prefix copied from elsewhere, and the
    // pointer here is this cell's own read, never the other cell's.
    let copied_prefix = matches!(
        &defining_load,
        Some(OldMachineTerm::MemoryLoad(_, address, _))
            if address.as_ref() != pointer
                && (purpose != LoadPurpose::Program || SpecificationReadScope::is_active()
                    || !crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
                        address, pointer, assumptions,
                    ))
    );
    // A volatile read may observe a value memory does not record, so it is
    // never named as the state's read of the cell.
    let loaded = if let Some(fresh) = fresh {
        Address::symbolic(fresh)
    } else if copied_prefix {
        Address::loaded_value_read_at(
            &crate::kernel::intern_memory_ref(memory).unchanged_bytes_source(),
            site,
            pointer,
        )
    } else if let Some((state, _)) = prefix_read.as_ref().filter(|(_, cell)| cell == pointer) {
        // The whole cell's read: the prefix's state when the memory still
        // holds both halves as that state's reads, else this memory.
        let from = held_pointer_cell_state(memory, pointer, state)
            .unwrap_or_else(|| crate::kernel::intern_memory_ref(memory));
        Address::canonical_read(&from, site, pointer)
    } else {
        Address::loaded(defining_load.as_ref()?).expect("selected pointer read")
    };
    let result = Pointer::from_read_at(
        loaded.clone(),
        value_type,
        &crate::kernel::intern_memory_ref(memory),
        site,
        pointer,
    );
    if purpose == LoadPurpose::Program
        && let Some(boundary) = result.provenance().as_loaded_value()
        && let Some(previous) =
            assumptions.pointer_read_source(&boundary.defining_memory, &boundary.defining_address)
    {
        // The complete read already names the memoized fact-free stopping
        // point. Check that one edge's frame; a scalar prefix alone cannot
        // establish equality of complete pointer domains.
        let ProgramValue::Pointer(before) =
            // The same read, one store edge back.
            previous.symbolic_pointer_version_load(
                Some(&boundary.point),
                &boundary.defining_address,
                value_type,
            )
        else {
            unreachable!("pointer version load")
        };
        facts.push(ExecutionPureFact::logical_pointer_value_equation(
            before,
            result.clone(),
        ));
    }
    // A scalar cache can name the numeric prefix of a pointer whose complete
    // value is still present in the recorded memory. Select that whole value
    // inside the typed read producer; never infer its bounds from the prefix
    // or publish the known pointer as an unconditional name for one cell.
    // Recovery may cross a store using separation facts. Logical reads and
    // C expressions in specification scope retain the read term; their
    // equalities belong in the graph.
    if purpose != LoadPurpose::Logical
        && !SpecificationReadScope::is_active()
        && let Some(stored) = crate::kernel::memory_history::complete_pointer_read_value(
            result.provenance(),
            assumptions,
        )
    {
        return Some(ProgramValue::Pointer(stored.with_type(value_type)));
    }
    if let Some(load) = defining_load {
        if !copied_prefix
            && (matches!(purpose, LoadPurpose::Logical | LoadPurpose::Validity)
                || purpose == LoadPurpose::Program && SpecificationReadScope::is_active())
            && let OldMachineTerm::MemoryLoad(memory, address, _) = &load
        {
            // The read is registered at the state that names it.
            match loaded.as_loaded_value() {
                Some(read)
                    if prefix_read
                        .as_ref()
                        .is_some_and(|(_, cell)| cell == pointer) =>
                {
                    assumptions.register_pointer_read_at(
                        &loaded,
                        &read.defining_memory,
                        Some(&read.point),
                        &read.defining_address,
                    )
                }
                _ => assumptions.register_pointer_read_at(
                    &loaded,
                    memory.shared_memory(),
                    Some(memory),
                    address,
                ),
            }
        }
        // Volatile observations retain their legacy opaque value until their
        // event representation migrates. Ordinary descriptors need no equation.
        if let Some(fresh) = fresh {
            record_load_variable_defining_fact_with_source_and_pointer(
                fresh, load, facts, source, None,
            );
        }
    }
    Some(ProgramValue::Pointer(result))
}

/// The value of a load at `pointer` that indexes a run of `memory`
/// symbolically, when the facts place every value of the index on the run's
/// live slots: the load of `pointer` in the run's source, which is what the
/// slot at each such index holds, or a constant run's one value.
///
/// The access must step by the run's element width from a slot boundary and
/// read the run's own element type. Every index the facts' interval admits
/// must be a live slot, so no hole, whose cell may hold a later store or
/// nothing at all, is read through the source. A live slot is the only cell
/// at its address (a store makes a hole of every slot it may meet), which is
/// the same rule that lets the equal-cell scan take an exact slot's value.
/// `None` sends the load on to the ordinary scans.
#[allow(clippy::too_many_arguments)]
fn symbolic_index_run_load(
    memory: &SymbolicMemory,
    pointer: &Address,
    value_type: ProgramType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
) -> Option<ProgramValue> {
    use crate::kernel::reasoning::memory_resolution::{RunAccess, run_access};
    // A distinct case of a split load holds its distinctness from the cells
    // split off it as path facts, not in `assumptions`: they can exclude the
    // indexes those cells held, leaving the index on the run's live slots.
    // Its context is built only when the facts alone do not place the index.
    let path_context = std::cell::OnceCell::new();
    let path_interval = |index: crate::kernel::MachineOperandView<'_>| {
        (!facts.is_empty())
            .then(|| {
                path_context
                    .get_or_init(|| {
                        crate::kernel::reasoning::path_facts::assumptions_with_path_context(
                            assumptions,
                            &*facts,
                            &[],
                        )
                    })
                    .signed_interval_past_exclusions_view(index)
            })
            .flatten()
    };
    let candidates = AliasCandidates::of_block(&pointer.base);
    let (run, index, scale, shift, wide) =
        memory.cells.candidate_runs(&candidates).find_map(|run| {
            crate::instrumentation::record_deterministic_work(1);
            let (index, scale, shift, wide) = match run_access(run, pointer) {
                RunAccess::Scaled {
                    index,
                    scale,
                    shift,
                } => (index, scale, shift, false),
                RunAccess::ScaledWide {
                    index,
                    scale,
                    shift,
                } => (index, scale, shift, true),
                _ => return None,
            };
            let width = i64::from(run.element_width());
            if run.element_type() != value_type
                || width == 0
                || scale != width
                || shift.rem_euclid(width) != 0
            {
                return None;
            }
            let first_element = shift.div_euclid(width);
            // An unsigned 64-bit index starts at zero, so its slots begin at
            // `first_element`; they all lie in one live interval when the
            // index is decided below that interval's remaining length.
            let selected = if wide {
                let first = u32::try_from(first_element).ok()?;
                run.live_intervals()
                    .intervals()
                    .iter()
                    .any(|(live_low, live_high)| {
                        *live_low <= first
                            && first < *live_high
                            && *live_high <= run.count()
                            && assumptions.decide(
                                &crate::kernel::assumptions::wide_index_comparison(
                                    CompareRelation::LessThan,
                                    index.operand_view(),
                                    crate::kernel::MachineOperandView::Old(
                                        &OldMachineTerm::uint64_constant(u64::from(
                                            *live_high - first,
                                        )),
                                    ),
                                ),
                            ) == Some(true)
                    })
            } else {
                let on_live_slots = |(low, high): (i64, i64)| {
                    let (Some(first), Some(last)) = (
                        low.checked_add(first_element),
                        high.checked_add(first_element),
                    ) else {
                        return false;
                    };
                    let (Ok(first), Ok(last)) = (u32::try_from(first), u32::try_from(last)) else {
                        return false;
                    };
                    last < run.count()
                        && run
                            .live_intervals()
                            .intervals()
                            .iter()
                            .any(|(live_low, live_high)| *live_low <= first && last < *live_high)
                };
                assumptions
                    .signed_interval_past_exclusions_view(index.operand_view())
                    .is_some_and(on_live_slots)
                    || path_interval(index.operand_view()).is_some_and(on_live_slots)
            };
            selected.then_some((run, index, scale, shift, wide))
        })?;
    use crate::kernel::primitives::RunValueMode;
    let copied_address;
    let address = match run.value_mode() {
        RunValueMode::Constant(value) => return value_type.read_cell(value),
        RunValueMode::Load => {
            if let Some(value) =
                point_named_symbolic_float_read(Some(run.source_point()), pointer, value_type)
            {
                return Some(value);
            }
            pointer
        }
        RunValueMode::Copy { source_base } => {
            // The selected index is relative to the destination run. Apply
            // that same displacement to the captured source address.
            let scaled = if wide {
                AddressOffset::int64_scaled(index, scale, true)
            } else {
                AddressOffset::int32_scaled(index, scale)
            };
            let offset = if let Some(displaced) = source_base
                .offset
                .as_const()
                .and_then(|base| base.checked_add(shift))
            {
                AddressOffset::add(AddressOffset::constant(displaced), scaled)
            } else {
                AddressOffset::add(
                    source_base.offset.clone(),
                    AddressOffset::add(scaled, AddressOffset::constant(shift)),
                )
            };
            copied_address = source_base.with_offset(offset);
            let source = run.source_point();
            if let Some(read) = point_named_cell_load(source, &copied_address, value_type) {
                return Some(crate::kernel::cell_run_value(value_type, read));
            }
            &copied_address
        }
    };
    canonicalized_symbolic_load_value_with_identity(
        run.source().memory(),
        Some(run.source_point()),
        address,
        value_type,
        facts,
        assumptions,
        source,
        purpose,
    )
}

fn complete_loaded_word(
    value: ProgramValue,
    memory: &SymbolicMemory,
    site: Option<&ProgramPoint>,
    address: &Address,
) -> ProgramValue {
    if !WordRepresentationScope::keeps_representation() {
        return match value {
            ProgramValue::PointerInteger(record) => *record.numeric,
            value => value,
        };
    }
    if !matches!(value, ProgramValue::Int64(_) | ProgramValue::UInt64(_)) {
        return value;
    }
    let bits = crate::kernel::spec::program_value_bitvector_term(&value).expect("LP64 word");
    let pointer = Pointer::from_read_at(
        Address::from_integer_address(bits),
        ProgramType::VoidPointer,
        &crate::kernel::intern_memory_ref(memory),
        site,
        address,
    );
    ProgramValue::PointerInteger(PointerIntegerValue {
        numeric: Box::new(value),
        pointer: Box::new(pointer),
        kind: PointerIntegerKind::Word { changed_bits: 0 },
    })
}

fn canonicalized_symbolic_load_value_with_identity(
    memory: &SymbolicMemory,
    site: Option<&ProgramPoint>,
    pointer: &Address,
    value_type: ProgramType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
) -> Option<ProgramValue> {
    canonicalized_retained_symbolic_load_value_with_identity(
        memory,
        site,
        pointer,
        value_type,
        facts,
        assumptions,
        source,
        purpose,
    )
    .map(ExecutionValue::into_native)
}

#[allow(clippy::too_many_arguments)]
fn canonicalized_retained_symbolic_load_value_with_identity(
    memory: &SymbolicMemory,
    site: Option<&ProgramPoint>,
    pointer: &Address,
    value_type: ProgramType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
) -> Option<ExecutionValue> {
    // An optional site is placed explicitly until the shared pointer chain
    // requires one.
    let placed = || {
        site.cloned()
            .unwrap_or_else(|| ProgramPoint::unplaced(&crate::kernel::intern_memory_ref(memory)))
    };
    // A slice read keeps the address it was written with and names the
    // read, whatever slice the cell holds (`design/rust-slice-values.md`,
    // step 2b-ii-b).
    if value_type.is_slice_pointer() {
        return Some(symbolic_slice_read(memory, placed(), pointer, value_type, facts).into());
    }
    // A logical read keeps the address it was written with: lowering is
    // fact-stable (`docs/internals/raise-lower-principle.md`). The equality graph
    // relates it to a read of the same cell through another alias. A C read
    // still selects footprint coordinates through a checked opaque address
    // alias; only the symbolic value's coordinates change, and C access
    // validity still checks the original pointer and its provenance.
    let address = if purpose == LoadPurpose::Logical {
        pointer.clone()
    } else {
        logical_memory_load_address(memory, pointer.clone(), value_type, assumptions)
    };
    // Only a complete stored word supplies a representation record. Numeric
    // equalities between loads are not a source of complete C values.
    if let Some(value @ ProgramValue::PointerInteger(_)) = memory.known_value(&address)
        && value_type.accepts(&value)
    {
        return Some((complete_loaded_word(value, memory, site, &address)).into());
    }
    if WordRepresentationScope::keeps_representation()
        && matches!(value_type, ProgramType::Int64 | ProgramType::UInt64)
        && let Some(value @ ProgramValue::PointerInteger(_)) =
            crate::kernel::memory_history::complete_pointer_carrier_read_value(
                &Address::loaded_value_read_at(
                    &crate::kernel::intern_memory_ref(memory),
                    site,
                    &address,
                ),
                assumptions,
            )
        && value_type.accepts(&value)
    {
        return Some((complete_loaded_word(value, memory, site, &address)).into());
    }
    // A logical pointer read names the cell's version, whatever pointer the
    // cell holds (`docs/internals/raise-lower-principle.md`).
    let names_version = purpose == LoadPurpose::Logical && value_type.is_pointer();
    // Canonical address selection can expose a materialized pointer cell that
    // the original spelling did not name. Reuse its complete stored value;
    // manufacturing another read here would discard the selected provenance.
    if !names_version
        && let Some(value) = memory.known_retained_value(&address)
        && value.pointer().is_some()
        && value_type.accepts(&value.native())
    {
        let stored = value.pointer().expect("selected complete pointer cell");
        facts.push(ExecutionPureFact::logical_read_equation(
            stored.clone(),
            Address::loaded_value_read_at(
                &crate::kernel::intern_memory_ref(memory),
                site,
                &address,
            ),
        ));
        if !assumptions.should_force_symbolic_external_loads() {
            return Some(value);
        }
    }
    // A stored abstract value is the value the memory holds there.
    if let Some(value @ ProgramValue::Parameter(_)) = memory.known_value(&address)
        && value_type.accepts(&value)
    {
        return Some(value.into());
    }
    // A C read whose address a checked alias selected (a call's slice
    // result read through its data pointer, `view[0]` for `let view =
    // whole(bytes);`) reads the selected cell, and is named at that cell's
    // version where its site names one, as a read written with that
    // address is; a memory-named read of the same cell would be a second
    // name for one version (`design/rust-slice-values.md`, step 3c-i).
    if address != *pointer
        && let Some(value) = point_named_symbolic_read(site, &address, value_type)
    {
        return Some(value.into());
    }
    let value = if names_version {
        record_load_access_width(memory, &address, value_type.byte_width());
        memory.symbolic_pointer_version_load(site, &address, value_type)
    } else {
        symbolic_load_value(memory, &placed(), &address, value_type)?
    };
    // Ordinary scalar reads retain their selected memory and address directly.
    match &value {
        // A signed byte read is its own load (byte R-mem relates it to the
        // byte's unsigned read).
        ProgramValue::Int8(bits @ OldMachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some((ProgramValue::Int8(read)).into());
        }
        ProgramValue::Int16(bits @ OldMachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some((ProgramValue::Int16(read)).into());
        }
        ProgramValue::Int32(bits @ OldMachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some((ProgramValue::Int32(read)).into());
        }
        ProgramValue::UInt8(bits @ OldMachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some((ProgramValue::UInt8(read)).into());
        }
        ProgramValue::UInt16(bits @ OldMachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some((ProgramValue::UInt16(read)).into());
        }
        ProgramValue::UInt32(bits @ OldMachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some((ProgramValue::UInt32(read)).into());
        }
        ProgramValue::Int64(bits @ OldMachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some(
                (complete_loaded_word(ProgramValue::Int64(read), memory, site, &address)).into(),
            );
        }
        ProgramValue::UInt64(bits @ OldMachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some(
                (complete_loaded_word(ProgramValue::UInt64(read), memory, site, &address)).into(),
            );
        }
        ProgramValue::Int128(bits @ OldMachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some((ProgramValue::Int128(read)).into());
        }
        ProgramValue::UInt128(bits @ OldMachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some((ProgramValue::UInt128(read)).into());
        }
        _ => {}
    }
    let ProgramValue::Pointer(pointer_value) = &value else {
        return Some((complete_loaded_word(value, memory, site, &address)).into());
    };
    // The read keeps its version name. The equality graph relates it to the
    // pointer stored there whenever a query names the read and memory alone
    // shows that pointer (`EqualityGraph::register_logical_read_values`); the
    // read equation beside it lets a context that keeps it reach the read from
    // the stored pointer too.
    if names_version {
        if let Some(stored) = pointer_read_over_write_decoded_value(
            pointer_value.address(),
            PointerLoadCategory::of_type(value_type),
        ) {
            facts.push(ExecutionPureFact::logical_read_equation(
                stored.with_type(value_type),
                pointer_value.address().clone(),
            ));
        }
        // The raw read of this state is the read the version names: one
        // place, so a read through an alias of the address reaches it.
        let raw = Address::loaded_value_read_at(
            &crate::kernel::intern_memory_ref(memory),
            site,
            &address,
        );
        if raw != *pointer_value.address() {
            facts.push(ExecutionPureFact::logical_read_equation(
                pointer_value.clone(),
                raw,
            ));
        }
        return Some(value.into());
    }
    // Losing a scalar cache does not lose a complete pointer stored in the
    // selected memory history. Return that whole value before minting another
    // numeric read coordinate, preserving its bounds and object class.
    // Forced symbolic reads retain the selected state's read instead;
    // recovering a representation is neither requested nor needed there.
    let complete_read = Pointer::from_read_at(
        pointer_value.address().clone(),
        value_type,
        &crate::kernel::intern_memory_ref(memory),
        site,
        &address,
    );
    // A logical or specification read keeps its term; recovery belongs to
    // executed reads, with equality reasoning in the shared graph.
    if !names_version
        && !SpecificationReadScope::is_active()
        && !assumptions.should_force_symbolic_external_loads()
        && let Some(stored) = crate::kernel::memory_history::complete_pointer_read_retained_value(
            complete_read.provenance(),
            assumptions,
        )
    {
        let pointer = stored
            .pointer()
            .expect("complete pointer recovery")
            .clone()
            .with_type(value_type);
        facts.push(ExecutionPureFact::logical_read_equation(
            pointer.clone(),
            Address::loaded_value_read_at(
                &crate::kernel::intern_memory_ref(memory),
                site,
                &address,
            ),
        ));
        return Some(retained_cell_conversion(
            &stored,
            ProgramValue::Pointer(pointer),
        ));
    }
    // A volatile read may observe a value memory does not record, so it is
    // never named as the state's read of the cell. It keeps an opaque
    // load-variable name, as a volatile read of a cached cell does.
    if purpose == LoadPurpose::VolatileProgram
        && matches!(pointer_value.address().base, AddressBase::Load(_))
    {
        let retained_state = crate::kernel::intern_memory_ref(memory);
        let bits = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::read_at_optional(&retained_state, site),
            address.clone(),
            LoadKind::Int32,
        );
        let (fresh, load) = load_variable_for_term(&bits)?;
        record_load_variable_defining_fact_with_source_and_pointer(
            fresh, load, facts, source, None,
        );
        return Some(
            (ProgramValue::Pointer(Pointer::from_read_at(
                Address::symbolic(fresh),
                value_type,
                &retained_state,
                site,
                &address,
            )))
            .into(),
        );
    }
    Some(value.into())
}

const LOAD_VARIABLE_BASE: u64 = 1 << 40;
const LOAD_VARIABLE_RANGE_SIZE: u64 = 1 << 40;

/// The most load identities one verification session may mint. The registry
/// is the only guard against two distinct loads sharing an id (the defining
/// equations `Var(id) == load(memory, pointer)` circulate as ambient truths),
/// so it must never forget an entry mid-session; exhausting it is a loud
/// verifier failure, never a silent clear.
const LOAD_VARIABLE_REGISTRY_CAPACITY: usize = 1_000_000;

#[cfg(test)]
thread_local! {
    static LOAD_VARIABLE_REGISTRY_CAPACITY_OVERRIDE: std::cell::Cell<Option<usize>> =
        const { std::cell::Cell::new(None) };
}

/// A cheap candidate filter for a pointer that may be an exact typed read.
/// Its shape is not itself evidence: indexed arithmetic can look identical.
pub(crate) fn typed_pointer_read_variable(value: &Address) -> Option<Variable> {
    Some(match (&value.base, value.offset.view()) {
        (
            AddressBase::Symbolic(variable) | AddressBase::FunctionSymbolic(variable),
            OffsetView::Constant(0),
        ) => *variable,
        _ => return None,
    })
}

fn load_variable_registry_capacity() -> usize {
    #[cfg(test)]
    if let Some(capacity) = LOAD_VARIABLE_REGISTRY_CAPACITY_OVERRIDE.with(|cell| cell.get()) {
        return capacity;
    }
    LOAD_VARIABLE_REGISTRY_CAPACITY
}

#[cfg(test)]
thread_local! {
    static LOAD_VARIABLE_RANGE_OVERRIDE: std::cell::Cell<Option<u64>> =
        const { std::cell::Cell::new(None) };
}

/// How many ids the load-variable space offers to the probe in
/// `mint_load_variable_identity`. The real range dwarfs the capacity, so a
/// collision is rare; a test narrows it to make every hash collide.
fn load_variable_range() -> u64 {
    #[cfg(test)]
    if let Some(range) = LOAD_VARIABLE_RANGE_OVERRIDE.with(|cell| cell.get()) {
        return range;
    }
    LOAD_VARIABLE_RANGE_SIZE
}

/// Runs `body` with only the first `range` load-variable ids available, so
/// distinct loads collide at the hash and a test can watch the probe.
#[cfg(test)]
pub(crate) fn with_load_variable_range<T>(range: u64, body: impl FnOnce() -> T) -> T {
    assert!(range > 0 && range <= LOAD_VARIABLE_RANGE_SIZE);
    let previous = LOAD_VARIABLE_RANGE_OVERRIDE.with(|cell| cell.replace(Some(range)));
    let result = body();
    LOAD_VARIABLE_RANGE_OVERRIDE.with(|cell| cell.set(previous));
    result
}

/// Runs `body` with the registry capacity lowered so a test can reach it.
#[cfg(test)]
pub(crate) fn with_load_variable_registry_capacity<T>(
    capacity: usize,
    body: impl FnOnce() -> T,
) -> T {
    let previous =
        LOAD_VARIABLE_REGISTRY_CAPACITY_OVERRIDE.with(|cell| cell.replace(Some(capacity)));
    let result = body();
    LOAD_VARIABLE_REGISTRY_CAPACITY_OVERRIDE.with(|cell| cell.set(previous));
    result
}

#[cfg(test)]
pub(crate) fn load_variable_registry_len() -> usize {
    LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow().len())
}

/// Whether a kernel variable id lies in the reserved load-variable id space.
/// Structural: no registry consultation, so the answer is deterministic
/// and thread-agnostic.
pub(crate) fn is_load_variable(variable: &Variable) -> bool {
    variable.is_ordinary() && LOAD_VARIABLE_RANGE.contains(&variable.0)
}

/// Whether a proposition is a load-variable defining equation
/// (a reserved read handle equated to its own structural read). Raw
/// descriptors remain recognized for retained internal equations. These
/// equations are true by construction, so path wrapping treats them as
/// ambient truths rather than premises.
pub(crate) fn is_load_variable_defining_fact(proposition: &Proposition) -> bool {
    let Some((
        OldConditionTerm::Compare {
            format: _,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        true,
    )) = proposition.old_condition()
    else {
        return false;
    };
    match (left.as_ref(), right.as_ref()) {
        (OldMachineTerm::Variable(variable), OldMachineTerm::MemoryLoad(_, _, _)) => {
            is_load_variable(variable)
        }
        (OldMachineTerm::Variable(variable), OldMachineTerm::Variable(read)) => {
            variable == read && is_load_variable(variable)
        }
        _ => false,
    }
}

/// One load variable's registry entry: the load it names, and what the
/// session has learned about it since.
#[derive(Clone)]
struct RegisteredLoad {
    /// Retain prepared components from admission, so a later query never pays
    /// for their re-insertion after unrelated weak-arena cleanup.
    address: Option<crate::kernel::SharedAddress>,
    /// Shared structural forms of this immutable descriptor. Capture/restore
    /// keeps them with the entry they describe; origins and widths do not
    /// change the value. None records an unmigrated native address payload.
    terms: std::collections::HashMap<MachineIntegerType, Option<crate::kernel::KernelTerm>>,
    /// The version point, address and kind: the load itself.
    point: ProgramPoint,
    pointer: Address,
    kind: LoadKind,
    /// Observation ownership is independent of this compatibility name.
    observation: read_observations::Id,
}

thread_local! {
    // Latest complete pointer and wide-word reads, indexed by value and
    // function epoch. Observations never change the defining name.
    // Persistent roots keep session capture/restore from copying the table.
    static POINTER_READ_OBSERVATIONS: std::cell::RefCell<
        imbl::HashMap<(u64, Address), (SharedMemory, Address)>,
    > = std::cell::RefCell::new(imbl::HashMap::new());
    static WIDE_LOAD_OBSERVATIONS: std::cell::RefCell<
        imbl::HashMap<(u64, Variable), (ProgramPoint, Address)>,
    > = std::cell::RefCell::new(imbl::HashMap::new());
    /// The read observation a memory-named pointer load was first produced from, whose
    /// epoch-scoped live origin answers what existed when the value was read
    /// (`loaded_pointer_read_predates_block`). The defining state cannot:
    /// it may be a canonical projection that keeps only the load's own block.
    static POINTER_LOAD_SOURCES: std::cell::RefCell<
        std::collections::HashMap<Load, read_observations::Id>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    /// Load variable -> the load it names (canonical memory, pointer, kind),
    /// its first-seen live origin and the origin epoch that origin was
    /// recorded in, and an access width in bytes.
    ///
    /// The kind is part of the name: two reads of one address in one state
    /// that differ in kind are two entries. The width is the framing width a
    /// later caller holding only the name walks with, which covers every
    /// access recorded at the address and so may exceed the kind's own. Mints
    /// that cannot name a width record
    /// [`resource_tracker::widest_scalar_access_bytes`], and a mint that can
    /// widens any narrower width already recorded: one entry stands for every
    /// access that resolved to this name, so it has to cover all of them.
    static LOAD_VARIABLE_REGISTRY: std::cell::RefCell<
        std::collections::HashMap<Variable, RegisteredLoad>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    /// The current origin epoch. A load variable's id names one load for the
    /// whole session, but the live state transport resolves through is
    /// first-seen within one verified function: the surface begins a new
    /// epoch per function, and the next mint in a new epoch replaces an
    /// origin recorded under an older one, which belongs to a DAG the
    /// current function's effect states never connect to.
    static LOAD_ORIGIN_EPOCH: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static LOAD_VARIABLE_CACHE: std::cell::RefCell<
        std::collections::HashMap<OldMachineTerm, (Variable, OldMachineTerm)>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    // The flag retains whether version selection used an observed width.
    // Such hits need no second metadata lookup; widening clears this cache.
    static SCALAR_READ_IDENTITY_CACHE: std::cell::RefCell<
        std::collections::HashMap<OldMachineTerm, (ScalarReadComparisonIdentity, bool)>,
    > = Default::default();
    static TERM_CACHE: std::cell::RefCell<
        std::collections::HashMap<OldMachineTerm, OldMachineTerm>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    #[cfg(test)]
    static LOAD_SUBSTITUTION_TERM_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_load_substitution_term_visits() {
    LOAD_SUBSTITUTION_TERM_VISITS.with(|visits| visits.set(0));
}

#[cfg(test)]
pub(crate) fn load_substitution_term_visits() -> usize {
    LOAD_SUBSTITUTION_TERM_VISITS.with(std::cell::Cell::get)
}

pub(crate) fn clear_load_canonicalization_caches() {
    crate::kernel::proof::term_rewrite::clear_arithmetic_comparison_cache();
    COMPARISON_FORMS.with(|cache| cache.borrow_mut().clear());
    STORED_POINTER_BLOCKS.with(|cache| cache.borrow_mut().clear());
    MEMORY_SHOWN_CELLS.with(|cache| cache.borrow_mut().clear());
    LOAD_VARIABLE_CACHE.with(|cache| cache.borrow_mut().clear());
    SCALAR_READ_IDENTITY_CACHE.with(|cache| cache.borrow_mut().clear());
    TERM_CACHE.with(|cache| cache.borrow_mut().clear());
}

/// Everything `clear_load_variable_registry` clears, as one value: the load
/// names, their origins, observations and widths, the pointer-load names, and the logical
/// pointer reads. A reusable session captures it once and restores it before
/// each check.
#[derive(Clone)]
pub(crate) struct LoadRegistryState {
    pointer_observations: imbl::HashMap<(u64, Address), (SharedMemory, Address)>,
    wide_observations: imbl::HashMap<(u64, Variable), (ProgramPoint, Address)>,
    variables: std::collections::HashMap<Variable, RegisteredLoad>,
    read_observations: read_observations::State,
    loads: crate::kernel::LoadInternerState,
    pointer_sources: std::collections::HashMap<Load, read_observations::Id>,
    widths: std::collections::HashMap<(SharedMemory, Address), u32>,
    widths_at_address: std::collections::HashMap<Address, u32>,
    origin_epoch: u64,
    logical_pointer_reads: crate::kernel::equality_graph::LogicalPointerReadsState,
}

/// How many load and pointer-load names are registered.
#[cfg(test)]
pub(crate) fn load_registry_entry_count() -> usize {
    LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow().len())
        + crate::kernel::interned_load_count()
}

pub(crate) fn capture_load_variable_registry() -> LoadRegistryState {
    LoadRegistryState {
        pointer_observations: POINTER_READ_OBSERVATIONS.with(|registry| registry.borrow().clone()),
        wide_observations: WIDE_LOAD_OBSERVATIONS.with(|registry| registry.borrow().clone()),
        variables: LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow().clone()),
        read_observations: read_observations::capture(),
        loads: crate::kernel::capture_load_interner(),
        pointer_sources: POINTER_LOAD_SOURCES.with(|sources| sources.borrow().clone()),
        widths: LOAD_ACCESS_WIDTH.with(|widths| widths.borrow().clone()),
        widths_at_address: LOAD_ACCESS_WIDTH_AT_ADDRESS.with(|widths| widths.borrow().clone()),
        origin_epoch: LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get),
        logical_pointer_reads: crate::kernel::equality_graph::capture_logical_pointer_reads(),
    }
}

pub(crate) fn restore_load_variable_registry(state: &LoadRegistryState) {
    crate::kernel::proof::fact_keys::clear_state_operand_keys();
    STORED_POINTER_BLOCKS.with(|cache| cache.borrow_mut().clear());
    POINTER_READ_OBSERVATIONS
        .with(|registry| *registry.borrow_mut() = state.pointer_observations.clone());
    WIDE_LOAD_OBSERVATIONS
        .with(|registry| *registry.borrow_mut() = state.wide_observations.clone());
    crate::kernel::equality_graph::restore_logical_pointer_reads(&state.logical_pointer_reads);
    LOAD_VARIABLE_REGISTRY.with(|registry| *registry.borrow_mut() = state.variables.clone());
    read_observations::restore(&state.read_observations);
    crate::kernel::restore_load_interner(&state.loads);
    POINTER_LOAD_SOURCES.with(|sources| *sources.borrow_mut() = state.pointer_sources.clone());
    LOAD_ACCESS_WIDTH.with(|widths| *widths.borrow_mut() = state.widths.clone());
    LOAD_ACCESS_WIDTH_AT_ADDRESS
        .with(|widths| *widths.borrow_mut() = state.widths_at_address.clone());
    LOAD_ORIGIN_EPOCH.with(|epoch| epoch.set(state.origin_epoch));
}

pub(crate) fn clear_load_variable_registry() {
    crate::kernel::proof::fact_keys::clear_state_operand_keys();
    crate::kernel::proof::term_rewrite::clear_arithmetic_comparison_cache();
    COMPARISON_FORMS.with(|cache| cache.borrow_mut().clear());
    STORED_POINTER_BLOCKS.with(|cache| cache.borrow_mut().clear());
    MEMORY_SHOWN_CELLS.with(|cache| cache.borrow_mut().clear());
    POINTER_READ_OBSERVATIONS.with(|registry| registry.borrow_mut().clear());
    WIDE_LOAD_OBSERVATIONS.with(|registry| registry.borrow_mut().clear());
    crate::kernel::equality_graph::clear_logical_pointer_reads();
    LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow_mut().clear());
    read_observations::clear();
    crate::kernel::clear_load_interner();
    POINTER_LOAD_SOURCES.with(|sources| sources.borrow_mut().clear());
    // Access widths are scoped to the verification that observed them. A
    // `local:` address is spelled the same in the next function, so a width
    // left behind would answer for an unrelated cell there.
    LOAD_ACCESS_WIDTH.with(|widths| widths.borrow_mut().clear());
    LOAD_ACCESS_WIDTH_AT_ADDRESS.with(|widths| widths.borrow_mut().clear());
    LOAD_ORIGIN_EPOCH.with(|epoch| epoch.set(0));
}

/// Starts a new load-origin epoch: the next mint of any load variable
/// records its live origin afresh, so origins registered while verifying an
/// earlier function do not answer transport in this one. Ids and their
/// canonical loads are untouched.
///
/// The naming caches are per epoch. A cached name is returned without
/// minting, and minting is what refreshes a variable's origin, so a name
/// cached by an earlier function would keep that function's origin: a later
/// function's transport would then walk the earlier function's DAG history,
/// and its proof cost would depend on what was verified before it.
pub(crate) fn begin_load_origin_epoch() {
    LOAD_ORIGIN_EPOCH.with(|epoch| epoch.set(epoch.get() + 1));
    clear_load_canonicalization_caches();
}

/// The read-over-write authority: the value a structural or named read
/// returns when its state records the cell's value at exactly
/// its address. The read retains its version, so this holds
/// at every point; it depends on the memory, never on facts.
pub(crate) fn read_over_write_value(term: &OldMachineTerm) -> Option<OldMachineTerm> {
    let OldMachineTerm::MemoryLoad(memory, pointer, kind) = viewed_as_memory_load(term)? else {
        return None;
    };
    // A slice's count is the count of the slice memory shows stored in the
    // whole cell, never a word of it.
    if kind == LoadKind::SliceCount {
        let count = stored_slice_of_load(pointer.load())?.len()?.clone();
        return (count != *term).then_some(count);
    }
    let stored = memory.shared_memory().known_value(&pointer).or_else(|| {
        memory
            .shared_memory()
            .known_value(&stored_pointer_address(&pointer)?)
    })?;
    let read = kind.read_cell(&stored)?;
    let value = crate::kernel::spec::program_value_bitvector_term(&read)?;
    (value != *term).then_some(value)
}

/// `address` with its base read through the pointer read-over-write
/// authority: an address offset from a pointer read whose state stores a
/// pointer at the read's address is that pointer, offset alike. Both steps
/// read memory, never facts.
fn stored_pointer_address(address: &Address) -> Option<Address> {
    let (AddressBase::Load(_) | AddressBase::SliceData(_)) = &address.base else {
        return None;
    };
    let read = address.with_offset(AddressOffset::constant(0));
    let stored = pointer_read_over_write_value(&read)?;
    Some(stored.with_offset(AddressOffset::add(
        stored.offset.clone(),
        address.offset.clone(),
    )))
}

thread_local! {
    static COMPARISON_FORMS: std::cell::RefCell<std::collections::HashMap<Proposition, Option<Proposition>>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
}

/// The comparison form of `proposition`: each read of a stored cell
/// replaced by the value stored there (the read-over-write authority,
/// [`read_over_write_value`]), or `None` when it reads none.
///
/// A read keeps its version name in every term a proof holds, so it can be
/// spelled and written (`docs/internals/raise-lower-principle.md`); two facts that
/// differ only by a read on one side and its stored value on the other are
/// one fact. Exact matching therefore compares comparison forms: the fact
/// stores file each fact under its comparison form as well as its own
/// (`PureFactStore::with_fact`, `PureFactContext::assume_condition_once`), an
/// exact lookup also asks for the comparison form of what it looks up, and a
/// kernel rule that compares a stated term with the one it derives compares
/// their comparison forms. This is the one place the authority enters
/// matching; a check does not resolve reads on its own.
///
/// A closed comparison, which lowering retains as written (`1u64 == 0u64`,
/// `true == false`), has the comparison form of the constant it decides, so
/// it matches the folded `false` a kernel constructor produced for the same
/// fact. Only the two literal roots are inspected.
pub(crate) fn comparison_form(proposition: &Proposition) -> Option<Proposition> {
    if let Proposition::ConditionIs(condition, value) = proposition
        && let Some(decided) = crate::kernel::machine_integer::comparison::closed_condition_value(
            condition.operand_view(),
        )
    {
        return Some(Proposition::condition_is(
            crate::kernel::StoredConditionTerm::constant(decided),
            *value,
        ));
    }
    if crate::instrumentation::deadline_exceeded_with_work(0) {
        return None;
    }
    if let Some(result) = COMPARISON_FORMS.with(|cache| cache.borrow().get(proposition).cloned()) {
        return result;
    }
    let mut result = comparison_form_uncached(proposition);
    if crate::instrumentation::deadline_exceeded_with_work(0) {
        return None;
    }
    // A closed comparison nested under connectives or binders, such as the
    // antecedent of `0 == 0 implies x == 1`, stands for the constant it
    // decides, as the top-level case above does.
    if let Some(decided) = decide_closed_conditions(result.as_ref().unwrap_or(proposition)) {
        result = Some(decided);
    }
    COMPARISON_FORMS.with(|cache| {
        let mut cache = cache.borrow_mut();
        if cache.len() >= 4096 {
            cache.clear();
        }
        cache.insert(proposition.clone(), result.clone());
    });
    result
}

/// `proposition` with each closed comparison under its connectives and
/// binders replaced by the constant it decides from its literal roots, or
/// `None` when it contains none. Visits only the proposition's own nodes.
///
/// Uncharged, like the rest of the comparison form: the form is memoized, so
/// charging its walk would make the same lookup cost differ by cache state.
fn decide_closed_conditions(proposition: &Proposition) -> Option<Proposition> {
    let pair = |left: &Proposition, right: &Proposition| {
        let decided_left = decide_closed_conditions(left);
        let decided_right = decide_closed_conditions(right);
        (decided_left.is_some() || decided_right.is_some()).then(|| {
            (
                Box::new(decided_left.unwrap_or_else(|| left.clone())),
                Box::new(decided_right.unwrap_or_else(|| right.clone())),
            )
        })
    };
    match proposition {
        Proposition::ConditionIs(condition, value)
            if condition.operand_view().constant().is_none() =>
        {
            crate::kernel::machine_integer::comparison::closed_condition_value(
                condition.operand_view(),
            )
            .map(|decided| {
                Proposition::condition_is(
                    crate::kernel::StoredConditionTerm::constant(decided),
                    *value,
                )
            })
        }
        Proposition::And(left, right) => pair(left, right).map(|(l, r)| Proposition::And(l, r)),
        Proposition::Or(left, right) => pair(left, right).map(|(l, r)| Proposition::Or(l, r)),
        Proposition::Implies(left, right) => {
            pair(left, right).map(|(l, r)| Proposition::Implies(l, r))
        }
        Proposition::Not(body) => {
            decide_closed_conditions(body).map(|body| Proposition::Not(Box::new(body)))
        }
        Proposition::ForAll {
            name,
            var,
            sort,
            body,
        } => decide_closed_conditions(body).map(|body| Proposition::ForAll {
            name: name.clone(),
            var: *var,
            sort: sort.clone(),
            body: Box::new(body),
        }),
        Proposition::Exists {
            name,
            var,
            sort,
            body,
        } => decide_closed_conditions(body).map(|body| Proposition::Exists {
            name: name.clone(),
            var: *var,
            sort: sort.clone(),
            body: Box::new(body),
        }),
        _ => None,
    }
}

fn comparison_form_uncached(proposition: &Proposition) -> Option<Proposition> {
    if let Some((condition, value)) = proposition.old_condition() {
        if let OldConditionTerm::BoolEqual(left, right) = condition {
            let left_value = read_over_write_boolean(left);
            let right_value = read_over_write_boolean(right);
            if left_value.is_some() || right_value.is_some() {
                return Some(Proposition::condition_is(
                    OldConditionTerm::bool_equal(
                        left_value.unwrap_or_else(|| left.as_ref().clone()),
                        right_value.unwrap_or_else(|| right.as_ref().clone()),
                    ),
                    *value,
                ));
            }
        } else if let Some(stored) = read_over_write_boolean(condition) {
            return Some(Proposition::condition_is(stored, *value));
        }
    }
    // SymbolicMemory states stay opaque: only the proposition's own terms are
    // visited, never the cells of a state a read names.
    let mut collector =
        crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector::uncharged();
    collector.collect_read_terms();
    collector.collect(proposition);
    let mut variables = std::collections::BTreeSet::new();
    collector.extend_into(&mut variables);
    let reads = collector.take_read_terms().collect::<Vec<_>>();
    // A read of a library or enum value is the value its state stores
    // at that address, as a scalar read is: one cell lookup, no walk. A
    // value of a type Click knows only by name is not one of these.
    let algebraic_reads = reads
        .iter()
        .filter_map(|read| {
            let OldMachineTerm::MemoryLoad(memory, pointer, LoadKind::Algebraic(read_type)) = read
            else {
                return None;
            };
            if read_type.has_abstract_size() {
                return None;
            }
            let ProgramValue::Parameter(stored) = memory.shared_memory().known_value(pointer)?
            else {
                return None;
            };
            Some(((memory.point().clone(), pointer.address().clone()), *stored))
        })
        .collect::<std::collections::HashMap<_, _>>();
    let replacements = variables
        .into_iter()
        .map(OldMachineTerm::Variable)
        .chain(reads)
        .filter_map(|read| read_over_write_value(&read).map(|value| (read, value)));
    let mut resolved =
        crate::kernel::proof::term_rewrite::TermRewrite::comparison_read_batch_with_algebraic(
            proposition,
            replacements,
            &algebraic_reads,
        )?;
    if crate::instrumentation::deadline_exceeded_with_work(0) {
        return None;
    }
    if let Some((OldConditionTerm::AddressEqual(left, right), value)) = resolved.old_condition() {
        let left_value = pointer_read_over_write_value(left);
        let right_value = pointer_read_over_write_value(right);
        if left_value.is_some() || right_value.is_some() {
            let left = left_value.unwrap_or_else(|| left.as_ref().clone());
            let right = right_value.unwrap_or_else(|| right.as_ref().clone());
            // Two reads of one stored pointer compare equal; the comparison
            // form is a lookup aid, so it states that outright.
            let condition = if left == right {
                OldConditionTerm::Constant(true)
            } else {
                OldConditionTerm::address_equal(left, right)
            };
            resolved = Proposition::condition_is(condition, *value);
        }
    }
    // A pointer value carries a provenance and bounds beside its address,
    // so each read side resolves to the whole stored value, and the
    // comparison is rebuilt from the two values: equal addresses alone never
    // make two pointer values equal.
    if let Some((OldConditionTerm::PointerEqual(left, right), value)) = resolved.old_condition() {
        let resolve = |side: &Pointer| {
            // The whole stored value defines the unmodified read. An
            // explicitly selected subobject or changed domain is a different
            // value even when it carries that same numeric read address.
            // A slice read resolves to the whole slice stored in its cell,
            // count included (`design/rust-slice-values.md`, step 2b-ii-b).
            if side.is_wide() {
                return slice_read_side_over_write_value(side);
            }
            if side != &Pointer::new(side.address().clone(), side.program_type()) {
                return None;
            }
            pointer_read_over_write_decoded_value(
                side.address(),
                PointerLoadCategory::of_type(side.program_type()),
            )
            .map(|stored| stored.with_type(side.program_type()))
        };
        let (left_value, right_value) = (resolve(left), resolve(right));
        if left_value.is_some() || right_value.is_some() {
            let left = left_value.unwrap_or_else(|| left.as_ref().clone());
            let right = right_value.unwrap_or_else(|| right.as_ref().clone());
            let condition = match OldConditionTerm::pointer_equal(left, right) {
                OldConditionTerm::AddressEqual(left, right) if left == right => {
                    OldConditionTerm::Constant(true)
                }
                // Two reads of one stored slice, count included.
                OldConditionTerm::PointerEqual(left, right) if left.is_wide() && left == right => {
                    OldConditionTerm::Constant(true)
                }
                condition => condition,
            };
            resolved = Proposition::condition_is(condition, *value);
        }
    }
    (&resolved != proposition).then_some(resolved)
}

/// A Boolean read gets the logical value of its recorded store. For an
/// exact read, the selected point's index can supply that store directly.
fn read_over_write_boolean(condition: &OldConditionTerm) -> Option<OldConditionTerm> {
    let OldConditionTerm::Compare {
        format: MachineIntegerType::UInt8,
        relation: CompareRelation::Equal,
        left,
        right,
    } = condition.bool_negation_operand()?
    else {
        return None;
    };
    if right.bool_constant_value() != Some(false) {
        return None;
    }
    let OldMachineTerm::MemoryLoad(point, pointer, LoadKind::UInt8) = left.as_ref() else {
        return None;
    };
    let version;
    let point = if point.is_exact_read() {
        version = point.indexed_typed_version(pointer, ProgramType::Bool)?;
        &version
    } else {
        point
    };
    let ProgramValue::Bool(stored) = point.indexed_stored_value()?.native() else {
        return None;
    };
    Some(OldConditionTerm::truth_of_bool_word(stored))
}

/// Arithmetic congruence for selected comparison queries. Unlike the
/// read-over-write form, this is not an additional fact to publish or index.
pub(crate) fn arithmetic_comparison_form(proposition: &Proposition) -> Option<Proposition> {
    let resolved = comparison_form(proposition);
    crate::kernel::proof::term_rewrite::TermRewrite::arithmetic_comparison(
        resolved.as_ref().unwrap_or(proposition),
    )
    .or(resolved)
}

/// One read-over-write reduction, using only the read's defining store.
/// A cached value at a later state is not this evidence. Never follow a
/// predecessor, alias, or another pointer read here. A read projection has
/// one retained source endpoint; looking up that endpoint is not a history walk.
pub(crate) fn pointer_read_over_immediate_store(pointer: &Address) -> Option<Address> {
    crate::instrumentation::record_deterministic_work(1);
    let read = pointer.as_loaded_value()?;
    if !matches!(read.displacement.view(), OffsetView::Constant(0)) {
        return None;
    }

    if let Some(ProgramValue::Pointer(stored)) = read
        .point
        .indexed_stored_value()
        .map(StoredMemoryValue::native)
    {
        return Some(stored.address().clone());
    }
    let source = crate::kernel::prelude::canonical_load_projection_source(
        &read.defining_memory,
        &read.defining_address,
    );
    let derivation = source
        .as_ref()
        .unwrap_or(&read.defining_memory)
        .derivation()?;
    let MemoryDerivation::Store {
        pointer: written,
        value,
        ..
    } = derivation.as_ref()
    else {
        return None;
    };
    let ProgramValue::Pointer(value) = value.native() else {
        return None;
    };
    (written == &read.defining_address).then(|| value.address().clone())
}

/// The read-over-write authority for a pointer read: the pointer stored at
/// the read's address in the state it reads, as a cell or as the pointer
/// view of a union cell, when that state records one. A cell holding the
/// read itself resolves to nothing.
pub(crate) fn pointer_read_over_write_value(pointer: &Address) -> Option<Address> {
    pointer_read_over_write_program_value(pointer).map(|stored| stored.address().clone())
}

/// The pointer a recorded store wrote to the cell a load reads, for a
/// decoding of `category`. Any store of a pointer of the same category
/// answers, whatever pointee type either names: the stored value keeps its
/// own type, and a caller that knows the reading term's type retags it. No
/// category asks about the cell's bytes as an address, which a store of
/// either category answers. The category is the decoding's, passed here,
/// never the load's: one cell at one version point is one load.
fn indexed_pointer_read_value(
    point: &ProgramPoint,
    address: &Address,
    category: Option<PointerLoadCategory>,
) -> Option<Pointer> {
    // The answer depends only on the load's version point, never on which
    // selection kind (exact, indexed write, indexed cell, entry, call output)
    // built the load first: a version-named load asks the index at its
    // point. An indexed write finds its own write there; an entry or a call
    // output finds no store. A memory-named load has no index to ask.
    point.read_version_id()?;
    crate::instrumentation::record_deterministic_work(1);
    let version = point.indexed_pointer_version(address, category)?;
    let ProgramValue::Pointer(stored) = version.indexed_stored_value()?.native() else {
        return None;
    };
    decodes_as(stored, category).then(|| stored.clone())
}

/// The slice memory alone shows stored in the whole cell `load` reads
/// (`design/rust-slice-values.md`, step 2b-ii-b): the store the load's
/// version point indexes, or the cell its state holds when the
/// assumption-free version walk shows it standing. A store into either word
/// ends both. One indexed lookup, or the memoized walk the pointer authority
/// takes; never facts.
pub(crate) fn stored_slice_of_load(load: &crate::kernel::Load) -> Option<Pointer> {
    crate::instrumentation::record_deterministic_work(1);
    let point = load.point();
    let indexed = point
        .read_version_id()
        .and_then(|_| point.indexed_slice_version(load.cell()))
        .and_then(|version| {
            version
                .indexed_stored_value()
                .map(|stored| stored.native().clone())
        });
    let stored = match indexed {
        Some(stored) => stored,
        None => memory_shown_cell_value(
            point.shared_memory(),
            load.cell(),
            crate::kernel::WIDE_POINTER_BYTE_WIDTH,
        )?,
    };
    match stored {
        ProgramValue::Pointer(stored) if stored.is_wide() => Some(stored),
        _ => None,
    }
}

/// The read-over-write authority for a slice read: the slice stored in the
/// cell the read names, at the read's slice type, when memory alone shows
/// one ([`stored_slice_of_load`]). Only the whole read resolves; a slice
/// built from parts of reads is not a read.
pub(crate) fn slice_read_over_write_value(slice: &Pointer) -> Option<Pointer> {
    let load = slice.slice_read_load()?;
    let stored = stored_slice_of_load(load)?.with_type(slice.program_type());
    (stored != *slice).then_some(stored)
}

/// A slice read as one side of a comparison form, whose count the batch of
/// scalar reads may already have replaced by the stored count: its data
/// pointer, when it is the read's, becomes the stored slice's, and a count
/// still read resolves as the scalar authority resolves it. A slice whose
/// data pointer is not a read's resolves to nothing.
fn slice_read_side_over_write_value(side: &Pointer) -> Option<Pointer> {
    let AddressBase::SliceData(load) = &side.address().base else {
        return None;
    };
    let read = Pointer::slice_read(load.point().clone(), load.cell(), side.program_type());
    if side.as_ptr() != read.as_ptr() {
        return None;
    }
    let stored = stored_slice_of_load(load)?;
    let count = side.len()?;
    let count = read_over_write_value(count).unwrap_or_else(|| count.clone());
    Some(
        stored
            .as_ptr()
            .with_element_count(count)
            .with_type(side.program_type()),
    )
}

/// A symbolic read of the slice cell at `address`
/// (`design/rust-slice-values.md`, step 2b-ii-b): the slice the cell's load
/// decodes to ([`Pointer::slice_read`]), whatever the cell holds, so a logical
/// read keeps its name and a read of an unknown cell names the read. When
/// memory alone shows a slice stored there, the read equation beside it
/// relates the read to it; the read is never replaced by it.
fn symbolic_slice_read(
    memory: &SymbolicMemory,
    point: ProgramPoint,
    address: &Address,
    value_type: ProgramType,
    facts: &mut ExecutionFacts,
) -> ProgramValue {
    record_load_access_width(memory, address, crate::kernel::WIDE_POINTER_BYTE_WIDTH);
    let read = Pointer::slice_read(
        ProgramPoint::read_at(&crate::kernel::intern_memory_ref(memory), &point),
        address,
        value_type,
    );
    if let Some(stored) = slice_read_over_write_value(&read) {
        facts.push(ExecutionPureFact::logical_pointer_value_equation(
            stored,
            read.clone(),
        ));
    }
    ProgramValue::Pointer(read)
}

/// Whether a stored pointer is the value of a decoding of `category`: a
/// function-pointer store answers no object-pointer decoding, nor the
/// reverse (`design/loads.md`, "Pointers"). No category accepts either.
fn decodes_as(stored: &Pointer, category: Option<PointerLoadCategory>) -> bool {
    // A stored slice is a two-word cell, never one pointer word: no
    // decoding of a pointer read, nor the bytes as an address, reads it
    // until a layout fact states its words (`design/rust-slice-values.md`).
    !stored.is_wide()
        && category.is_none_or(|category| {
            PointerLoadCategory::of_type(stored.program_type()) == Some(category)
        })
}

/// The complete pointer stored at this read's address, when the state's
/// typed point index or fact-free version walk establishes it. Retained
/// caches alone are not evidence.
///
/// The address alone names the load's bytes, not a decoding of them, so a
/// store of either pointer category answers;
/// [`pointer_read_over_write_decoded_value`] asks for one decoding.
pub(crate) fn pointer_read_over_write_program_value(pointer: &Address) -> Option<Pointer> {
    pointer_read_over_write_decoded_value(pointer, None)
}

/// [`pointer_read_over_write_program_value`] for the decoding of the load at
/// `category`: a store of the other category answers nothing.
pub(crate) fn pointer_read_over_write_decoded_value(
    pointer: &Address,
    category: Option<PointerLoadCategory>,
) -> Option<Pointer> {
    // A slice's data pointer is the data pointer of the slice stored in the
    // whole cell (`design/rust-slice-values.md`, step 2b-ii-b).
    if let AddressBase::SliceData(load) = &pointer.base {
        if !matches!(pointer.offset.view(), OffsetView::Constant(0)) {
            return None;
        }
        let data = stored_slice_of_load(load)?.as_ptr();
        return decodes_as(&data, category).then_some(data);
    }
    let read = pointer.as_loaded_value()?;
    if !matches!(read.displacement.view(), OffsetView::Constant(0)) {
        return None;
    }

    if let Some(stored) = indexed_pointer_read_value(&read.point, &read.defining_address, category)
    {
        return Some(stored);
    }
    // Only a cached pointer can be the stored pointer; anything else needs no
    // walk of the cell's history, nor a run's element built to look at.
    if !holds_pointer_cell(read.defining_memory.memory(), &read.defining_address) {
        return None;
    }
    let ProgramValue::Pointer(stored) = memory_shown_cell_value(
        &read.defining_memory,
        &read.defining_address,
        crate::kernel::C_POINTER_BYTE_WIDTH,
    )?
    else {
        return None;
    };
    (stored.address() != pointer && decodes_as(&stored, category)).then_some(stored)
}

thread_local! {
    // [`memory_shown_cell_value`] is a function of the interned state, the
    // address and the width, so it is memoized per session; a query met again
    // while its own walk runs (the walk asks block distinctness, which asks
    // this) answers nothing rather than recursing.
    static MEMORY_SHOWN_CELLS: std::cell::RefCell<
        std::collections::HashMap<(SharedMemory, Address, u32), Option<ProgramValue>>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    static MEMORY_SHOWN_IN_PROGRESS: std::cell::RefCell<
        std::collections::HashSet<(SharedMemory, Address, u32)>,
    > = std::cell::RefCell::new(std::collections::HashSet::new());
}

/// Whether `memory` caches a whole pointer at exactly `address`, as a cell or
/// as a union cell's pointer view.
fn holds_pointer_cell(memory: &SymbolicMemory, address: &Address) -> bool {
    matches!(
        memory
            .cells
            .concrete()
            .get(address)
            .map(StoredMemoryValue::native),
        Some(ProgramValue::Pointer(_))
    ) || memory.known_union_pointer(address).is_some()
}

/// The value `memory` holds at exactly `address`, as a cell or as the pointer
/// view of a union cell, when memory alone shows it: the assumption-free
/// version walk (`resource_tracker::last_same`) stops at a step that wrote
/// the cell. A cell a havoc kept because a fact showed it separate holds its
/// value only where that fact holds, so it gives nothing here; the
/// read-over-write authority never stands in for a frame fact.
fn memory_shown_cell_value(
    memory: &SharedMemory,
    address: &Address,
    bytes: u32,
) -> Option<ProgramValue> {
    let key = (memory.clone(), address.clone(), bytes);
    if let Some(hit) = MEMORY_SHOWN_CELLS.with(|cache| cache.borrow().get(&key).cloned()) {
        return hit;
    }
    if !MEMORY_SHOWN_IN_PROGRESS.with(|running| running.borrow_mut().insert(key.clone())) {
        return None;
    }
    let shown = memory_shown_cell_value_uncached(memory, address, bytes);
    MEMORY_SHOWN_IN_PROGRESS.with(|running| running.borrow_mut().remove(&key));
    MEMORY_SHOWN_CELLS.with(|cache| {
        let mut cache = cache.borrow_mut();
        if cache.len() >= 100_000 {
            cache.clear();
        }
        cache.insert(key, shown.clone());
    });
    shown
}

fn memory_shown_cell_value_uncached(
    memory: &SharedMemory,
    address: &Address,
    bytes: u32,
) -> Option<ProgramValue> {
    // The read's own state must hold the cell: a projection interned from
    // several sources names its oldest, which need not be this read's.
    let held = memory
        .known_value(address)
        .or_else(|| memory.known_union_pointer(address))?;
    let source = crate::kernel::prelude::canonical_load_projection_source(memory, address)
        .unwrap_or_else(|| memory.clone());
    let (last_memory, last_stopped_by) =
        crate::kernel::resource_tracker::last_same_cell_memory(&source, address, bytes.into())?;
    // The step the walk stopped at must have left the cached cell standing
    // for the cell's bytes by memory alone. A store elsewhere that overlaps
    // the cell changed some of them, whatever a cached cell still says; a
    // havoc keeps a cell only where a frame fact showed it separate, and that
    // fact, not the cache, is the authority for it.
    match last_memory.derivation().as_deref() {
        Some(MemoryDerivation::Store { pointer, value, .. })
            if last_stopped_by.reason == crate::kernel::resource_tracker::StopReason::Affected
                && (pointer != address || value.byte_width() < bytes) =>
        {
            None
        }
        Some(MemoryDerivation::CallHavoc { .. } | MemoryDerivation::LoopHavoc { .. }) => None,
        // A step the walk could not show separate from the cell (a store or a
        // release through an unrelated address) left the cache standing only
        // where a fact shows it separate.
        _ if matches!(
            last_stopped_by.reason,
            crate::kernel::resource_tracker::StopReason::NotShownSeparate(_)
        ) =>
        {
            None
        }
        _ => Some(held),
    }
}

/// Whether `proposition` holds by the read-over-write authority alone: its
/// reads of stored cells, replaced by the values stored there, leave a
/// constant truth. Such a fact states nothing beyond the memory it reads.
pub(crate) fn holds_by_read_over_write(proposition: &Proposition) -> bool {
    comparison_form(proposition)
        .is_some_and(|resolved| crate::kernel::reasoning::path_facts::solve_builtin_prop(&resolved))
}

/// `value` with its term read through the read-over-write authority: what a
/// logical read of a stored cell evaluates to, as a diagnostic or a test
/// reports it, now that the read names its version.
pub(crate) fn read_over_write_program_value(value: &ProgramValue) -> ProgramValue {
    let resolve = |term: &OldMachineTerm| read_over_write_value(term).unwrap_or(term.clone());
    match value {
        ProgramValue::Int8(term) => ProgramValue::Int8(resolve(term)),
        ProgramValue::Int16(term) => ProgramValue::Int16(resolve(term)),
        ProgramValue::Int32(term) => ProgramValue::Int32(resolve(term)),
        ProgramValue::UInt8(term) => ProgramValue::UInt8(resolve(term)),
        ProgramValue::UInt16(term) => ProgramValue::UInt16(resolve(term)),
        ProgramValue::UInt32(term) => ProgramValue::UInt32(resolve(term)),
        ProgramValue::Int64(term) => ProgramValue::Int64(resolve(term)),
        ProgramValue::UInt64(term) => ProgramValue::UInt64(resolve(term)),
        value => value.clone(),
    }
}

/// The load represented by a load variable minted on this thread.
/// Reasoning uses this to consult the state lazily: a load variable in
/// an equality query is viewed as its load exactly where a load term would
/// have triggered memory-history evidence.
pub(crate) fn registered_load_for_variable(variable: &Variable) -> Option<(SharedMemory, Address)> {
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        registry
            .borrow()
            .get(variable)
            .map(|load| (load.point.shared_memory().clone(), load.pointer.clone()))
    })
}

/// [`registered_load_for_variable`] with the registered read's point, so a
/// read rebuilt from it is placed where the registered one was.
pub(crate) fn registered_load_point_for_variable(
    variable: &Variable,
) -> Option<(ProgramPoint, Address)> {
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        registry
            .borrow()
            .get(variable)
            .map(|load| (load.point.clone(), load.pointer.clone()))
    })
}

/// The load term a load variable names, kind included: the right-hand side
/// of its defining equation.
pub(crate) fn registered_load_term_for_variable(variable: &Variable) -> Option<OldMachineTerm> {
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        registry.borrow().get(variable).map(|load| {
            crate::kernel::OldMachineTerm::read_named(
                load.point.clone(),
                load.pointer.clone(),
                load.kind,
            )
        })
    })
}

/// Retain a registered read as structure once, without expanding its address
/// on every imported use. The descriptor is immutable within its registry entry.
pub(crate) fn registered_scalar_read_term(
    variable: &Variable,
    format: MachineIntegerType,
) -> Option<crate::kernel::KernelTerm> {
    crate::instrumentation::record_deterministic_work(1);
    let (term, observation) = LOAD_VARIABLE_REGISTRY.with(|registry| {
        let mut registry = registry.borrow_mut();
        let read = registry.get_mut(variable)?;
        let term = read
            .terms
            .entry(format)
            .or_insert_with(|| {
                read.address.as_ref().map(|address| {
                    crate::kernel::KernelTerm::shared_scalar_read_descriptor(
                        format,
                        &read.point,
                        address,
                        read.kind,
                    )
                })
            })
            .clone();
        Some((term, read.observation))
    })?;
    if let Some(term) = &term {
        read_observations::remember_term(term, observation);
    }
    term
}

/// A selected read's observation data, distinct from its immutable value.
pub(crate) struct ScalarReadObservation {
    pub point: ProgramPoint,
    pub pointer: Address,
    pub kind: LoadKind,
    pub bytes: u32,
    /// The producing observation in the current load-origin epoch.
    pub origin: Option<ProgramPoint>,
}

mod read_observations;
#[cfg(test)]
mod read_site_tests;
mod scalar_reads;

use scalar_reads::{ScalarReadComparisonIdentity, ScalarReadDescriptor};

pub(crate) fn scalar_read_observation(
    operand: crate::kernel::MachineOperandView<'_>,
) -> Option<ScalarReadObservation> {
    read_observations::for_operand(operand)
}

pub(in crate::kernel) fn scalar_read_origin_for_cell(
    point: &ProgramPoint,
    address: &Address,
    kind: LoadKind,
) -> Option<SharedMemory> {
    read_observations::origin_for_cell(point, address, kind)
}

/// Build an exact read and publish its typed observation. This does not
/// select a comparison identity or change the supplied memory state. Use
/// `OldMachineTerm::memory_read` when no observation needs to be published.
#[cfg(test)]
#[track_caller]
pub(crate) fn scalar_read_for_exact_cell(
    memory: &SharedMemory,
    pointer: &Address,
    kind: LoadKind,
    bytes: u32,
) -> OldMachineTerm {
    scalar_read_for_exact_cell_at(&ProgramPoint::unplaced(memory), pointer, kind, bytes)
}

#[cfg_attr(test, track_caller)]
pub(crate) fn scalar_read_for_exact_cell_at(
    point: &ProgramPoint,
    pointer: &Address,
    kind: LoadKind,
    bytes: u32,
) -> OldMachineTerm {
    let id = read_observations::record_at(point, pointer, kind, point, bytes);
    read_observations::select(id);
    crate::kernel::OldMachineTerm::read_named(point.clone(), pointer.clone(), kind)
}

pub(crate) fn is_selected_scalar_read(
    point: &ProgramPoint,
    pointer: &Address,
    kind: LoadKind,
) -> bool {
    read_observations::selected(point, pointer, kind)
}

/// The access width registered by a typed producer for this exact descriptor.
pub(in crate::kernel) fn observed_scalar_read_width(
    point: &ProgramPoint,
    pointer: &Address,
    kind: LoadKind,
) -> Option<u32> {
    read_observations::existing_at(point, pointer, kind).and_then(read_observations::bytes)
}

/// Existing observation metadata is evidence of an access width too. Merely
/// inspecting a retained read must not replace it with the unknown-width default.
fn existing_read_access_width(
    memory: &SharedMemory,
    pointer: &Address,
    kind: LoadKind,
) -> Option<u32> {
    read_observations::existing(memory, pointer, kind).and_then(read_observations::bytes)
}

/// The kind of read a load variable names.
pub(crate) fn registered_load_kind_for_variable(variable: &Variable) -> Option<LoadKind> {
    LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow().get(variable).map(|load| load.kind))
}

/// The block a pointer read's value lies in by the read-over-write authority:
/// the block of the pointer memory alone shows stored at the read's address
/// (`memory_shown_cell_value`). `None` when memory shows no pointer there.
/// The base names the load's bytes as an address, so a store of either
/// pointer category answers.
pub(crate) fn loaded_pointer_stored_block(load: &Load) -> Option<AddressBase> {
    let mut current = load.clone();
    let mut path = Vec::new();
    let (terminal, complete) = loop {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(cached) =
            STORED_POINTER_BLOCKS.with(|cache| cache.borrow().get(&current).cloned())
        {
            break (Some(cached.unwrap_or_else(|| current.base())), true);
        }
        if !STORED_POINTER_BLOCKS_RUNNING
            .with(|running| running.borrow_mut().insert(current.clone()))
        {
            // A memory naming walk can ask about the read it is resolving.
            // That recursive question supplies no definition and is not memoized.
            break (None, false);
        }
        path.push(current.clone());
        match immediate_stored_address_base(&current) {
            Some(AddressBase::Load(next)) => current = next,
            Some(block) => break (Some(block), true),
            None => break (Some(current.base()), true),
        }
    };
    for read in path {
        STORED_POINTER_BLOCKS_RUNNING.with(|running| running.borrow_mut().remove(&read));
        if complete {
            let value = terminal
                .clone()
                .filter(|block| !matches!(block, AddressBase::Load(load) if *load == read));
            STORED_POINTER_BLOCKS.with(|cache| cache.borrow_mut().insert(read, value));
        }
    }
    terminal.filter(|block| !matches!(block, AddressBase::Load(own) if own == load))
}

thread_local! {
    static STORED_POINTER_BLOCKS: std::cell::RefCell<std::collections::HashMap<Load, Option<AddressBase>>> = std::cell::RefCell::new(std::collections::HashMap::new());
    static STORED_POINTER_BLOCKS_RUNNING: std::cell::RefCell<std::collections::HashSet<Load>> = std::cell::RefCell::new(std::collections::HashSet::new());
}

fn immediate_stored_address_base(load: &Load) -> Option<AddressBase> {
    stored_pointer_for_load(load, None).map(|pointer| pointer.into_pointer().base.clone())
}

/// The pointer stored at the load's cell, for its decoding at `category`
/// (none: the bytes as an address).
fn stored_pointer_for_load(load: &Load, category: Option<PointerLoadCategory>) -> Option<Pointer> {
    let (point, cell) = (load.point(), load.cell());
    if let Some(stored) = indexed_pointer_read_value(point, cell, category) {
        return Some(stored);
    }
    let memory = point.shared_memory();
    if !holds_pointer_cell(memory.memory(), cell) {
        return None;
    }
    let ProgramValue::Pointer(stored) =
        memory_shown_cell_value(memory, cell, crate::kernel::C_POINTER_BYTE_WIDTH)?
    else {
        return None;
    };
    (!matches!(&stored.address().base, AddressBase::Load(own) if own == load)
        && decodes_as(&stored, category))
    .then_some(stored)
}

/// The stored address of the pointer read, decoded at `category` (none: the
/// bytes as an address). A recorded typed store supplies the address even
/// when the memory view no longer caches it.
pub(crate) fn loaded_pointer_stored_address(
    load: &Load,
    category: Option<PointerLoadCategory>,
) -> Option<Address> {
    let address = stored_pointer_for_load(load, category)?.into_pointer();
    (!matches!(&address.base, AddressBase::Load(own) if own == load)).then_some(address)
}

thread_local! {
    /// `(retained_state, address)` -> how many bytes the C load there reads.
    ///
    /// A `MemoryLoad` term carries its own read's kind, but one address may
    /// be read at several widths, and a framing walk about the address has to
    /// cover all of them; without this a caller has to assume the widest
    /// scalar, and an `int32` load stops being separable from a store four
    /// bytes away. The entry is written by [`symbolic_load_value`], the one
    /// typed entry point every C load passes through, before any naming can
    /// happen.
    static LOAD_ACCESS_WIDTH: std::cell::RefCell<
        std::collections::HashMap<(SharedMemory, Address), u32>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());

    /// `address` -> the widest C load seen at it, in any state.
    ///
    /// How wide the access at an address is comes from the C type being
    /// loaded, which does not vary with the state. The exact key above is
    /// still preferred, because it answers for one particular load; this one
    /// answers for a walk that reached the address through a state no
    /// typed load was ever performed at, which is every framing walk that
    /// starts at a later state than the load it is carrying.
    ///
    /// Widening on conflict, so a `char` view and a `long` view of one
    /// address answer with the `long`: over-stating a width can only shrink
    /// the separated set.
    static LOAD_ACCESS_WIDTH_AT_ADDRESS: std::cell::RefCell<
        std::collections::HashMap<Address, u32>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// Remembers that a load of `bytes` bytes happens at this address in this
/// state. Widening on conflict: the entry has to cover every access that
/// resolves through it. A declared array element counts as already recorded
/// at its declared width.
pub(in crate::kernel) fn record_load_access_width(
    memory: &SymbolicMemory,
    pointer: &Address,
    bytes: u32,
) {
    let key = (
        crate::kernel::intern_memory(memory.clone()),
        pointer.clone(),
    );
    // A recorded width can only ever widen, and a name computed under the
    // narrower one is stale: the version walk a narrow access takes crosses
    // stores the wider one stops at, so it names the load at an older
    // state. `LOAD_VARIABLE_CACHE` is keyed by the term alone — a term
    // carries its own kind, not the widest access recorded at its address —
    // so widening has to drop the names that were derived before it.
    // Widening is rare; a name being the answer to a question this
    // table has since changed is not something a later reader can detect.
    let mut widened = false;
    let mut widen = |known: &mut u32| {
        if bytes > *known {
            *known = bytes;
            widened = true;
        }
    };
    LOAD_ACCESS_WIDTH.with(|widths| {
        let mut widths = widths.borrow_mut();
        if widths.len() >= 100_000 {
            widths.clear();
        }
        match widths.get_mut(&key) {
            Some(known) => widen(known),
            None => {
                widths.insert(key, bytes);
            }
        }
    });
    LOAD_ACCESS_WIDTH_AT_ADDRESS.with(|widths| {
        let mut widths = widths.borrow_mut();
        if widths.len() >= 100_000 {
            widths.clear();
        }
        match widths.get_mut(pointer) {
            Some(known) => widen(known),
            None => {
                widths.insert(pointer.clone(), bytes);
            }
        }
    });
    if widened {
        LOAD_VARIABLE_CACHE.with(|cache| cache.borrow_mut().clear());
        SCALAR_READ_IDENTITY_CACHE.with(|cache| cache.borrow_mut().clear());
    }
}

/// Says that a load of `bytes` bytes happens at this address, the way
/// [`symbolic_load_value`] says it for a typed C load.
///
/// Kernel tests build `MemoryLoad` terms by hand, without the C load that
/// records its address's width. Without a declaration such an address stands
/// in the widest scalar, which no store four bytes away can be separated
/// from. A test that means "the `int32` at this address" says so here.
#[cfg(test)]
pub(in crate::kernel) fn declare_load_access_width(pointer: &Address, bytes: u32) {
    LOAD_ACCESS_WIDTH_AT_ADDRESS.with(|widths| {
        widths
            .borrow_mut()
            .entry(pointer.clone())
            .and_modify(|known| *known = (*known).max(bytes))
            .or_insert(bytes);
    });
}

/// The width of the C load recorded at this address in this state, when
/// one was. `None` means no typed load was seen here, and the caller stands
/// in [`crate::kernel::resource_tracker::widest_scalar_access_bytes`].
pub(crate) fn recorded_load_access_width(memory: &SharedMemory, pointer: &Address) -> Option<u32> {
    LOAD_ACCESS_WIDTH
        .with(|widths| {
            widths
                .borrow()
                .get(&(memory.clone(), pointer.clone()))
                .copied()
        })
        .or_else(|| {
            // This state saw no typed load here, but the address still has
            // a width if any state did: the C type at an address does not
            // change with the state a framing walk happens to start from.
            recorded_load_access_width_at_address(pointer)
        })
}

/// The widest C load recorded at this address in any state.
fn recorded_load_access_width_at_address(pointer: &Address) -> Option<u32> {
    LOAD_ACCESS_WIDTH_AT_ADDRESS.with(|widths| widths.borrow().get(pointer).copied())
}

/// The access width to use for a load named only by a term.
pub(crate) fn load_access_width_or_widest(memory: &SharedMemory, pointer: &Address) -> u32 {
    recorded_load_access_width(memory, pointer)
        .unwrap_or_else(crate::kernel::resource_tracker::widest_scalar_access_bytes)
}

/// The access width a framing walk uses for a `kind` read at this address:
/// the width recorded there, never narrower than the read itself.
pub(crate) fn load_term_access_width(
    memory: &SharedMemory,
    pointer: &Address,
    kind: LoadKind,
) -> u32 {
    recorded_load_access_width(memory, pointer)
        .or_else(|| existing_read_access_width(memory, pointer, kind))
        .unwrap_or_else(|| kind.unrecorded_access_byte_width())
        .max(kind.byte_width())
}

/// The widest C load recorded at this address in any state, or the widest
/// scalar when none was seen.
///
/// The state-keyed form above is the precise one and is what a caller
/// holding an interned state asks. This one is for a caller holding a bare
/// `SymbolicMemory` it would have to intern only to ask the question, where the C
/// type at the address is the whole answer anyway: every framing comparison
/// runs at a state later than the load it is carrying, so the exact key
/// would miss and fall through to this table regardless.
/// The bytes a `kind` read at `pointer` reaches for a framing check: a
/// value of abstract type's whole object, else the widest access recorded
/// at the address, never narrower than the read.
pub(crate) fn load_access_extent(pointer: &Address, kind: LoadKind) -> crate::kernel::AccessExtent {
    match kind.extent() {
        object @ crate::kernel::AccessExtent::Object(_) => object,
        crate::kernel::AccessExtent::Bytes(bytes) => crate::kernel::AccessExtent::Bytes(
            load_access_width_at_address_or_widest(pointer).max(bytes),
        ),
    }
}

pub(crate) fn load_access_width_at_address_or_widest(pointer: &Address) -> u32 {
    recorded_load_access_width_at_address(pointer)
        .unwrap_or_else(crate::kernel::resource_tracker::widest_scalar_access_bytes)
}

/// How many bytes the access this variable names reads.
///
/// This is the widest access any mint of the name asked for, which can exceed
/// the name's own kind ([`registered_load_kind_for_variable`]) when the
/// address is also read wider. `None` means the variable is not a registered
/// load; a caller that needs a width anyway uses
/// [`crate::kernel::resource_tracker::widest_scalar_access_bytes`].
pub(crate) fn registered_load_bytes_for_variable(variable: &Variable) -> Option<u32> {
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        registry
            .borrow()
            .get(variable)
            .and_then(|load| read_observations::bytes(load.observation))
    })
}

/// The first-seen live state a load variable was minted from in the
/// current origin epoch. The canonical form is a jumped placeholder unsuited
/// to frame checks; transport resolves through this origin, which is
/// DAG-connected and cell-comparable to later effect states of the
/// function that minted it. First-seen is deterministic because mint order
/// is execution order; per-epoch because two functions in one session can
/// mint the same variable from unconnected states.
pub(crate) fn registered_load_origin_for_variable(
    variable: &Variable,
) -> Option<(SharedMemory, Address)> {
    let read = scalar_read_observation(crate::kernel::MachineOperandView::Old(
        &OldMachineTerm::Variable(*variable),
    ))?;
    Some((read.origin?.into_shared_memory(), read.pointer))
}

/// [`registered_load_origin_for_variable`] with the origin's point.
pub(crate) fn registered_load_origin_point_for_variable(
    variable: &Variable,
) -> Option<(ProgramPoint, Address)> {
    let read = scalar_read_observation(crate::kernel::MachineOperandView::Old(
        &OldMachineTerm::Variable(*variable),
    ))?;
    Some((read.origin?, read.pointer))
}

/// [`registered_load_origin_for_variable`] as the load term it names there:
/// the same read, kind included, at the live origin.
pub(crate) fn registered_load_origin_term_for_variable(
    variable: &Variable,
) -> Option<OldMachineTerm> {
    let read = scalar_read_observation(crate::kernel::MachineOperandView::Old(
        &OldMachineTerm::Variable(*variable),
    ))?;
    Some(crate::kernel::OldMachineTerm::read_named(
        read.origin?,
        read.pointer,
        read.kind,
    ))
}

/// Whether the pointer a load variable names was obtained before `block`
/// existed, so cannot point into it: a pointer value read at a state
/// cannot hold the address of an object that state does not have.
///
/// The reference is the load's live origin, the state it was first read in,
/// never its canonical memory, which may be a projection that leaves
/// unrelated blocks out. Local and heap blocks are judged. A local exists
/// from the step that declares it into the state, so a local the origin
/// does not hold, and has not ended, was declared after the read. A heap
/// identity is handed out by a `malloc` in the state that records it as
/// pending, then live, then freed, and is never reused within a proof, so a
/// heap identity the origin has none of those records for was allocated
/// after the read.
pub(crate) fn loaded_pointer_predates_block(variable: &Variable, block: &AddressBase) -> bool {
    if !block.is_local_block() && !matches!(block, AddressBase::Heap(_)) {
        return false;
    }
    let Some((origin, _)) = registered_load_origin_for_variable(variable) else {
        return false;
    };
    match block {
        AddressBase::Heap(identity) => !origin.heap_identity_allocated(*identity),
        _ => !origin.has_block(block) && !origin.forgotten.ended_local_blocks.contains(block),
    }
}

/// Retain the selected read's observation independently of any scalar name.
pub(crate) fn record_pointer_load_source(load: &Load, read: &OldMachineTerm) {
    let OldMachineTerm::MemoryLoad(memory, address, kind) = read else {
        return;
    };
    if let Some(observation) = read_observations::existing_at(memory, address, *kind) {
        POINTER_LOAD_SOURCES.with(|sources| {
            sources
                .borrow_mut()
                .entry(load.clone())
                .or_insert(observation);
        });
    }
}

fn pointer_load_origin(load: &Load) -> Option<SharedMemory> {
    // A version point is the state the value was read in.
    if load.is_point_named() {
        return Some(load.point().shared_memory().clone());
    }
    let observation = POINTER_LOAD_SOURCES.with(|sources| sources.borrow().get(load).copied())?;
    Some(
        read_observations::observation(observation)?
            .origin?
            .into_shared_memory(),
    )
}

pub(crate) fn loaded_pointer_read_predates_block(load: &Load, block: &AddressBase) -> bool {
    if !block.is_local_block() && !matches!(block, AddressBase::Heap(_)) {
        return false;
    }
    let Some(origin) = pointer_load_origin(load) else {
        return false;
    };
    match block {
        AddressBase::Heap(identity) => !origin.heap_identity_allocated(*identity),
        _ => !origin.has_block(block) && !origin.forgotten.ended_local_blocks.contains(block),
    }
}

pub(crate) fn loaded_pointer_read_heap_identities(load: &Load) -> Option<Vec<u64>> {
    Some(pointer_load_origin(load)?.allocated_heap_identities())
}

/// Views a term as a memory load for equality reasoning: load terms pass
/// through, and registered load variables resolve to the loads they
/// represent. Other terms are not loads.
pub(crate) fn viewed_as_memory_load(term: &OldMachineTerm) -> Option<OldMachineTerm> {
    match term {
        OldMachineTerm::MemoryLoad(_, _, _) => Some(term.clone()),
        OldMachineTerm::Variable(variable) => registered_load_term_for_variable(variable),
        _ => None,
    }
}

/// Conservative read presence for transport planning: structural reads and
/// reserved names count even when a name has not yet been registered. MemoryState
/// variable summaries retain the existing single-load presence shortcut.
pub(crate) fn proposition_mentions_load_variable(proposition: &Proposition) -> bool {
    if proposition_mentions_structural_read(proposition) {
        return true;
    }
    let mut variables = std::collections::BTreeSet::new();
    crate::kernel::reasoning::variable_collection::collect_proposition_variables_for_load_presence(
        proposition,
        &mut variables,
    );
    variables.iter().any(is_load_variable)
}

fn proposition_mentions_structural_read(proposition: &Proposition) -> bool {
    let mut collector =
        crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector::uncharged();
    collector.collect_read_terms();
    collector.collect(proposition);
    collector.take_read_terms().next().is_some()
}

/// The identities load variables are minted from.
pub(crate) const LOAD_VARIABLE_RANGE: std::ops::Range<u64> =
    LOAD_VARIABLE_BASE..LOAD_VARIABLE_BASE + LOAD_VARIABLE_RANGE_SIZE;

/// The comparison form: assumption-free read-over-write canonicalization
/// followed by structural selection of unresolved scalar reads. This is a
/// checker operation; lowering retains the read even when its value is known.
/// Deterministic and idempotent. The traversal is linear and uses explicit
/// worklists. Shallow terms are memoized; deep terms bypass the recursive
/// structural key and take the same complete path directly.
///
/// [`canonicalize_atomic_loads`]: crate::kernel::memory_history::canonicalize_atomic_loads
pub(crate) fn canonical_term(term: &OldMachineTerm) -> OldMachineTerm {
    let cacheable = crate::kernel::memory_history::term_is_shallow_structural_cache_key(term);
    if cacheable && let Some(hit) = TERM_CACHE.with(|cache| cache.borrow().get(term).cloned()) {
        return hit;
    }
    let structural = crate::kernel::memory_history::canonicalize_atomic_loads(term);
    // Register the live observation before its projected form can claim the
    // load's origin. Keep the established projected canonical identity.
    if matches!(term, OldMachineTerm::MemoryLoad(..))
        && matches!(structural, OldMachineTerm::MemoryLoad(..))
    {
        canonical_scalar_read(term);
    }
    let result = select_scalar_reads(&structural);
    if cacheable {
        TERM_CACHE.with(|cache| {
            let mut cache = cache.borrow_mut();
            if cache.len() >= 100_000 {
                cache.clear();
            }
            cache.insert(term.clone(), result.clone());
        });
    }
    result
}

/// The canonical form for a pointer offset. Shared scaled indices retain
/// their structure; legacy indices take their [`canonical_term`] form.
pub(crate) fn canonical_offset_term(offset: &AddressOffset) -> AddressOffset {
    enum Task<'a> {
        Visit(&'a AddressOffset),
        RebuildAdd,
    }
    let mut tasks = vec![Task::Visit(offset)];
    let mut results = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(offset) => match offset.view() {
                OffsetView::Constant(_) | OffsetView::Variable(_) => results.push(offset.clone()),
                OffsetView::Add(left, right) => {
                    tasks.push(Task::RebuildAdd);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                }
                OffsetView::Int32Scaled { index, .. } | OffsetView::Int64Scaled { index, .. }
                    if index.shared_operand().is_some() =>
                {
                    // This child was constructed already. Reopening its read
                    // would change its identity and repeatedly walk its prefix.
                    results.push(offset.clone());
                }
                OffsetView::Int32Scaled { index, byte_width } => {
                    results.push(AddressOffset::scale_int32(
                        canonical_term(
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
                    canonical_term(
                        index
                            .retained_written_operand()
                            .expect("shared indices handled above"),
                    ),
                    byte_width,
                    unsigned,
                )),
            },
            Task::RebuildAdd => {
                let right = results.pop().expect("visited right offset");
                let left = results.pop().expect("visited left offset");
                results.push(AddressOffset::add(left, right));
            }
        }
    }
    results.pop().expect("canonicalization produces one offset")
}

/// Keep an index's read structure at the producer boundary.
pub(crate) fn canonicalized_offset_index_term(
    bits: OldMachineTerm,
    _facts: &mut ExecutionFacts,
) -> OldMachineTerm {
    let bits = bits.into_index_word32();
    let observed = if term_mentions_a_memory_load(&bits) {
        select_scalar_reads(&bits)
    } else {
        bits
    };
    let index = SharedMachineIntegerTerm::index(MachineIntegerType::Int32, observed);
    index.structural_value().clone()
}

/// Legacy selected-version read policy shared by execution, resource
/// materialization, and contract evaluation. Exact descriptor construction is
/// `OldMachineTerm::memory_read`; this adapter still retains the comparison
/// identity as the read term until those callers migrate to exact states.
pub(crate) fn canonical_form_of_load(
    memory: SharedMemory,
    pointer: Address,
    kind: LoadKind,
) -> OldMachineTerm {
    canonical_scalar_read(&OldMachineTerm::memory_read(memory, pointer, kind))
}

/// [`canonical_form_of_load`] of the read made at `site`: named by `site`'s
/// memory, as that function names it, and recording `site` as the read site
/// (`ProgramPoint::at_read_site`). The term is the same.
#[cfg_attr(test, track_caller)]
pub(crate) fn canonical_form_of_load_at(
    site: &ProgramPoint,
    pointer: Address,
    kind: LoadKind,
) -> OldMachineTerm {
    canonical_scalar_read(&OldMachineTerm::read_named(
        ProgramPoint::read_at(site.shared_memory(), site),
        pointer,
        kind,
    ))
}

/// Name a resource cell by its indexed store or entry point when available.
pub(crate) fn canonical_cell_load(
    source: &ProgramPoint,
    pointer: &Address,
    ty: ProgramType,
) -> OldMachineTerm {
    if let Some(read) = point_named_cell_load(source, pointer, ty) {
        return read;
    }
    let kind = LoadKind::of_type(ty).expect("scalar cell read kind");
    canonical_form_of_load_at(source, pointer.clone(), kind)
}

/// Construct a cell read when its recorded point can supply a name.
pub(in crate::kernel) fn point_named_cell_load(
    source: &ProgramPoint,
    pointer: &Address,
    ty: ProgramType,
) -> Option<OldMachineTerm> {
    let read = expected_point_named_cell_read(source, pointer, ty)?;
    record_indexed_cell_read(source, &read);
    Some(read)
}

/// Name a typed cell exposed by a resource view.
pub(crate) fn canonical_cell_value(
    source: &ProgramPoint,
    pointer: &Address,
    value_type: ProgramType,
) -> ProgramValue {
    if let ProgramType::Parameter(parameter) = value_type {
        return AlgebraicTermNode::parameter_cell_load(source, pointer.clone(), parameter);
    }
    if value_type == ProgramType::Bool
        && let Some(value) = point_named_symbolic_read(Some(source), pointer, value_type)
    {
        return value;
    }
    if let Some(read) = point_named_pointer_cell_read(source, pointer, value_type) {
        return ProgramValue::Pointer(read);
    }
    crate::kernel::cell_run_value(value_type, canonical_cell_load(source, pointer, value_type))
}

/// Name a complete pointer cell from its typed store or entry point.
pub(crate) fn point_named_pointer_cell_read(
    source: &ProgramPoint,
    pointer: &Address,
    value_type: ProgramType,
) -> Option<Pointer> {
    if !value_type.is_pointer() {
        return None;
    }
    let version = source.ordinary_typed_version(pointer, value_type)?;
    Some(Pointer::from_point_read(version, value_type, pointer))
}

fn indexed_resource_scalar_read(
    source: &ProgramPoint,
    pointer: &Address,
    ty: ProgramType,
) -> Option<OldMachineTerm> {
    MachineIntegerType::from_program_type(ty)?;
    let kind = LoadKind::of_type(ty)?;
    let point = source.indexed_integer_version(pointer, kind)?;
    Some(crate::kernel::OldMachineTerm::read_named(
        point,
        pointer.clone(),
        kind,
    ))
}

pub(in crate::kernel) fn expected_point_named_cell_read(
    source: &ProgramPoint,
    pointer: &Address,
    ty: ProgramType,
) -> Option<OldMachineTerm> {
    point_named_float_load(source, pointer, ty)
        .or_else(|| indexed_resource_scalar_read(source, pointer, ty))
        .or_else(|| {
            let kind = LoadKind::of_type(ty)?;
            let point = source.entry_cell_version(pointer, ty)?;
            Some(crate::kernel::OldMachineTerm::read_named(
                point,
                pointer.clone(),
                kind,
            ))
        })
}

pub(in crate::kernel) fn observe_entry_integer_cell(
    source: &ProgramPoint,
    pointer: &Address,
) -> Option<OldMachineTerm> {
    let kind = LoadKind::Int32;
    let point = source.entry_integer_version(pointer, kind)?;
    let read = crate::kernel::OldMachineTerm::read_named(point, pointer.clone(), kind);
    record_indexed_cell_read(source, &read);
    Some(read)
}

fn record_indexed_cell_read(source: &ProgramPoint, read: &OldMachineTerm) {
    let OldMachineTerm::MemoryLoad(version, pointer, kind) = read else {
        unreachable!("indexed resource read")
    };
    read_observations::record_at(version, pointer, *kind, source, kind.byte_width());
}

/// The test-only audit of the creation-time invariant (see
/// `docs/internals/canonicalization.md`): while
/// `count_canonical_at_creation_violations` is counting on this thread,
/// every condition fact entering a `PureFactContext` is compared with its
/// canonical form. Each distinct (rewrite kind, creating module) pair is
/// reported once on stderr with an example, where the creating module is
/// the innermost `click::` frame outside the generic context-construction
/// and reasoning layers. Defining facts are exempt: they are the base of
/// the construction. The report is the work list for establishing the
/// invariant at every creation point. Off, this is one thread-local read.
pub(crate) fn check_canonical_at_creation(condition: &OldConditionTerm, value: bool) {
    thread_local! {
        static SEEN: std::cell::RefCell<std::collections::BTreeSet<(String, String)>> =
            const { std::cell::RefCell::new(std::collections::BTreeSet::new()) };
    }
    if !CANONICAL_AT_CREATION_VIOLATIONS.with(|count| count.get().is_some()) {
        return;
    }
    let proposition = Proposition::condition_is(condition.clone(), value);
    if is_load_variable_defining_fact(&proposition) || is_store_fact(condition, value) {
        return;
    }
    let canonical = canonical_condition(condition);
    if &canonical == condition {
        return;
    }
    CANONICAL_AT_CREATION_VIOLATIONS.with(|count| {
        if let Some(seen) = count.get() {
            count.set(Some(seen + 1));
        }
    });
    let kind = if !condition_mentions_a_memory_load(&canonical) {
        let mut variables = std::collections::BTreeSet::new();
        crate::kernel::reasoning::variable_collection::collect_condition_bitvector_variables(
            &canonical,
            &mut variables,
        );
        if variables.iter().any(is_load_variable) {
            "load -> load variable"
        } else {
            "load -> recorded value"
        }
    } else {
        "load rewritten, still a load"
    };
    const GENERIC: [&str; 12] = [
        "check_canonical_at_creation",
        "assume_condition",
        "assume_proposition",
        "assumptions_from_propositions",
        "assumptions_with_path_context",
        "assumptions_with_propositions",
        "PureFactStore::",
        "atomic_derivation_premises",
        "derive_proposition",
        "::proves",
        "PureFactContext>::",
        "path_facts::",
    ];
    let backtrace = std::backtrace::Backtrace::force_capture().to_string();
    let creator = backtrace
        .lines()
        .filter_map(|line| line.trim().split_once(": ").map(|(_, frame)| frame))
        .find(|frame| {
            frame.starts_with("click::") && !GENERIC.iter().any(|generic| frame.contains(generic))
        })
        .map(|frame| {
            frame
                .split("::{{closure}}")
                .next()
                .unwrap_or(frame)
                .trim_start_matches("click::")
                .to_string()
        })
        .unwrap_or_else(|| "<no click frame>".to_string());
    let first_time = SEEN.with(|seen| {
        seen.borrow_mut()
            .insert((kind.to_string(), creator.clone()))
    });
    if !first_time {
        return;
    }
    let width = 240usize;
    let shown = format!("{condition:?}");
    let shown = &shown[..shown.len().min(width)];
    eprintln!("CANONICAL-AT-CREATION violation [{kind}] created in {creator}\n  example: {shown}");
}

thread_local! {
    /// `Some(n)` while a creation-time invariant audit is counting
    /// violations on this thread; `None` otherwise (the check is off).
    static CANONICAL_AT_CREATION_VIOLATIONS: std::cell::Cell<Option<usize>> =
        const { std::cell::Cell::new(None) };
}

/// Runs `body` with the creation-time invariant check on, returning the
/// body's result and the number of condition facts that entered a
/// `PureFactContext` in a non-canonical form. The standing regression for
/// `docs/internals/canonicalization.md` asserts zero over fixture verification.
#[cfg(test)]
pub(crate) fn count_canonical_at_creation_violations<T>(body: impl FnOnce() -> T) -> (T, usize) {
    let previous = CANONICAL_AT_CREATION_VIOLATIONS.with(|count| count.replace(Some(0)));
    let result = body();
    let violations = CANONICAL_AT_CREATION_VIOLATIONS
        .with(|count| count.replace(previous))
        .unwrap_or(0);
    (result, violations)
}

/// Whether a condition is a store fact `load(after, p) == v` where `after`
/// records `v` at `p`: the memory-content counterpart of a defining fact,
/// exported from a certified store record and cited by certificates through
/// `at(statement(n).exit, ...)`. Like defining facts, store facts are the
/// base the invariant rests on and keep their load term.
pub(crate) fn is_store_fact(condition: &OldConditionTerm, value: bool) -> bool {
    if !value {
        return false;
    }
    let OldConditionTerm::Compare {
        format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
        relation: CompareRelation::Equal,
        left,
        right,
    } = condition
    else {
        return false;
    };
    let (load, stored) = match (left.as_ref(), right.as_ref()) {
        (OldMachineTerm::MemoryLoad(memory, pointer, kind), stored)
        | (stored, OldMachineTerm::MemoryLoad(memory, pointer, kind)) => {
            ((memory, pointer, kind), stored)
        }
        _ => return false,
    };
    let Some(value) = load.0.shared_memory().known_value(load.1) else {
        return false;
    };
    matches!(
        load.2.read_cell(&value),
        Some(crate::kernel::integer32_c_value!(recorded)) if &recorded == stored
    )
}

/// Memory canonicalization treats these logical values as written, including
/// any reads inside their operands.
fn keeps_written_condition(view: BooleanOperandView<'_>) -> bool {
    view.is_bool_value_form()
        || view.is_integer_comparison()
        || match view {
            BooleanOperandView::Shared(root) => matches!(
                root.node(),
                KernelTermNode::BoolLiteral(_)
                    | KernelTermNode::Variable(_)
                    | KernelTermNode::AlgebraicEqual { .. }
                    | KernelTermNode::PointerEqual(_)
            ),
            BooleanOperandView::Native(condition) => matches!(
                condition,
                OldConditionTerm::Constant(_)
                    | OldConditionTerm::Variable(_)
                    | OldConditionTerm::AlgebraicEqual(..)
                    | OldConditionTerm::PointerEqual(..)
            ),
        }
}

fn canonical_address(address: &Address) -> Address {
    address.with_offset(canonical_offset_term(&address.offset))
}

/// The canonical form for a condition: every operand takes its
/// [`canonical_term`] form, so terms that are equal by definition compare
/// identically. The comparison direction of the canonical model for
/// whole facts.
pub(crate) fn canonical_condition(condition: &OldConditionTerm) -> OldConditionTerm {
    match condition {
        _ if keeps_written_condition(BooleanOperandView::Native(condition)) => condition.clone(),
        OldConditionTerm::Float32(float_condition) => {
            OldConditionTerm::Float32(float_condition.map_bitvector_terms(canonical_term))
        }
        OldConditionTerm::Float64(float_condition) => {
            OldConditionTerm::Float64(float_condition.map_bitvector_terms(canonical_term))
        }
        OldConditionTerm::AddressOffsetEqual(left, right) => OldConditionTerm::AddressOffsetEqual(
            Box::new(canonical_offset_term(left)),
            Box::new(canonical_offset_term(right)),
        ),
        OldConditionTerm::AddressEqual(left, right) => OldConditionTerm::AddressEqual(
            Box::new(canonical_address(left)),
            Box::new(canonical_address(right)),
        ),
        condition => {
            let (op, left, right) = condition
                .as_bitvector_comparison()
                .expect("every other condition has its own arm");
            op.build_raw(canonical_term(left), canonical_term(right))
        }
    }
}

/// The canonical form for a condition fact; non-condition propositions pass
/// through unchanged.
pub(crate) fn canonical_condition_fact(fact: &Proposition) -> Proposition {
    let Proposition::ConditionIs(condition, value) = fact else {
        return fact.clone();
    };
    if keeps_written_condition(condition.operand_view()) {
        return fact.clone();
    }
    // Canonicalize the written displacements, keeping the producer's block
    // payload and the raw equality even when both operands become identical.
    use crate::kernel::{PointerEquality, StoredConditionTerm};
    let root = match condition.pointer_equality() {
        Some(PointerEquality::Address(pair)) => {
            KernelTerm::address_equal_raw(pair.each_ref().map(|address| {
                canonical_address(address.written().expect("written address")).into_shared()
            }))
        }
        Some(PointerEquality::Offset(pair)) => {
            KernelTerm::address_offset_equal_raw(pair.each_ref().map(|offset| {
                canonical_offset_term(AddressOffset::try_from_ref(offset).expect("written offset"))
                    .into_shared()
            }))
        }
        _ => return Proposition::condition_is(canonical_condition(condition.old_form()), *value),
    };
    Proposition::condition_is(
        StoredConditionTerm::from_root(root).expect("logical equality"),
        *value,
    )
}

/// Select unresolved read descriptors with an explicit worklist. Range-fold
/// bodies remain scoped and are not assigned a global read identity.
fn select_scalar_reads(term: &OldMachineTerm) -> OldMachineTerm {
    select_scalar_reads_impl(term, false)
}

/// Prepare an equality-graph expression by selecting only read identities.
/// Preserve a producer-selected read exactly; never substitute cached values.
pub(in crate::kernel) fn select_graph_scalar_reads(term: &OldMachineTerm) -> OldMachineTerm {
    select_scalar_reads_impl(term, true)
}

fn select_scalar_reads_impl(term: &OldMachineTerm, retain_selected: bool) -> OldMachineTerm {
    enum Task<'a> {
        VisitTerm(&'a OldMachineTerm),
        VisitCondition(&'a OldConditionTerm),
        VisitOffset(&'a AddressOffset),
        RebuildBinary(BitvectorBinaryOp),
        RebuildUnary(BitvectorUnaryOp),
        RebuildIf,
        RebuildBoolCast(MachineIntegerType),
        RebuildPureFunction {
            name: String,
            argument_count: usize,
        },
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
    }

    let mut tasks = vec![Task::VisitTerm(term)];
    let mut term_results = Vec::new();
    let mut condition_results = Vec::new();
    let mut offset_results = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::VisitTerm(term) => {
                #[cfg(test)]
                LOAD_SUBSTITUTION_TERM_VISITS.with(|visits| visits.set(visits.get() + 1));
                match term {
                    OldMachineTerm::ThreadHandle(_) => term_results.push(term.clone()),
                    bits32_constant!(_)
                    | int64_constant!(_)
                    | uint64_constant!(_)
                    | native_constant!(_, _) => term_results.push(term.clone()),
                    OldMachineTerm::Variable(variable) => {
                        term_results.push(
                            registered_load_term_for_variable(variable)
                                .unwrap_or_else(|| term.clone()),
                        );
                    }
                    OldMachineTerm::MemoryLoad(memory, pointer, kind) => {
                        term_results.push(if memory.is_exact_read() {
                            comparison_identity_of_exact_read(memory, pointer, *kind)
                        } else if retain_selected && is_selected_scalar_read(memory, pointer, *kind)
                        {
                            term.clone()
                        } else {
                            canonical_scalar_read(term)
                        });
                    }
                    OldMachineTerm::IntegerAddress(_, _)
                    | OldMachineTerm::IntegerToMachine { .. } => term_results.push(term.clone()),
                    OldMachineTerm::ClickFunctionApplication { .. }
                    | OldMachineTerm::PureApplicationCount(_)
                    | OldMachineTerm::AlgebraicMatch { .. } => term_results.push(term.clone()),
                    OldMachineTerm::If {
                        condition,
                        then_term,
                        else_term,
                    } => {
                        tasks.push(Task::RebuildIf);
                        tasks.push(Task::VisitTerm(else_term));
                        tasks.push(Task::VisitTerm(then_term));
                        tasks.push(Task::VisitCondition(condition));
                    }
                    OldMachineTerm::BoolCast { to, value } => {
                        tasks.push(Task::RebuildBoolCast(*to));
                        tasks.push(Task::VisitCondition(value));
                    }
                    // A fold is a binder boundary: loads in its body can mention
                    // bound variables and therefore do not have a global load
                    // identity. Preserve the whole scoped term verbatim.
                    OldMachineTerm::RangeFold { .. } => term_results.push(term.clone()),
                    OldMachineTerm::PureFunctionApplication { name, arguments } => {
                        tasks.push(Task::RebuildPureFunction {
                            name: name.clone(),
                            argument_count: arguments.len(),
                        });
                        for argument in arguments.iter().rev() {
                            tasks.push(Task::VisitTerm(argument));
                        }
                    }
                    term => match (term.as_binary(), term.as_unary()) {
                        (Some((op, left, right)), _) => {
                            tasks.push(Task::RebuildBinary(op));
                            tasks.push(Task::VisitTerm(right));
                            tasks.push(Task::VisitTerm(left));
                        }
                        (_, Some((op, value))) => {
                            tasks.push(Task::RebuildUnary(op));
                            tasks.push(Task::VisitTerm(value));
                        }
                        _ => unreachable!("every other variant has its own arm"),
                    },
                }
            }
            Task::VisitCondition(condition) => match condition {
                _ if keeps_written_condition(BooleanOperandView::Native(condition)) => {
                    condition_results.push(condition.clone())
                }
                OldConditionTerm::Float32(float_condition) => {
                    let term_count = match float_condition {
                        FloatCondition::Comparison { .. } => 2,
                        FloatCondition::Classification { .. } => 1,
                    };
                    tasks.push(Task::RebuildFloatCondition {
                        is_float64: false,
                        condition: float_condition.clone(),
                        term_count,
                    });
                    match float_condition {
                        FloatCondition::Comparison { left, right, .. } => {
                            tasks.push(Task::VisitTerm(right));
                            tasks.push(Task::VisitTerm(left));
                        }
                        FloatCondition::Classification { value, .. } => {
                            tasks.push(Task::VisitTerm(value));
                        }
                    }
                }
                OldConditionTerm::Float64(float_condition) => {
                    let term_count = match float_condition {
                        FloatCondition::Comparison { .. } => 2,
                        FloatCondition::Classification { .. } => 1,
                    };
                    tasks.push(Task::RebuildFloatCondition {
                        is_float64: true,
                        condition: float_condition.clone(),
                        term_count,
                    });
                    match float_condition {
                        FloatCondition::Comparison { left, right, .. } => {
                            tasks.push(Task::VisitTerm(right));
                            tasks.push(Task::VisitTerm(left));
                        }
                        FloatCondition::Classification { value, .. } => {
                            tasks.push(Task::VisitTerm(value));
                        }
                    }
                }
                OldConditionTerm::AddressOffsetEqual(left, right) => {
                    tasks.push(Task::RebuildAddressOffsetEqual);
                    tasks.push(Task::VisitOffset(right));
                    tasks.push(Task::VisitOffset(left));
                }
                OldConditionTerm::AddressEqual(left, right) => {
                    tasks.push(Task::RebuildAddressEqual {
                        left_block: left.base.clone(),
                        right_block: right.base.clone(),
                    });
                    tasks.push(Task::VisitOffset(&right.offset));
                    tasks.push(Task::VisitOffset(&left.offset));
                }
                condition => {
                    let (op, left, right) = condition
                        .as_bitvector_comparison()
                        .expect("every other condition has its own arm");
                    tasks.push(Task::RebuildConditionBinary(op));
                    tasks.push(Task::VisitTerm(right));
                    tasks.push(Task::VisitTerm(left));
                }
            },
            Task::VisitOffset(offset) => match offset.view() {
                OffsetView::Constant(_) | OffsetView::Variable(_) => {
                    offset_results.push(offset.clone())
                }
                OffsetView::Add(left, right) => {
                    tasks.push(Task::RebuildOffsetAdd);
                    tasks.push(Task::VisitOffset(right));
                    tasks.push(Task::VisitOffset(left));
                }
                OffsetView::Int32Scaled { index, .. } | OffsetView::Int64Scaled { index, .. }
                    if index.shared_operand().is_some() =>
                {
                    // This child was constructed already. Reopening its read
                    // would change its identity and repeatedly walk its prefix.
                    offset_results.push(offset.clone());
                }
                // The view owns the index, so its written operand is walked
                // by a nested walk, at the point the operand's task would be
                // popped. Nesting follows the source: a nested walk needs an
                // address comparison written inside an index.
                OffsetView::Int32Scaled { index, byte_width } => {
                    let value = select_scalar_reads_impl(
                        index
                            .retained_written_operand()
                            .expect("shared indices handled above"),
                        retain_selected,
                    );
                    offset_results.push(AddressOffset::scale_int32(value, byte_width));
                }
                OffsetView::Int64Scaled {
                    index,
                    byte_width,
                    unsigned,
                } => {
                    let value = select_scalar_reads_impl(
                        index
                            .retained_written_operand()
                            .expect("shared indices handled above"),
                        retain_selected,
                    );
                    offset_results.push(AddressOffset::scale_int64(value, byte_width, unsigned));
                }
            },
            // Integer operators and conversions are rebuilt as bare nodes;
            // float operators and the machine cast through their smart
            // constructors.
            Task::RebuildBinary(op) => {
                let right = term_results.pop().expect("visited right term");
                let left = term_results.pop().expect("visited left term");
                term_results.push(if op.is_float() {
                    op.build(left, right)
                } else {
                    op.build_raw(left, right)
                });
            }
            Task::RebuildUnary(op) => {
                let value = term_results.pop().expect("visited unary term");
                let smart = op.is_float()
                    || matches!(
                        op,
                        BitvectorUnaryOp::Cast {
                            spelling: MachineCastSpelling::Generic,
                            ..
                        }
                    );
                term_results.push(if smart {
                    op.build(value)
                } else {
                    op.build_raw(value)
                });
            }
            Task::RebuildBoolCast(to) => {
                let value = condition_results.pop().expect("visited cast operand");
                term_results.push(OldMachineTerm::BoolCast {
                    to,
                    value: Box::new(value),
                });
            }
            Task::RebuildIf => {
                let else_term = term_results.pop().expect("visited else term");
                let then_term = term_results.pop().expect("visited then term");
                let condition = condition_results.pop().expect("visited condition");
                term_results.push(OldMachineTerm::If {
                    condition: Box::new(condition),
                    then_term: Box::new(then_term),
                    else_term: Box::new(else_term),
                });
            }
            Task::RebuildPureFunction {
                name,
                argument_count,
            } => {
                let first = term_results.len() - argument_count;
                let arguments = term_results.split_off(first);
                term_results.push(OldMachineTerm::rebuild_pure_application(name, arguments));
            }
            Task::RebuildConditionBinary(op) => {
                let right = term_results.pop().expect("visited right condition operand");
                let left = term_results.pop().expect("visited left condition operand");
                condition_results.push(op.build_raw(left, right));
            }
            Task::RebuildFloatCondition {
                is_float64,
                condition,
                term_count,
            } => {
                let first = term_results.len() - term_count;
                let mut index = first;
                let rebuilt = condition.map_bitvector_terms(|_| {
                    let term = term_results[index].clone();
                    index += 1;
                    term
                });
                term_results.truncate(first);
                condition_results.push(if is_float64 {
                    OldConditionTerm::Float64(rebuilt)
                } else {
                    OldConditionTerm::Float32(rebuilt)
                });
            }
            Task::RebuildAddressOffsetEqual => {
                let right = offset_results.pop().expect("visited right pointer offset");
                let left = offset_results.pop().expect("visited left pointer offset");
                condition_results.push(OldConditionTerm::AddressOffsetEqual(
                    Box::new(left),
                    Box::new(right),
                ));
            }
            Task::RebuildAddressEqual {
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
            Task::RebuildOffsetAdd => {
                let right = offset_results.pop().expect("visited right pointer offset");
                let left = offset_results.pop().expect("visited left pointer offset");
                offset_results.push(AddressOffset::add(left, right));
            }
        }
    }
    assert_eq!(term_results.len(), 1, "substitution produces one term");
    assert!(condition_results.is_empty());
    assert!(offset_results.is_empty());
    term_results.pop().unwrap()
}

/// Whether two terms have the same canonical form. Two forms of one value
/// compare equal exactly when their [`canonical_term`] forms are
/// identical. Load-free terms are fixed points of the canonical form, so
/// they compare by identity without a canonicalization walk. Both
/// canonicalization stages are bounded by explicit term size.
pub(crate) fn terms_have_same_canonical_form(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
) -> bool {
    if left == right {
        return true;
    }
    // A registered name and its exact descriptor are one occurrence even
    // when canonicalizing the descriptor would resolve a stored value.
    if let (Some(left), Some(right)) = (viewed_as_memory_load(left), viewed_as_memory_load(right))
        && left == right
    {
        return true;
    }
    if !term_mentions_a_memory_load(left) && !term_mentions_a_memory_load(right) {
        return false;
    }
    canonical_term(left) == canonical_term(right)
}

/// Whether two pointer offsets have the same canonical form; the offset
/// analogue of [`terms_have_same_canonical_form`].
pub(crate) fn offsets_have_same_canonical_form(
    left: &AddressOffset,
    right: &AddressOffset,
) -> bool {
    if left == right {
        return true;
    }
    if !offset_mentions_a_memory_load(left) && !offset_mentions_a_memory_load(right) {
        return false;
    }
    canonical_offset_term(left) == canonical_offset_term(right)
}

/// Whether a term contains any load atom the canonical form could rewrite.
/// Load-free terms are fixed points of [`canonical_term`], which the
/// comparators use to answer load-free mismatches without a walk.
pub(in crate::kernel) fn operand_mentions_a_memory_load(
    operand: crate::kernel::MachineOperandView<'_>,
) -> bool {
    use crate::kernel::MachineOperandView as V;
    let V::Shared(root) = operand else {
        let V::Old(term) = operand else {
            unreachable!()
        };
        return term_mentions_a_memory_load(term);
    };
    if operand.read().is_some() {
        return true;
    }
    if matches!(root.node(), KernelTermNode::FloatConvert { .. }) {
        return common_float_conversion_mentions_load(root);
    }
    if let Some(leaf) = root.machine_conversion_leaf() {
        return term_mentions_a_memory_load(leaf);
    }
    let checkpoint = || !crate::instrumentation::deadline_exceeded_with_work(1);
    let Some(reads) = crate::kernel::shared_machine_read_leaves(root, checkpoint) else {
        return true;
    };
    if !reads.is_empty() {
        return true;
    }
    let Some(leaves) = crate::kernel::shared_machine_conversion_leaves(root, checkpoint) else {
        return true;
    };
    leaves.iter().any(|(_, leaf)| {
        matches!(
            leaf.node(),
            KernelTermNode::Fold(_) | KernelTermNode::Match(_)
        ) || if matches!(leaf.node(), KernelTermNode::FloatConvert { .. }) {
            common_float_conversion_mentions_load(leaf)
        } else {
            term_mentions_a_memory_load(leaf.machine_conversion_leaf().expect("conversion leaf"))
        }
    })
}

fn common_float_conversion_mentions_load(root: &KernelTerm) -> bool {
    let mut pending = vec![root];
    let mut seen = std::collections::HashSet::new();
    while let Some(term) = pending.pop() {
        if !seen.insert(term.id()) {
            continue;
        }
        crate::instrumentation::record_deterministic_work(1);
        match term.node() {
            KernelTermNode::FloatRead(_)
            | KernelTermNode::MemoryLoad { .. }
            | KernelTermNode::FloatCall(_) => return true,
            KernelTermNode::ImportedScalar(input) => {
                if term_mentions_a_memory_load(input.value()) {
                    return true;
                }
            }
            KernelTermNode::FloatLiteral { .. }
            | KernelTermNode::MachineLiteral(_)
            | KernelTermNode::Variable(_) => {}
            KernelTermNode::FloatConvert { .. }
            | KernelTermNode::FloatNegate { .. }
            | KernelTermNode::FloatBinary { .. } => pending.extend(term.children()),
            _ => {
                if let Some(view) = crate::kernel::FloatOperandView::from_shared(term) {
                    if term_mentions_a_memory_load(view.old_form().expect("native float atom")) {
                        return true;
                    }
                } else if operand_mentions_a_memory_load(crate::kernel::MachineOperandView::Shared(
                    term,
                )) {
                    return true;
                }
            }
        }
    }
    false
}

pub(in crate::kernel) fn term_mentions_a_memory_load(term: &OldMachineTerm) -> bool {
    match term {
        OldMachineTerm::ThreadHandle(_) => false,
        bits32_constant!(_)
        | OldMachineTerm::Variable(_)
        | int64_constant!(_)
        | uint64_constant!(_)
        | native_constant!(_, _) => false,
        OldMachineTerm::MemoryLoad(_, _, _) => true,
        OldMachineTerm::IntegerAddress(pointer, _) => pointer
            .offset
            .any_scaled_operand(|value| operand_mentions_a_memory_load(value.operand_view())),
        OldMachineTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            condition_mentions_a_memory_load(condition)
                || term_mentions_a_memory_load(then_term)
                || term_mentions_a_memory_load(else_term)
        }
        // The structural stage canonicalizes inside fold bodies even though
        // name substitution stops at the binder, so a fold may still change
        // under the canonical form.
        OldMachineTerm::RangeFold { .. } => true,
        OldMachineTerm::PureFunctionApplication { name: _, arguments } => {
            arguments.iter().any(term_mentions_a_memory_load)
        }
        OldMachineTerm::ClickFunctionApplication { .. }
        | OldMachineTerm::PureApplicationCount(_) => true,
        OldMachineTerm::AlgebraicMatch { arms, .. } => arms
            .iter()
            .any(|arm| term_mentions_a_memory_load(&arm.body)),
        OldMachineTerm::IntegerToMachine { .. } => true,
        OldMachineTerm::BoolCast { value, .. } => condition_mentions_a_memory_load(value),
        term => {
            if let Some((_, left, right)) = term.as_binary() {
                term_mentions_a_memory_load(left) || term_mentions_a_memory_load(right)
            } else {
                let (_, value) = term
                    .as_unary()
                    .expect("every other term is binary or unary");
                term_mentions_a_memory_load(value)
            }
        }
    }
}

fn condition_mentions_a_memory_load(condition: &OldConditionTerm) -> bool {
    match condition {
        OldConditionTerm::PointerEqual(left, right) => {
            left.pointers().chain(right.pointers()).any(|p| {
                p.offset.any_scaled_operand(|value| {
                    operand_mentions_a_memory_load(value.operand_view())
                })
            }) || left
                .metadata_terms()
                .chain(right.metadata_terms())
                .any(term_mentions_a_memory_load)
        }

        // Until memory canonicalization traverses ADTs, conservatively disable
        // the memory-free fast path for this logical condition.
        OldConditionTerm::AlgebraicEqual(_, _) => true,
        OldConditionTerm::Constant(_) | OldConditionTerm::Variable(_) => false,
        crate::kernel::binary_bitvector_condition!(left, right) => {
            term_mentions_a_memory_load(left) || term_mentions_a_memory_load(right)
        }
        OldConditionTerm::Float32(float_condition) | OldConditionTerm::Float64(float_condition) => {
            let mut mentions = false;
            float_condition.for_each_bitvector_term(|term| {
                mentions |= term_mentions_a_memory_load(term);
            });
            mentions
        }
        OldConditionTerm::AddressOffsetEqual(left, right) => {
            offset_mentions_a_memory_load(left) || offset_mentions_a_memory_load(right)
        }
        OldConditionTerm::AddressEqual(left, right) => {
            offset_mentions_a_memory_load(&left.offset)
                || offset_mentions_a_memory_load(&right.offset)
        }
        crate::kernel::integer_comparison_condition!(_, _) => false,
        OldConditionTerm::BoolApplication(_) => true,
        OldConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => [condition, then_condition, else_condition]
            .into_iter()
            .any(|condition| condition_mentions_a_memory_load(condition)),
        OldConditionTerm::BoolEqual(left, right) => {
            condition_mentions_a_memory_load(left) || condition_mentions_a_memory_load(right)
        }
    }
}

fn offset_mentions_a_memory_load(offset: &AddressOffset) -> bool {
    offset.any_scaled_operand(|value| operand_mentions_a_memory_load(value.operand_view()))
}

/// The load variable representing one load identity: the pair of a memory
/// state (by content) and a loaded pointer. Hashing that identity into a
/// reserved id space picks where the search for its id starts, and the
/// thread-local registry assigns the first slot that holds this identity or
/// nothing, so distinct identities get distinct ids by construction. Every
/// pass — contract-grant lowering, requirement evaluation, and body
/// execution — therefore writes the same load with the same variable, and
/// the id is the hash itself unless another load already took that slot in
/// this session. The registry is never cleared within a session, and
/// exhausting its capacity is a loud failure rather than a silent reset.
/// The variable naming a `kind` load of `pointer` in `memory`. The version
/// walk that picks the state it is named at is as wide as the widest
/// access recorded at the address, and never narrower than the read.
pub(crate) fn load_variable_for_cell(
    memory: &SharedMemory,
    pointer: &Address,
    kind: LoadKind,
) -> Variable {
    load_variable_for_cell_with_origin(
        memory,
        pointer,
        kind,
        load_term_access_width(memory, pointer, kind),
        memory,
    )
}

/// Mint the load identity for exactly this state and pointer.
///
/// Fold substitution uses this after rewriting a registered load's address.
/// The ordinary cell helper first projects a state through memory
/// provenance, which is correct for a newly observed load but would change
/// the state identity carried by an existing defining fact.  Keeping this
/// narrow helper separate makes the selected state explicit and avoids
/// traversing or rewriting any of its contents.
pub(crate) fn load_variable_for_exact_cell(
    memory: &SharedMemory,
    pointer: &Address,
    kind: LoadKind,
    bytes: u32,
) -> Variable {
    mint_load_variable_identity(memory, pointer, kind, memory, bytes)
}

/// The variable naming a `kind` load of `pointer` in `memory`.
///
/// `bytes` is the access width the version walk uses, and it decides how far
/// back the walk may go: a store lands on this load exactly when it writes
/// one of these bytes. It is never narrower than the read itself.
pub(crate) fn load_variable_for_cell_with_origin(
    memory: &SharedMemory,
    pointer: &Address,
    kind: LoadKind,
    bytes: u32,
    origin: &SharedMemory,
) -> Variable {
    let bytes = bytes.max(kind.byte_width());
    // Derive the variable from the cell's version when one is recorded:
    // states that differ only by effects provably disjoint from this
    // cell then share the variable, so bookkeeping drift and unrelated
    // stores do not mint new identities for one load.
    let version = crate::kernel::resource_tracker::last_same_version_point(
        crate::kernel::resource_tracker::TrackedResource::Cell {
            pointer,
            bytes: bytes.into(),
        },
        &crate::kernel::resource_tracker::ProgramPoint::unplaced(memory),
    )
    .map(|point| point.shared_memory().clone());
    let memory = version.as_ref().unwrap_or(memory);
    #[cfg(test)]
    duplicate_read_names::observe(memory, pointer, kind);
    mint_load_variable_identity(memory, pointer, kind, origin, bytes)
}

/// A test-only count of the facts that still hold a load variable when they
/// enter a `PureFactContext`, by kind of fact, with one example each.
/// Defining facts are left out: they are what minting a variable adds. The
/// counts are the work list for removing load variables from facts
/// (`docs/internals/canonicalization.md`, "Transitional load variables and
/// shared reads").
#[cfg(test)]
pub(crate) mod load_variable_fact_census {
    use super::*;

    thread_local! {
        static COUNTS: std::cell::RefCell<
            Option<std::collections::BTreeMap<String, (usize, String)>>,
        > = const { std::cell::RefCell::new(None) };
    }

    /// Runs `run` and returns, per kind of fact, how many admitted facts held
    /// a load variable and one example.
    pub(crate) fn capture(
        run: impl FnOnce(),
    ) -> std::collections::BTreeMap<String, (usize, String)> {
        let previous = COUNTS.with(|counts| counts.replace(Some(Default::default())));
        run();
        COUNTS
            .with(|counts| counts.replace(previous))
            .unwrap_or_default()
    }

    pub(crate) fn active() -> bool {
        COUNTS.with(|counts| counts.borrow().is_some())
    }

    /// The census sees a native comparison that holds a load variable, so a
    /// report of none is not a census that misses them. An Integer
    /// comparison stated over the same variable does not hold it: its
    /// shared operand imports the variable as the read it names, and only
    /// the producer's retained native payload still spells the variable.
    #[test]
    fn counts_native_comparisons_holding_a_load_variable() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::intern_memory(SymbolicMemory::new().with_block("cell", 4));
        let pointer = Address::new(
            AddressBase::Concrete("cell".into()),
            AddressOffset::constant(0),
        );
        let variable = load_variable_for_cell(&memory, &pointer, LoadKind::Int32);
        let native = Proposition::condition_is(
            OldConditionTerm::signed_less_than(
                OldMachineTerm::Variable(variable),
                OldMachineTerm::constant(5),
            ),
            true,
        );
        let integer = Proposition::condition_is(
            OldConditionTerm::integer_less_than(
                crate::kernel::IntegerTerm::from_machine(
                    MachineIntegerType::Int32,
                    OldMachineTerm::Variable(variable),
                )
                .unwrap(),
                crate::kernel::IntegerTerm::constant(5.into()),
            ),
            true,
        );
        let counts = capture(|| {
            let _ = PureFactContext::new()
                .assume_proposition(native)
                .assume_proposition(integer);
        });
        assert!(
            counts.contains_key("condition: native comparison"),
            "{counts:?}"
        );
        assert!(
            !counts.contains_key("condition: integer comparison"),
            "{counts:?}"
        );
    }

    pub(crate) fn observe(proposition: &Proposition) {
        if !active() || is_load_variable_defining_fact(proposition) {
            return;
        }
        let mut variables = std::collections::BTreeSet::new();
        crate::kernel::reasoning::variable_collection::collect_proposition_variables_for_load_presence(
            proposition,
            &mut variables,
        );
        if !variables.iter().any(is_load_variable) {
            return;
        }
        let kind = match proposition {
            Proposition::ConditionIs(condition, _) => match condition.old_form() {
                crate::kernel::integer_comparison_condition!(_, _) => {
                    "condition: integer comparison".to_string()
                }
                OldConditionTerm::Compare { .. } => "condition: native comparison".to_string(),
                OldConditionTerm::Overflows { .. } => "condition: overflow".to_string(),
                condition => {
                    let shown = format!("{condition:?}");
                    let name = shown
                        .split(|c: char| !c.is_alphanumeric())
                        .next()
                        .unwrap_or("")
                        .to_string();
                    format!("condition: {name}")
                }
            },
            proposition => {
                let shown = format!("{proposition:?}");
                shown
                    .split(|c: char| !c.is_alphanumeric())
                    .next()
                    .unwrap_or("")
                    .to_string()
            }
        };
        COUNTS.with(|counts| {
            if let Some(counts) = counts.borrow_mut().as_mut() {
                let entry = counts.entry(kind).or_insert_with(|| {
                    let shown = format!("{proposition:?}");
                    (0, shown[..shown.len().min(300)].to_string())
                });
                entry.0 += 1;
            }
        });
    }
}

/// A test-only audit for the program-point migration (`roadmap/smart-tactics.md`,
/// "Program-point memory migration"): while [`mixed_read_names::capture`]
/// runs, each integer read the equality graph registers is filed by its
/// memory state, address and kind, and a cell at one memory state that is
/// named both by a selected program point and by its memory is reported.
/// Those two terms denote one value, but no rule relates them, so a fact
/// stated with one does not prove a goal stated with the other. Each report
/// names the source line that built the memory-named read, as the read
/// constructor `OldMachineTerm::read_named` records it through
/// `#[track_caller]` (the wrappers that build reads pass their callers on),
/// which is the producer still to migrate. Two different points with equal memory are not
/// reported: that is the precision the migration adds.
#[cfg(test)]
pub(crate) mod mixed_read_names {
    use super::*;

    type CellKey = ((u32, u32), Address, LoadKind);

    #[derive(Default)]
    struct Census {
        point_named: std::collections::HashSet<CellKey>,
        memory_named: std::collections::HashMap<CellKey, String>,
        reported: std::collections::HashSet<CellKey>,
        producers: std::collections::HashMap<CellKey, &'static std::panic::Location<'static>>,
        reports: Vec<String>,
    }

    thread_local! {
        static CENSUS: std::cell::RefCell<Option<Census>> = const { std::cell::RefCell::new(None) };
    }

    /// Runs `run` and returns one line per cell named both ways.
    pub(crate) fn capture(run: impl FnOnce()) -> Vec<String> {
        let previous = CENSUS.with(|census| census.replace(Some(Census::default())));
        run();
        CENSUS
            .with(|census| census.replace(previous))
            .map(|census| census.reports)
            .unwrap_or_default()
    }

    /// Files the source line that built a memory-named read, from the read
    /// constructor (`OldMachineTerm::read_named`). The first producer of a read
    /// is kept.
    pub(crate) fn record_producer(
        point: &ProgramPoint,
        pointer: &Address,
        kind: LoadKind,
        producer: &'static std::panic::Location<'static>,
    ) {
        if point.read_version_id().is_some() {
            return;
        }
        CENSUS.with(|census| {
            if let Some(census) = census.borrow_mut().as_mut() {
                census
                    .producers
                    .entry((point.shared_memory().arena_id(), pointer.clone(), kind))
                    .or_insert(producer);
            }
        });
    }

    pub(crate) fn observe(point: &ProgramPoint, pointer: &Address, kind: LoadKind) {
        CENSUS.with(|census| {
            let mut census = census.borrow_mut();
            let Some(census) = census.as_mut() else {
                return;
            };
            let key = (point.shared_memory().arena_id(), pointer.clone(), kind);
            if point.read_version_id().is_some() {
                census.point_named.insert(key.clone());
            } else {
                let origin = census
                    .producers
                    .get(&key)
                    .map_or_else(|| "unrecorded".to_string(), |origin| {
                        format!("{}:{}", origin.file(), origin.line())
                    });
                census.memory_named.entry(key.clone()).or_insert(origin);
            }
            if census.point_named.contains(&key)
                && let Some(origin) = census.memory_named.get(&key)
                && census.reported.insert(key.clone())
            {
                let report = format!(
                    "{kind:?} read of {pointer:?} named by a point and by its memory, built at {origin}"
                );
                census.reports.push(report);
            }
        });
    }
}

/// A test-only audit of one read, one name (`docs/internals/raise-lower-principle.md`):
/// while [`duplicate_read_names::capture`] runs, each load named at a new
/// version of its cell is compared with the versions earlier loads of that
/// cell were named at in the same verification, and a pair the kernel's
/// assumption-free load equality proves equal is reported. Two writes of one
/// stored value are two versions, which the read-over-write authority
/// relates, so they are not reported.
#[cfg(test)]
pub(crate) mod duplicate_read_names {
    use super::*;

    #[derive(Default)]
    struct Census {
        seen: std::collections::HashMap<(u64, Address, LoadKind), Vec<SharedMemory>>,
        reports: Vec<String>,
        comparing: bool,
    }

    thread_local! {
        static CENSUS: std::cell::RefCell<Option<Census>> = const { std::cell::RefCell::new(None) };
    }

    /// Runs `run` and returns one line per load that was given a second name
    /// for a version its cell was already named at.
    pub(crate) fn capture(run: impl FnOnce()) -> Vec<String> {
        CENSUS.with(|census| census.replace(Some(Census::default())));
        run();
        CENSUS
            .with(|census| census.take())
            .map(|census| census.reports)
            .unwrap_or_default()
    }

    pub(super) fn observe(version: &SharedMemory, pointer: &Address, kind: LoadKind) {
        let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
        let Some(earlier) = CENSUS.with(|census| {
            let mut census = census.borrow_mut();
            let census = census.as_mut().filter(|census| !census.comparing)?;
            let seen = census
                .seen
                .entry((epoch, pointer.clone(), kind))
                .or_default();
            if seen.contains(version) {
                return None;
            }
            let earlier = seen.clone();
            seen.push(version.clone());
            census.comparing = true;
            Some(earlier)
        }) else {
            return;
        };
        let stored = version.memory().known_value(pointer);
        let read = |memory: &SharedMemory| {
            crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(memory),
                pointer.clone(),
                kind,
            )
        };
        let empty = PureFactContext::new();
        let duplicate = earlier.iter().any(|earlier| {
            !(stored.is_some() && earlier.memory().known_value(pointer) == stored)
                && crate::kernel::memory_history::checked_atomic_load_equality(
                    &read(earlier),
                    &read(version),
                    &empty,
                )
        });
        CENSUS.with(|census| {
            if let Some(census) = census.borrow_mut().as_mut() {
                census.comparing = false;
                if duplicate {
                    census.reports.push(format!("{pointer:?} {kind:?}"));
                }
            }
        });
    }
}

/// The kind is part of the identity: two reads of one address in one
/// state that differ in kind are two values. The hash leaves it out, so a
/// load keeps the slot it had when every load of its address agreed on one
/// kind, and a second kind probes past it like any other collision.
///
/// Each read is its own load: a 32-bit read of either signedness has a name
/// of its own, and the two reads of one cell are related by σ (R-mem, in
/// the equality graph's cell reads; `design/machine-integers.md`, G5).
fn mint_load_variable_identity(
    memory: &SharedMemory,
    pointer: &Address,
    kind: LoadKind,
    origin: &SharedMemory,
    bytes: u32,
) -> Variable {
    mint_load_variable_at(
        &ProgramPoint::unplaced(memory),
        pointer,
        kind,
        &ProgramPoint::unplaced(origin),
        bytes,
    )
}

fn mint_load_variable_at(
    point: &ProgramPoint,
    pointer: &Address,
    kind: LoadKind,
    origin: &ProgramPoint,
    bytes: u32,
) -> Variable {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    point.hash(&mut hasher);
    pointer.hash(&mut hasher);
    let hash = hasher.finish();
    let range = load_variable_range();
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        let mut registry = registry.borrow_mut();
        // The hash picks where the search for this load's id starts, not the
        // id itself. A slot is this load's exactly when the registry holds
        // this load there; a slot holding another load is skipped, so two
        // distinct loads can never share an id however their hashes compare.
        // Nothing is removed within a session, so a lookup that reaches an
        // empty slot has passed every slot this load could already hold.
        //
        // Termination: the capacity check below keeps the registry strictly
        // smaller than the id range, so an empty slot always exists; the
        // expected probe length at the real capacity and range is one.
        let mut slot = hash % range;
        loop {
            let variable = Variable(LOAD_VARIABLE_BASE + slot);
            match registry.get_mut(&variable) {
                Some(RegisteredLoad {
                    point: known_point,
                    pointer: known_pointer,
                    kind: known_kind,
                    observation,
                    ..
                }) if known_point == point && known_pointer == pointer && *known_kind == kind => {
                    read_observations::refresh(*observation, origin, bytes);
                    return variable;
                }
                Some(_) => {
                    crate::instrumentation::record_deterministic_work(1);
                    slot = (slot + 1) % range;
                }
                None => {
                    assert!(
                        (registry.len() as u64) < range.saturating_sub(1)
                            && registry.len() < load_variable_registry_capacity(),
                        "load-variable registry capacity exhausted: this verification session \
                         minted {} distinct load identities; the registry never forgets an \
                         entry because it is what keeps two loads from sharing an id",
                        registry.len()
                    );
                    registry.insert(
                        variable,
                        RegisteredLoad {
                            address: crate::kernel::KernelTerm::scalar_read_address(pointer),
                            terms: Default::default(),
                            point: point.clone(),
                            pointer: pointer.clone(),
                            kind,
                            observation: {
                                let id = read_observations::record_at(
                                    point, pointer, kind, origin, bytes,
                                );
                                read_observations::select(id);
                                id
                            },
                        },
                    );
                    return variable;
                }
            }
        }
    })
}

// Keep the actual producer expression, including its live state and
// pointer. Load identities can recur in disconnected model arms; their first
// registered origin is not necessarily in the current arm's memory history.
fn record_wide_load_observation(term: &OldMachineTerm, variable: Variable) {
    let OldMachineTerm::MemoryLoad(memory, pointer, LoadKind::Bits64) = term else {
        return;
    };
    if registered_load_kind_for_variable(&variable) != Some(LoadKind::Bits64) {
        return;
    }
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    crate::instrumentation::record_deterministic_work(1);
    let point = if has_selected_read_point(memory) {
        memory.point().clone()
    } else {
        ProgramPoint::unplaced(memory.shared_memory())
    };
    WIDE_LOAD_OBSERVATIONS.with(|registry| {
        let mut registry = registry.borrow_mut();
        let key = (epoch, variable);
        if registry
            .get(&key)
            .is_some_and(|(known_point, known_pointer)| {
                *known_point == point && known_pointer == pointer.as_ref()
            })
        {
            return;
        }
        crate::instrumentation::record_deterministic_work(1);
        registry.insert(key, (point, pointer.as_ref().clone()));
    });
}

// Only a typed producer records an unconditional pointer-read expression.
fn record_pointer_read_observation(value: &Address, memory: &SymbolicMemory, address: &Address) {
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    crate::instrumentation::record_deterministic_work(1);
    let memory = crate::kernel::intern_memory_ref(memory);
    POINTER_READ_OBSERVATIONS.with(|registry| {
        let mut registry = registry.borrow_mut();
        let key = (epoch, value.clone());
        if registry
            .get(&key)
            .is_some_and(|(known_memory, known_address)| {
                known_memory == &memory && known_address == address
            })
        {
            return;
        }
        crate::instrumentation::record_deterministic_work(1);
        registry.insert(key, (memory, address.clone()));
    });
}

pub(crate) fn latest_pointer_read_observation(value: &Address) -> Option<(SharedMemory, Address)> {
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    crate::instrumentation::record_deterministic_work(1);
    POINTER_READ_OBSERVATIONS
        .with(|registry| registry.borrow().get(&(epoch, value.clone())).cloned())
}

pub(crate) fn latest_wide_load_observation(variable: &Variable) -> Option<OldMachineTerm> {
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    crate::instrumentation::record_deterministic_work(1);
    WIDE_LOAD_OBSERVATIONS.with(|registry| {
        registry
            .borrow()
            .get(&(epoch, *variable))
            .map(|(point, pointer)| {
                crate::kernel::OldMachineTerm::read_named(
                    point.clone(),
                    pointer.clone(),
                    LoadKind::Bits64,
                )
            })
    })
}

/// The equality graph can use an indexed version of an exact read without
/// changing the retained proof term. If only the selected point is certified,
/// that point supplies the comparison identity.
pub(crate) fn comparison_identity_of_exact_read(
    point: &ProgramPoint,
    pointer: &Address,
    kind: LoadKind,
) -> OldMachineTerm {
    match point
        .indexed_integer_version(pointer, kind)
        .or_else(|| point.call_output_integer_version(pointer, kind))
        .or_else(|| point.entry_integer_version(pointer, kind))
        .or_else(|| point.has_certified_read_view().then(|| point.clone()))
    {
        Some(version) => crate::kernel::OldMachineTerm::read_named(version, pointer.clone(), kind),
        None => canonical_form_of_load_at(point, pointer.clone(), kind),
    }
}

/// Compatibility adapter for the existing selected-version read policy.
/// Exact construction, comparison identity selection, and observation
/// publication are separate operations. Until exact-state lowering migrates,
/// callers still retain the selected identity as their read term.
pub(in crate::kernel) fn canonical_scalar_read(bits: &OldMachineTerm) -> OldMachineTerm {
    if matches!(bits, OldMachineTerm::MemoryLoad(point, _, _) if point.read_version_id().is_some())
    {
        return bits.clone();
    }
    let Some(descriptor) = ScalarReadDescriptor::from_term(bits) else {
        return bits.clone();
    };
    if let Some((identity, typed)) =
        SCALAR_READ_IDENTITY_CACHE.with(|cache| cache.borrow().get(bits).cloned())
    {
        let OldMachineTerm::MemoryLoad(memory, pointer, kind) = identity.as_legacy_read() else {
            unreachable!("cached scalar read identity");
        };
        // Preserve master's intrinsic byte/halfword width on cache hits.
        if let Some(bytes) = descriptor.narrow_bytes() {
            scalar_reads::record_comparison_observation(&identity, descriptor.point(), Some(bytes));
            read_observations::produced(identity.as_legacy_read(), bits);
            return identity.into_legacy_read();
        }
        // A conservative, untyped selection is not an observed access width.
        // Once a producer supplies the width, select its version with that
        // width instead of treating the earlier guess as an eight-byte load.
        if typed
            || existing_read_access_width(memory.shared_memory(), pointer, *kind).is_some()
            || recorded_load_access_width(descriptor.memory(), descriptor.address()).is_none()
        {
            read_observations::produced(identity.as_legacy_read(), bits);
            return identity.into_legacy_read();
        }
    }
    let (identity, observed_bytes) = scalar_reads::select_comparison_identity(descriptor);
    scalar_reads::record_comparison_observation(&identity, descriptor.point(), observed_bytes);
    read_observations::produced(identity.as_legacy_read(), bits);
    SCALAR_READ_IDENTITY_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        if cache.len() >= 100_000 {
            cache.clear();
        }
        cache.insert(bits.clone(), (identity.clone(), observed_bytes.is_some()));
    });
    identity.into_legacy_read()
}

pub(crate) fn latest_scalar_read_observation(read: &OldMachineTerm) -> Option<OldMachineTerm> {
    read_observations::latest(read)
}

/// Returns the load variable for a load term's history-stable form.
/// The term is first canonicalized without assumptions, resolving cached
/// cells and state representation differences. The same cell loaded at
/// different symbolic states therefore shares one load variable whenever
/// the difference is representational. The second return value is the form
/// retained in the producer binding, exactly as registered under the name.
pub(crate) fn load_variable_for_term(bits: &OldMachineTerm) -> Option<(Variable, OldMachineTerm)> {
    let OldMachineTerm::MemoryLoad(..) = bits else {
        return None;
    };
    // Naming is deterministic per term, and callers ask per fact atom per
    // comparison; the version walk and canonicalization behind a cold call
    // are not free, so cache by term. Term hashing is cheap: embedded
    // states hash by interned identity.
    if let Some(hit) = LOAD_VARIABLE_CACHE.with(|cache| cache.borrow().get(bits).cloned()) {
        record_wide_load_observation(bits, hit.0);
        return Some(hit);
    }
    crate::instrumentation::record_deterministic_work(1);
    let (variable, _) = load_variable_for_term_uncached(bits)?;
    // Naming may cross a cache-only state or project away unrelated cells.
    // Its defining equation must retain the exact structural read registered
    // under this name, rather than a second representation of that read.
    // This does not resolve the read to a stored value or consult facts.
    let defining_load = registered_load_term_for_variable(&variable)
        .expect("a minted load variable retains its structural read");
    let computed = (variable, defining_load);
    record_wide_load_observation(bits, computed.0);
    LOAD_VARIABLE_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        if cache.len() >= 100_000 {
            cache.clear();
        }
        cache.insert(bits.clone(), computed.clone());
    });
    Some(computed)
}

fn has_selected_read_point(point: &ProgramPoint) -> bool {
    point.read_version_id().is_some() && point.has_certified_read_view()
}

fn load_variable_for_term_uncached(bits: &OldMachineTerm) -> Option<(Variable, OldMachineTerm)> {
    if let OldMachineTerm::MemoryLoad(point, pointer, kind) = bits
        && has_selected_read_point(point)
    {
        let bytes =
            observed_scalar_read_width(point, pointer, *kind).unwrap_or_else(|| kind.byte_width());
        let variable = mint_load_variable_at(point, pointer, *kind, point, bytes);
        return Some((variable, bits.clone()));
    }
    let canonical = crate::kernel::memory_history::canonicalize_atomic_loads(bits);
    if let OldMachineTerm::MemoryLoad(memory, pointer, kind) = &canonical {
        let OldMachineTerm::MemoryLoad(origin, _, _) = bits else {
            unreachable!("the pattern above matched a memory load");
        };
        // A cell of the canonical state holding this cell's own read (a
        // materialization) names that read: the load is that read. The raw
        // state can lack the cell while its unchanged-bytes source, which
        // the canonical state is projected from, holds it, so the cell is
        // asked of the canonical state. Only a read of the same address
        // and kind qualifies, so no stored value replaces a read.
        if let Some(OldMachineTerm::Variable(held)) = memory
            .memory()
            .known_value(pointer)
            .and_then(|value| crate::kernel::spec::program_value_bitvector_term(&value))
            && is_load_variable(&held)
            && registered_load_for_variable(&held).is_some_and(|(_, at)| at == **pointer)
            && registered_load_kind_for_variable(&held) == Some(*kind)
        {
            return Some((held, bits.clone()));
        }
        return Some((
            load_variable_for_cell_with_origin(
                memory.shared_memory(),
                pointer,
                *kind,
                // Either state's recorded entry is this same load's own
                // width, so the first one found is the answer. Taking the
                // larger would let a miss on one side widen a width the
                // other side knows exactly.
                recorded_load_access_width(origin.shared_memory(), pointer)
                    .or_else(|| recorded_load_access_width(memory.shared_memory(), pointer))
                    .or_else(|| {
                        existing_read_access_width(origin.shared_memory(), pointer, *kind).max(
                            existing_read_access_width(memory.shared_memory(), pointer, *kind),
                        )
                    })
                    .unwrap_or_else(|| kind.unrecorded_access_byte_width()),
                origin.shared_memory(),
            ),
            canonical.clone(),
        ));
    }
    // The canonical form resolved this load through the state's own
    // materialized cell, and the cell holds a load variable: that variable
    // already names this value, so it is this load's name too. Falling
    // through would mint a second identity for one value whenever the cell's
    // state cannot be reached by the assumption-free version walk — a cell
    // retained across a call havoc by a `separate` premise, for instance,
    // whose reload would otherwise lose every fact stated about it. The
    // resolution is structural and assumption-free, and the havoc's retention
    // decision is re-checked during certification, so this adds no alias
    // approximation of its own.
    if let OldMachineTerm::Variable(variable) = &canonical
        && let OldMachineTerm::MemoryLoad(_, _, kind) = bits
        && registered_load_kind_for_variable(variable) == Some(*kind)
    {
        return Some((*variable, bits.clone()));
    }
    let OldMachineTerm::MemoryLoad(memory, pointer, kind) = bits else {
        unreachable!("the pattern above matched a memory load");
    };
    Some((
        load_variable_for_cell(memory.shared_memory(), pointer, *kind),
        bits.clone(),
    ))
}

/// Binds a load term to its load variable and records the defining
/// equation in the path's fact stream. The defining equation is
/// kernel-certified by construction: the load variable represents this
/// load. It must not demand a checkable assumption derivation
/// downstream.
#[cfg(test)]
fn mint_load_variable(
    bits: &OldMachineTerm,
    facts: &mut ExecutionFacts,
    _assumptions: &PureFactContext,
    source: Option<&LoadSourceId>,
) -> Option<Variable> {
    let (fresh, load) = load_variable_for_term(bits)?;
    record_load_variable_defining_fact_with_source(fresh, load, facts, source);
    Some(fresh)
}

/// Records a load variable's exact defining fact in a fact
/// stream, deduplicated by proposition. The equation is kernel-certified by
/// construction: the load variable represents this load. It must not demand
/// a checkable assumption derivation downstream.
#[cfg(test)]
pub(crate) fn record_load_variable_defining_fact(
    variable: Variable,
    load: OldMachineTerm,
    facts: &mut ExecutionFacts,
) {
    record_load_variable_defining_fact_with_source(variable, load, facts, None);
}

#[cfg(test)]
pub(crate) fn record_load_variable_defining_fact_with_source(
    variable: Variable,
    load: OldMachineTerm,
    facts: &mut ExecutionFacts,
    source: Option<&LoadSourceId>,
) {
    record_load_variable_defining_fact_with_source_and_pointer(variable, load, facts, source, None);
}

fn record_load_variable_defining_fact_with_source_and_pointer(
    variable: Variable,
    load: OldMachineTerm,
    facts: &mut ExecutionFacts,
    source: Option<&LoadSourceId>,
    typed_pointer_value: Option<&Address>,
) {
    let OldMachineTerm::MemoryLoad(memory, pointer, kind) = &load else {
        // `load_variable_for_term` currently returns a memory load's
        // canonical operand.  Keep this guard explicit so future changes
        // cannot attach producer metadata to an unrelated term.
        return;
    };
    let defining_load = load.clone();
    let defining_proposition = Proposition::condition_is(
        OldConditionTerm::Compare {
            // The raw-load form historically used a 32-bit equality with
            // a width-check exception. Registered read terms use the actual
            // carrier width: a narrow read is a value of its own format.
            format: match kind {
                LoadKind::Int8 => MachineIntegerType::Int8,
                LoadKind::UInt8 => MachineIntegerType::UInt8,
                LoadKind::Int16 => MachineIntegerType::Int16,
                LoadKind::UInt16 => MachineIntegerType::UInt16,
                LoadKind::Bits64 | LoadKind::Algebraic(_) | LoadKind::Float64 => {
                    MachineIntegerType::Int64
                }
                LoadKind::Int128 => MachineIntegerType::Int128,
                LoadKind::UInt128 => MachineIntegerType::UInt128,
                LoadKind::Int32 | LoadKind::UInt32 | LoadKind::Float32 => MachineIntegerType::Int32,
                LoadKind::SliceCount => MachineIntegerType::UInt64,
            },
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::Variable(variable)),
            // Cite the same read as logical lowering. A selected point already
            // supplies the read's name.
            right: Box::new(if has_selected_read_point(memory) {
                load.clone()
            } else {
                canonical_form_of_load_at(memory, pointer.as_ref().clone(), *kind)
            }),
        },
        true,
    );
    let binding = GeneratedLoadBinding::Exact {
        variable,
        retained_state: MemoryStateIdentity::of(memory.memory()),
        pointer: pointer.as_ref().clone(),
        load: defining_load,
        typed_pointer_value: typed_pointer_value.cloned(),
        observed_pointer_read: None,
    };
    let event =
        source.and_then(|source| GeneratedLoadSourceEvent::new(source.clone(), binding.clone()));
    let existing_index = facts
        .iter()
        .position(|fact| fact.proposition() == &defining_proposition);
    if let Some(index) = existing_index {
        let existing = facts.get_mut(index);
        if existing.generated_load_binding.is_none() || typed_pointer_value.is_some() {
            existing.generated_load_binding = Some(Box::new(binding));
        }
        if let Some(event) = event {
            existing.generated_load_source_events.push(event);
        }
        return;
    }
    let mut defining =
        ExecutionPureFact::certified(defining_proposition).with_generated_load_binding(binding);
    if let Some(event) = event {
        defining = defining.with_generated_load_source_event(event);
    }
    facts.push(defining);
}

#[cfg_attr(test, track_caller)]
pub(in crate::kernel) fn symbolic_load_value(
    memory: &SymbolicMemory,
    site: &ProgramPoint,
    pointer: &Address,
    value_type: ProgramType,
) -> Option<ProgramValue> {
    // Every C load reaches the kernel through here with its type. The
    // `MemoryLoad` term built below carries the read's kind; the address's
    // recorded width, which every read there shares, is kept beside it.
    // Recording it here is what lets an `int32` load keep being separated
    // from a store one element away.
    record_load_access_width(memory, pointer, value_type.byte_width());
    symbolic_load_value_unrecorded(memory, site, pointer, value_type)
}

/// [`symbolic_load_value`] without recording the access width, for a caller
/// that has already said how wide the access is.
#[cfg_attr(test, track_caller)]
pub(in crate::kernel) fn symbolic_load_value_unrecorded(
    memory: &SymbolicMemory,
    site: &ProgramPoint,
    pointer: &Address,
    value_type: ProgramType,
) -> Option<ProgramValue> {
    match value_type {
        ProgramType::Int128 | ProgramType::UInt128 => memory.symbolic_wide_integer_load(
            pointer,
            MachineIntegerType::from_program_type(value_type)?,
        ),
        // An abstract value is the load of its type at the address.
        ProgramType::Parameter(parameter) => Some(AlgebraicTermNode::parameter_load(
            crate::kernel::intern_memory(memory.clone()),
            site,
            pointer.clone(),
            parameter,
        )),
        ProgramType::Void | ProgramType::VoidPointer => None,
        ProgramType::Bool => Some(ProgramValue::of_bool(OldConditionTerm::boolean_cell_read(
            ProgramPoint::read_at(&crate::kernel::intern_memory_ref(memory), site),
            pointer.clone(),
        ))),
        ProgramType::Int8 => Some(memory.symbolic_int8_load(site, pointer)),
        ProgramType::Int16 => Some(memory.symbolic_int16_load(site, pointer)),
        ProgramType::Int32 => Some(memory.symbolic_int32_load(site, pointer)),
        ProgramType::UInt8 => Some(memory.symbolic_uint8_load(site, pointer)),
        ProgramType::UInt16 => Some(memory.symbolic_uint16_load(site, pointer)),
        ProgramType::UInt32 => Some(memory.symbolic_uint32_load(site, pointer)),
        ProgramType::Int64 => Some(memory.symbolic_int64_load(site, pointer)),
        ProgramType::UInt64 => Some(memory.symbolic_uint64_load(site, pointer)),
        ProgramType::Float32 => Some(memory.symbolic_float32_load(pointer)),
        ProgramType::Float64 => Some(memory.symbolic_float64_load(pointer)),
        ProgramType::Int8Pointer | ProgramType::Int8PointerPointer => {
            Some(memory.symbolic_pointer_load(Some(site), pointer, value_type))
        }
        ProgramType::VoidPointerPointer
        | ProgramType::ParameterPointer(_)
        | ProgramType::Int16Pointer
        | ProgramType::UInt16Pointer
        | ProgramType::Int32Pointer
        | ProgramType::UInt8Pointer
        | ProgramType::UInt32Pointer
        | ProgramType::Int128Pointer
        | ProgramType::Int64Pointer
        | ProgramType::UInt128Pointer
        | ProgramType::UInt64Pointer
        | ProgramType::Int16PointerPointer
        | ProgramType::UInt16PointerPointer
        | ProgramType::Int32PointerPointer
        | ProgramType::UInt8PointerPointer
        | ProgramType::UInt32PointerPointer
        | ProgramType::Int128PointerPointer
        | ProgramType::Int64PointerPointer
        | ProgramType::UInt128PointerPointer
        | ProgramType::UInt64PointerPointer => {
            Some(memory.symbolic_pointer_load(Some(site), pointer, value_type))
        }
        ProgramType::Float32Pointer
        | ProgramType::Float64Pointer
        | ProgramType::Float32PointerPointer
        | ProgramType::Float64PointerPointer => {
            Some(memory.symbolic_pointer_load(Some(site), pointer, value_type))
        }
        ProgramType::FunctionPointer(_) => {
            Some(memory.symbolic_pointer_load(Some(site), pointer, value_type))
        }
        // Click's untyped pointer reads a pointer-width cell as any pointer
        // load does; only its type states no pointee.
        ProgramType::Pointer => Some(memory.symbolic_pointer_load(Some(site), pointer, value_type)),
        ProgramType::Int8Array(_) => None,
        ProgramType::Int32Array(_)
        | ProgramType::UInt8Array(_)
        | ProgramType::Int16Array(_)
        | ProgramType::UInt16Array(_)
        | ProgramType::UInt32Array(_)
        | ProgramType::Int128Array(_)
        | ProgramType::Int64Array(_)
        | ProgramType::UInt128Array(_)
        | ProgramType::UInt64Array(_)
        | ProgramType::Float32Array(_)
        | ProgramType::Float64Array(_) => None,
        ProgramType::PointerArray(_, _) => None,
        // A slice cell's read names its data pointer and its count, each its
        // own read of the one load (`design/rust-slice-values.md`, step
        // 2b-ii-b).
        ProgramType::SlicePointer(_) => Some(ProgramValue::Pointer(Pointer::slice_read(
            ProgramPoint::read_at(&crate::kernel::intern_memory_ref(memory), site),
            pointer,
            value_type,
        ))),
    }
}

/// The value a symbolic static-storage cell of type `program_type` at `pointer`
/// holds at function entry, where `memory` holds only the storage's block: a
/// fresh symbolic pointer named by the cell's load for an object pointer (a
/// stored pointer may point into any block), and otherwise the cell's typed
/// load, with its memory state and address retained directly.
///
/// `record_width` says the access width here, as [`symbolic_load_value`]
/// does; a caller that declared it for a whole array
/// ([`declare_symbolic_array_access_widths`]) passes `false`. An object
/// pointer's load retains the same typed definition as a logical read.
/// Reuse only a load already named at this exact state and address.
/// An optional cell-cache reconciliation must not canonicalize a cold load
/// by walking its unrelated memory history. Missing names give no evidence.
pub(in crate::kernel) fn cached_symbolic_storage_cell_value(
    memory: &SymbolicMemory,
    pointer: &Address,
    program_type: ProgramType,
) -> Option<ProgramValue> {
    let (kind, wrap): (LoadKind, fn(OldMachineTerm) -> ProgramValue) = match program_type {
        // A signed byte read is its own load.
        ProgramType::Int8 => (LoadKind::Int8, ProgramValue::Int8),
        ProgramType::Int16 => (LoadKind::Int16, ProgramValue::Int16),
        ProgramType::Int32 => (LoadKind::Int32, ProgramValue::Int32),
        ProgramType::UInt8 => (LoadKind::UInt8, ProgramValue::UInt8),
        ProgramType::UInt16 => (LoadKind::UInt16, ProgramValue::UInt16),
        ProgramType::UInt32 => (LoadKind::UInt32, ProgramValue::UInt32),
        ProgramType::Int64 => (LoadKind::Bits64, ProgramValue::Int64),
        ProgramType::UInt64 => (LoadKind::Bits64, ProgramValue::UInt64),
        _ if program_type.is_object_pointer() => {
            let load = crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::unplaced(&(crate::kernel::intern_memory(memory.clone()))),
                pointer.clone(),
                LoadKind::Int32,
            );
            return SCALAR_READ_IDENTITY_CACHE.with(|cache| {
                let read = cache.borrow().get(&load)?.0.as_legacy_read().clone();
                Some(ProgramValue::Pointer(Pointer::from_read(
                    Address::loaded(&read).expect("cached pointer read descriptor"),
                    program_type,
                    &crate::kernel::intern_memory_ref(memory),
                    pointer,
                )))
            });
        }
        _ => return None,
    };
    let load = crate::kernel::OldMachineTerm::read_named(
        ProgramPoint::unplaced(&(crate::kernel::intern_memory(memory.clone()))),
        pointer.clone(),
        kind,
    );
    crate::instrumentation::record_deterministic_work(1);
    SCALAR_READ_IDENTITY_CACHE
        .with(|cache| cache.borrow().get(&load).cloned())
        .map(|(identity, _)| wrap(identity.into_legacy_read()))
}

/// `site`, when the caller has one, is where the read is made; the read
/// records it and is the same term.
pub(in crate::kernel) fn symbolic_storage_cell_value(
    memory: &SymbolicMemory,
    site: Option<&ProgramPoint>,
    pointer: &Address,
    program_type: ProgramType,
    record_width: bool,
) -> Option<ProgramValue> {
    if program_type.is_object_pointer() {
        if record_width && pointer.base.is_local_block() {
            record_load_access_width(memory, pointer, program_type.byte_width());
        }
        let load = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::read_at_optional(&(crate::kernel::intern_memory(memory.clone())), site),
            pointer.clone(),
            LoadKind::Int32,
        );
        let value = Address::loaded(&load).expect("symbolic pointer cell read");
        return Some(ProgramValue::Pointer(Pointer::from_read_at(
            value,
            program_type,
            &crate::kernel::intern_memory(memory.clone()),
            site,
            pointer,
        )));
    }
    // Entry cells and contract reads select the same structural descriptor.
    let site = site
        .cloned()
        .unwrap_or_else(|| ProgramPoint::unplaced(&crate::kernel::intern_memory_ref(memory)));
    let value = if record_width {
        symbolic_load_value(memory, &site, pointer, program_type)
    } else {
        symbolic_load_value_unrecorded(memory, &site, pointer, program_type)
    };
    value.map(|value| match value {
        ProgramValue::Int8(bits) => ProgramValue::Int8(canonical_scalar_read(&bits)),
        ProgramValue::Int16(bits) => ProgramValue::Int16(canonical_scalar_read(&bits)),
        ProgramValue::Int32(bits) => ProgramValue::Int32(canonical_scalar_read(&bits)),
        ProgramValue::UInt8(bits) => ProgramValue::UInt8(canonical_scalar_read(&bits)),
        ProgramValue::UInt16(bits) => ProgramValue::UInt16(canonical_scalar_read(&bits)),
        ProgramValue::UInt32(bits) => ProgramValue::UInt32(canonical_scalar_read(&bits)),
        ProgramValue::Int64(bits) => ProgramValue::Int64(canonical_scalar_read(&bits)),
        ProgramValue::UInt64(bits) => ProgramValue::UInt64(canonical_scalar_read(&bits)),
        ProgramValue::Int128(bits) => ProgramValue::Int128(canonical_scalar_read(&bits)),
        ProgramValue::UInt128(bits) => ProgramValue::UInt128(canonical_scalar_read(&bits)),
        other => other,
    })
}

/// Whether the selected proposition contains a state-bearing scalar read,
/// in structural form or through the transitional registered name.
#[cfg(test)]
pub(crate) fn proposition_mentions_scalar_read(proposition: &Proposition) -> bool {
    if proposition_mentions_structural_read(proposition) {
        return true;
    }
    let mut variables = std::collections::BTreeSet::new();
    crate::kernel::reasoning::variable_collection::collect_proposition_bitvector_variables(
        proposition,
        &mut variables,
    );
    variables.iter().any(|variable| {
        is_load_variable(variable) && registered_load_for_variable(variable).is_some()
    })
}

#[cfg(test)]
mod tests {
    #[test]
    fn a_pointer_read_is_named_by_its_version_point() {
        // A pointer cell read before and after a store to another object
        // is one read: both name the cell's version point, as a Click read of
        // that place lowers, rather than each exact memory state.
        let _session = crate::kernel::VerificationSession::enter();
        let cell = Address::new(
            "version-point-pointer-cell".into(),
            AddressOffset::constant(0),
        );
        let other = Address::new("version-point-other".into(), AddressOffset::constant(0));
        let memory = SymbolicMemory::new()
            .with_block("version-point-pointer-cell", 8)
            .with_block("version-point-other", 4);
        let before = intern_memory_ref(&memory);
        let after = crate::kernel::intern_memory(memory.store(other.clone(), int32(9)));
        assert_eq!(
            Address::canonical_read(&before, None, &cell),
            Address::canonical_read(&after, None, &cell),
            "a store to another object leaves the cell's version point"
        );
        assert_ne!(
            Address::loaded_value(&before, &cell),
            Address::loaded_value(&after, &cell),
            "the per-state read names differ, which is what the version point removes"
        );
        // A store to the cell itself starts a new version.
        let rewritten = crate::kernel::intern_memory(after.memory().clone().store(
            cell.clone(),
            ProgramValue::Pointer(Pointer::new(Address::null(), ProgramType::Int32Pointer)),
        ));
        assert_ne!(
            Address::canonical_read(&after, None, &cell),
            Address::canonical_read(&rewritten, None, &cell),
        );
    }

    /// A pointer read and a 64-bit integer read of one cell share the
    /// selection state (the identity cache and the read observation) and
    /// select the same version, whichever registers first
    /// (`design/loads.md`, step 3b). Re-keying that state by cell and width
    /// must keep this.
    #[test]
    fn a_pointer_read_and_a_64_bit_integer_read_of_one_cell_select_one_version() {
        for pointer_first in [true, false] {
            let _session = crate::kernel::VerificationSession::enter();
            let cell = Address::new("shared-selection-cell".into(), AddressOffset::constant(0));
            let other = Address::new("shared-selection-other".into(), AddressOffset::constant(0));
            let memory = SymbolicMemory::new()
                .with_block("shared-selection-cell", 8)
                .with_block("shared-selection-other", 4);
            let before = intern_memory_ref(&memory);
            let after = crate::kernel::intern_memory(memory.store(other, int32(9)));
            let integer = || {
                canonical_scalar_read(&OldMachineTerm::read_named(
                    ProgramPoint::at(&after),
                    cell.clone(),
                    LoadKind::Bits64,
                ))
            };
            let pointer = || Address::canonical_read(&after, None, &cell);
            let (integer_read, pointer_read) = if pointer_first {
                let pointer_read = pointer();
                (integer(), pointer_read)
            } else {
                let integer_read = integer();
                (integer_read, pointer())
            };
            let OldMachineTerm::MemoryLoad(point, address, _) = &integer_read else {
                panic!("a selected integer read: {integer_read:?}");
            };
            assert_eq!(
                pointer_read,
                Address::loaded_source_value_at(point, address),
                "the pointer is the load the integer read selected (pointer first: {pointer_first})"
            );
            assert_eq!(
                pointer_read,
                Address::canonical_read(&before, None, &cell),
                "the store to another object leaves the version"
            );
            let observation =
                read_observations::existing(point.shared_memory(), address, LoadKind::Bits64)
                    .expect("one observation for both reads");
            assert!(is_selected_scalar_read(point, address, LoadKind::Bits64));
            assert_eq!(read_observations::bytes(observation), Some(8));
        }
    }

    #[test]
    fn a_pointer_version_point_read_does_not_cross_a_write_to_its_upper_half() {
        // A pointer cell is eight bytes. A store to its upper four bytes
        // changes the pointer, so the version-point read after the store is
        // not the read before it, even when the cell was observed as two
        // four-byte halves first.
        let _session = crate::kernel::VerificationSession::enter();
        let cell = Address::symbolic(Variable(92_399));
        let before = SymbolicMemory::new();
        let observed = before
            .clone()
            .materialize_symbolic_cell(cell.clone(), ProgramType::Int32)
            .materialize_symbolic_cell(cell.clone().offset_by_bytes(4), ProgramType::Int32);
        let overwritten = observed.clone().store(
            cell.clone().offset_by_bytes(4),
            ProgramValue::UInt32(0u32.into()),
        );
        let canonical_read =
            |memory: &SharedMemory, cell: &Address| Address::canonical_read(memory, None, cell);
        for read in [
            &canonical_read as &dyn Fn(&SharedMemory, &Address) -> Address,
            &Address::canonical_loaded_value,
        ] {
            let read = |memory: &SymbolicMemory| read(&intern_memory_ref(memory), &cell);
            assert_eq!(
                read(&before),
                read(&observed),
                "observing the halves changes no bytes"
            );
            assert_ne!(read(&observed), read(&overwritten));
        }
    }

    #[test]
    fn exact_read_descriptors_and_comparison_identities_keep_distinct_roles() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Address::new("read-api-target".into(), AddressOffset::constant(0));
        let other = Address::new("read-api-other".into(), AddressOffset::constant(0));
        let memory = SymbolicMemory::new()
            .with_block("read-api-target", 4)
            .with_block("read-api-other", 4)
            .store(pointer.clone(), int32(7));
        let before = intern_memory_ref(&memory);
        let after = crate::kernel::intern_memory(memory.store(other, int32(9)));
        record_load_access_width(before.memory(), &pointer, 4);
        record_load_access_width(after.memory(), &pointer, 4);
        let first = OldMachineTerm::memory_read(before.clone(), pointer.clone(), LoadKind::Int32);
        let second = OldMachineTerm::memory_read(after.clone(), pointer.clone(), LoadKind::Int32);
        assert_ne!(
            first, second,
            "exact descriptors retain their selected memory"
        );
        assert!(read_observations::existing(&before, &pointer, LoadKind::Int32).is_none());
        assert!(read_observations::existing(&after, &pointer, LoadKind::Int32).is_none());
        let (first_identity, _) = scalar_reads::select_comparison_identity(
            ScalarReadDescriptor::from_term(&first).unwrap(),
        );
        let (second_identity, width) = scalar_reads::select_comparison_identity(
            ScalarReadDescriptor::from_term(&second).unwrap(),
        );
        assert_eq!(
            first_identity, second_identity,
            "the other store leaves this cell unchanged"
        );
        assert_eq!(width, Some(4));
        assert_eq!(
            ScalarReadDescriptor::from_term(&second).unwrap().memory(),
            &after
        );
        assert_eq!(load_variable_registry_len(), 0);

        // Existing callers deliberately retain the comparison identity until
        // the exact-state lowering migration. Its observation keeps the live
        // origin and access width, rather than treating that origin as identity.
        let legacy = canonical_scalar_read(&second);
        assert_eq!(&legacy, second_identity.as_legacy_read());
        let observation =
            scalar_read_observation(crate::kernel::MachineOperandView::Old(&legacy)).unwrap();
        assert_eq!(observation.origin, Some(ProgramPoint::at(&after)));
        assert_eq!(observation.bytes, 4);
        assert_eq!(
            canonical_scalar_read(&second),
            legacy,
            "warm compatibility path"
        );
    }

    #[test]
    fn an_unwritten_static_word_names_function_entry_after_a_local_declaration() {
        check_unwritten_static_scalar_version(ProgramType::Int32, 0);
    }

    #[test]
    fn an_unwritten_static_array_element_uses_the_same_entry_point() {
        check_unwritten_static_scalar_version(ProgramType::Int32, 4);
    }

    #[test]
    fn an_unwritten_static_halfword_uses_the_same_entry_point() {
        check_unwritten_static_scalar_version(ProgramType::UInt16, 2);
    }

    #[test]
    fn an_unwritten_static_wide_word_uses_the_same_entry_point() {
        check_unwritten_static_scalar_version(ProgramType::UInt64, 8);
    }

    fn check_unwritten_static_scalar_version(ty: ProgramType, offset: u32) {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = SymbolicMemory::global_pointer("unwritten").offset_by_bytes(offset);
        let entry = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(cell.base.clone(), 16))
            .begin_function_entry_memory();
        let next = entry
            .clone()
            .with_memory(
                entry
                    .memory()
                    .clone()
                    .with_block(SymbolicMemory::local_pointer("local").base.clone(), 4),
            )
            .with_resource_context(ResourceContext::new().unchecked_with_fact(
                ResourceFact::view_memory(MemoryRange::access(cell.clone(), ty)),
            ));
        let point = next.program_point();
        assert_ne!(point.id(), entry.program_point_id());
        assert_eq!(
            point
                .indexed_array_version(&cell.base)
                .and_then(|version| version.read_version_id()),
            entry.program_point_id(),
        );

        let expression = ProgramExpression::Load(Box::new(ProgramExpression::Value(
            ProgramValue::typed_pointer(cell.clone(), ty.pointer_to().expect("pointer to scalar")),
        )));
        let paths = super::super::evaluate_expression_value_paths(
            &next,
            &expression,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one checked C read");
        };
        let ExpressionOutcome::Value(value) = &path.outcome else {
            panic!("static storage supplies the word: {:?}", path.outcome);
        };
        let Some(OldMachineTerm::MemoryLoad(version, address, kind)) =
            crate::kernel::spec::program_value_bitvector_term(&value.native())
        else {
            panic!("one symbolic word read");
        };
        assert_eq!(version.read_version_id(), entry.program_point_id());
        assert_eq!(*address, cell);
        assert_eq!(kind, LoadKind::of_type(ty).expect("scalar load kind"));
        assert_eq!(
            point
                .ordinary_typed_version(&cell, ty)
                .and_then(|version| version.read_version_id()),
            entry.program_point_id(),
        );
        let written = next.clone().with_memory(next.memory().clone().store(
            cell.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(7)),
        ));
        assert!(
            written
                .program_point()
                .unwritten_static_scalar_version(&cell, ty)
                .is_none()
        );
    }

    #[test]
    fn a_checked_c_read_names_the_call_that_wrote_its_static_word() {
        check_static_call_output_scalar_read(
            ProgramType::Int32,
            crate::kernel::effective_type::CScalarClass::Int,
        );
    }

    #[test]
    fn a_checked_c_read_names_the_call_that_wrote_its_static_wide_word() {
        check_static_call_output_scalar_read(
            ProgramType::UInt64,
            crate::kernel::effective_type::CScalarClass::Long,
        );
    }

    fn check_static_call_output_scalar_read(
        ty: ProgramType,
        class: crate::kernel::effective_type::CScalarClass,
    ) {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = SymbolicMemory::global_pointer("call_output_static");
        let start = ExecutionState::new().begin_function_entry_memory();
        let entry = start.clone().with_function_entry_memory(
            start.memory().clone().with_classed_scalar_block(
                cell.base.clone(),
                ty.byte_width(),
                ty,
                Some(crate::kernel::effective_type::CAccessClass::Scalar(class)),
            ),
        );
        let facts = PureFactContext::new();
        let range = MemoryRange::access(cell.clone(), ty);
        let output = entry
            .clone()
            .with_memory(entry.memory().clone().with_call_memory_havoc(
                Variable(1_008_445),
                std::slice::from_ref(&range),
                &facts,
                None,
            ));
        let next = output.clone().with_memory(
            output
                .memory()
                .clone()
                .with_block(SymbolicMemory::local_pointer("unrelated").base.clone(), 4),
        );
        let next = next.with_resource_context(
            ResourceContext::new().unchecked_with_fact(ResourceFact::view_memory(range)),
        );
        let expression = ProgramExpression::Load(Box::new(ProgramExpression::Value(
            ProgramValue::typed_pointer(cell.clone(), ty.pointer_to().expect("scalar pointer")),
        )));
        let paths = super::super::evaluate_expression_value_paths(
            &next,
            &expression,
            &facts,
            &mut ExecutionBudget::new(),
        )
        .expect("checked C access");
        let [path] = paths.as_slice() else {
            panic!("expected one checked read path");
        };
        let ExpressionOutcome::Value(value) = &path.outcome else {
            panic!("expected the call-modified value: {:?}", path.outcome);
        };
        let Some(OldMachineTerm::MemoryLoad(version, address, kind)) =
            crate::kernel::spec::program_value_bitvector_term(&value.native())
        else {
            panic!("expected a typed integer read");
        };
        assert_eq!(version.read_version_id(), output.program_point_id());
        assert_eq!(*address, cell);
        assert_eq!(kind, LoadKind::of_type(ty).expect("scalar load kind"));
        assert_eq!(
            next.program_point()
                .ordinary_typed_version(&cell, ty)
                .and_then(|point| point.read_version_id()),
            output.program_point_id(),
        );
    }

    #[test]
    fn a_checked_c_read_names_the_call_that_initialized_its_word() {
        check_call_output_scalar_read(ProgramType::Int32);
    }

    #[test]
    fn a_checked_c_read_names_the_call_that_initialized_its_halfword() {
        check_call_output_scalar_read(ProgramType::UInt16);
    }

    #[test]
    fn a_checked_c_read_names_the_call_that_initialized_its_wide_word() {
        check_call_output_scalar_read(ProgramType::UInt64);
    }

    fn check_call_output_scalar_read(ty: ProgramType) {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = SymbolicMemory::local_pointer("output");
        let bytes = ty.byte_width();
        let start = ExecutionState::new().begin_function_entry_memory();
        let declared =
            start
                .clone()
                .with_memory(start.memory().clone().with_declared_scalar_block(
                    cell.base.clone(),
                    bytes,
                    ty,
                ));
        let output = declared.clone().with_memory(
            declared
                .memory()
                .clone()
                .with_initialized_call_output(&cell, bytes),
        );
        let next = output.clone().with_memory(
            output
                .memory()
                .clone()
                .with_block(SymbolicMemory::local_pointer("other").base.clone(), 4),
        );
        let next = next.with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::view_memory(MemoryRange::access(cell.clone(), ty)),
        ));
        let expected = next
            .program_point()
            .ordinary_typed_version(&cell, ty)
            .expect("the local scalar has a recorded call output");
        assert_eq!(expected.read_version_id(), output.program_point_id());
        assert_ne!(expected.read_version_id(), next.program_point_id());

        let expression = ProgramExpression::Load(Box::new(ProgramExpression::Value(
            ProgramValue::typed_pointer(cell.clone(), ty.pointer_to().expect("pointer to scalar")),
        )));
        let paths = super::super::evaluate_expression_value_paths(
            &next,
            &expression,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one checked C read");
        };
        let ExpressionOutcome::Value(value) = &path.outcome else {
            panic!("the call initialized the cell: {:?}", path.outcome);
        };
        let Some(OldMachineTerm::MemoryLoad(version, address, kind)) =
            crate::kernel::spec::program_value_bitvector_term(&value.native())
        else {
            panic!("one typed word read");
        };
        assert_eq!(version.read_version_id(), expected.read_version_id());
        assert_eq!(*address, cell);
        assert_eq!(kind, LoadKind::of_type(ty).expect("scalar load kind"));
    }

    #[test]
    fn a_checked_c_read_keeps_the_caller_pointer_cell_entry_version() {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let ty = ProgramType::Int32Pointer;
        let state = ExecutionState::new()
            .begin_function_entry_memory()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(
                ResourceFact::view_memory(MemoryRange::access(cell.clone(), ty)),
            ));
        let expression = ProgramExpression::Load(Box::new(ProgramExpression::Value(
            ProgramValue::typed_pointer(cell.clone(), ProgramType::Int32PointerPointer),
        )));
        let paths = super::super::evaluate_expression_value_paths(
            &state,
            &expression,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one checked pointer read");
        };
        let ExpressionOutcome::Value(value) = &path.outcome else {
            panic!(
                "the caller supplies a readable pointer cell: {:?}",
                path.outcome
            );
        };
        let pointer = value.pointer().expect("complete pointer read");
        let defining_read = pointer.address().as_loaded_value().expect("read identity");
        assert_eq!(
            defining_read.point.read_version_id(),
            state.program_point_id()
        );
        assert_eq!(defining_read.defining_address, cell);
        assert!(defining_read.identity.is_point_named());
        assert_eq!(pointer.provenance(), pointer.address());
        assert_eq!(pointer.bounds_owner(), Some(pointer.address()));
    }

    #[test]
    fn an_unwritten_entry_pointer_has_one_identity_for_address_and_domain() {
        let _session = crate::kernel::VerificationSession::enter();
        let state = ExecutionState::new().begin_function_entry_memory();
        let entry = state.program_point();
        let cell = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let ty = ProgramType::Int32Pointer;
        let version = entry
            .ordinary_typed_version(&cell, ty)
            .expect("entry version");
        let path = evaluate_indexed_read(
            version,
            &entry,
            cell.clone(),
            ty,
            ExecutionFacts::new(),
            Vec::new(),
        );
        assert!(path.facts.is_empty());

        let ExpressionOutcome::Value(ProgramValue::Pointer(read)) = path.outcome else {
            panic!("expected a complete pointer read");
        };
        let descriptor = read.address().as_loaded_value().expect("entry read");
        assert_eq!(descriptor.point.read_version_id(), state.program_point_id());
        assert_eq!(descriptor.defining_address, cell);
        assert!(descriptor.identity.is_point_named());
        assert_eq!(read.provenance(), read.address());
        assert_eq!(read.bounds_owner(), Some(read.address()));
        assert_eq!(point_named_pointer_cell_read(&entry, &cell, ty), Some(read));
    }

    #[test]
    fn exact_scalar_read_comparison_keeps_the_point_without_an_indexed_version() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let memory = SymbolicMemory::new();
        let first = ProgramPoint::starting_at(&memory).for_exact_read();
        let second = ProgramPoint::starting_at(&memory).for_exact_read();
        let kind = LoadKind::UInt16;
        let compare = |point| comparison_identity_of_exact_read(point, &address, kind);

        assert_eq!(
            compare(&first),
            crate::kernel::OldMachineTerm::read_named(first.clone(), address.clone(), kind),
        );
        assert_ne!(compare(&first), compare(&second));
    }

    #[test]
    fn scalar_read_comparison_identities_distinguish_writes_and_kinds() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Address::new("read-api-written".into(), AddressOffset::constant(0));
        let memory = SymbolicMemory::new()
            .with_block("read-api-written", 4)
            .store(pointer.clone(), int32(7));
        let before = intern_memory_ref(&memory);
        let after = crate::kernel::intern_memory(memory.store(pointer.clone(), int32(9)));
        let identity = |memory: SharedMemory, kind| {
            let read = OldMachineTerm::memory_read(memory, pointer.clone(), kind);
            scalar_reads::select_comparison_identity(
                ScalarReadDescriptor::from_term(&read).unwrap(),
            )
            .0
        };
        assert_ne!(
            identity(before.clone(), LoadKind::Int32),
            identity(after, LoadKind::Int32),
            "a changed cell must not share the preceding comparison identity"
        );
        assert_ne!(
            identity(before.clone(), LoadKind::Int8),
            identity(before, LoadKind::UInt8),
            "signed and unsigned byte observations have distinct read kinds"
        );
    }

    #[test]
    fn pointer_producers_do_not_allocate_scalar_names() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = SymbolicMemory::new();
        let address = Address::symbolic(Variable(93_001));
        let before = load_variable_registry_len();
        for ty in [
            ProgramType::Int32Pointer,
            ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
        ] {
            let ordinary = symbolic_load_value(
                &memory,
                &crate::kernel::ProgramPoint::of_memory(&memory),
                &address,
                ty,
            )
            .unwrap();
            let logical = memory.symbolic_pointer_version_load(None, &address, ty);
            let entry = symbolic_storage_cell_value(&memory, None, &address, ty, true)
                .expect("entry pointer read");
            let run = memory.clone().with_seeded_cells(
                address.clone(),
                8,
                ty,
                0,
                1,
                intern_memory_ref(&memory),
            );
            let ExpressionOutcome::Value(seeded) = run.load(&address) else {
                panic!("seeded pointer read");
            };
            for value in [&ordinary, &logical, &entry, &seeded] {
                let ProgramValue::Pointer(pointer) = value else {
                    panic!("pointer read");
                };
                let read = pointer
                    .address()
                    .as_loaded_value()
                    .expect("structural read");
                assert_eq!(read.defining_address, address);
            }
            assert_eq!(ordinary, logical);
            assert_eq!(ordinary, entry);
            assert_eq!(load_variable_registry_len(), before);
        }
    }

    #[test]
    fn native_narrow_reads_keep_their_width_beside_word_observations() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::intern_memory(SymbolicMemory::new());
        let pointer = Address::symbolic(Variable(993151));
        record_load_access_width(memory.memory(), &pointer, 8);
        for (kind, bytes) in [
            (LoadKind::Int8, 1),
            (LoadKind::UInt8, 1),
            (LoadKind::Int16, 2),
            (LoadKind::UInt16, 2),
        ] {
            let raw = crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(&memory),
                pointer.clone(),
                kind,
            );
            for _ in 0..2 {
                let read = canonical_scalar_read(&raw);
                assert_eq!(
                    scalar_read_observation(crate::kernel::MachineOperandView::Old(&read))
                        .unwrap()
                        .bytes,
                    bytes,
                    "{kind:?}: both initial selection and cache hits keep native width"
                );
            }
        }
        let wide = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&memory),
            pointer,
            LoadKind::Int32,
        );
        let read = canonical_scalar_read(&wide);
        assert_eq!(
            scalar_read_observation(crate::kernel::MachineOperandView::Old(&read))
                .unwrap()
                .bytes,
            8,
            "the legacy pointer carrier still retains its recorded width"
        );
    }

    #[test]
    fn querying_a_registered_read_preserves_its_access_width() {
        for bytes in [4, 8] {
            let _session = crate::kernel::VerificationSession::enter();
            let memory = crate::kernel::intern_memory(SymbolicMemory::new());
            let pointer = Address::symbolic(Variable(993149));
            let name = load_variable_for_exact_cell(&memory, &pointer, LoadKind::Int32, bytes);
            let raw = crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(&memory),
                pointer.clone(),
                LoadKind::Int32,
            );
            assert_eq!(
                load_term_access_width(&memory, &pointer, LoadKind::Int32),
                bytes
            );
            let canonical = canonical_term(&raw);
            assert!(matches!(canonical, OldMachineTerm::MemoryLoad(..)));
            assert_eq!(registered_load_bytes_for_variable(&name), Some(bytes));
            assert_eq!(
                scalar_read_observation(crate::kernel::MachineOperandView::Old(&canonical))
                    .unwrap()
                    .bytes,
                bytes
            );
            record_load_access_width(memory.memory(), &pointer, 8);
            assert_eq!(
                load_term_access_width(&memory, &pointer, LoadKind::Int32),
                8
            );
        }
    }

    #[test]
    fn structural_read_observations_keep_live_width_epoch_and_restored_metadata() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::intern_memory(SymbolicMemory::new());
        let pointer = Address::symbolic(Variable(993150));
        let name = load_variable_for_exact_cell(&memory, &pointer, LoadKind::Int32, 4);
        let term = registered_scalar_read_term(&name, MachineIntegerType::Int32).unwrap();
        let other = term.with_machine_observation_type(MachineIntegerType::UInt32);
        let observe = |term: &crate::kernel::KernelTerm| {
            scalar_read_observation(crate::kernel::MachineOperandView::Shared(term)).unwrap()
        };
        assert_eq!(
            observe(&other).bytes,
            4,
            "a new format is not a wider access"
        );
        assert_eq!(observe(&other).origin, Some(ProgramPoint::at(&memory)));
        begin_load_origin_epoch();
        assert!(
            observe(&term).origin.is_none(),
            "a query must not renew an origin"
        );
        assert!(observe(&other).origin.is_none());
        load_variable_for_exact_cell(&memory, &pointer, LoadKind::Int32, 8);
        assert_eq!(observe(&term).bytes, 8, "width updates are live");
        assert_eq!(observe(&other).origin, Some(ProgramPoint::at(&memory)));
        let saved = capture_load_variable_registry();
        clear_load_variable_registry();
        restore_load_variable_registry(&saved);
        assert_eq!(observe(&term).bytes, 8);
        assert_eq!(observe(&other).bytes, 8);
    }

    use super::*;

    #[test]
    fn forced_logical_pointer_reads_keep_the_state_identity_of_cached_values() {
        for (ty, stored) in [
            (ProgramType::Int32Pointer, Address::null()),
            (
                ProgramType::Int32Pointer,
                Address::symbolic(Variable(989_850)),
            ),
            (
                ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
                Address::null(),
            ),
            (
                ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
                Address::function("callback"),
            ),
        ] {
            let _session = crate::kernel::VerificationSession::enter();
            let address = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
            let value = ProgramValue::typed_pointer(stored.clone(), ty);
            let memory = SymbolicMemory::new().store(address.clone(), value.clone());
            let context = PureFactContext::new()
                .allow_symbolic_contract_loads()
                .assume_proposition(Proposition::ResourceComposition(
                    ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
                        MemoryRange::new(address.clone(), 0u32.into(), 2u32.into()),
                    )),
                ));
            let ordinary = evaluate_logical_memory_load_paths(
                &memory,
                address.clone(),
                ty,
                ExecutionFacts::new(),
                vec![],
                &context,
            );
            // The structural read keeps its own provenance. The complete
            // stored value is related through the graph, not folded into it.
            let ProgramValue::Pointer(stored_value) = &value else {
                unreachable!()
            };
            assert!(
                matches!(&ordinary[0].outcome, ExpressionOutcome::Value(ProgramValue::Pointer(actual))
                if actual.address() != &stored
                    && context.equality_graph.knows_condition(
                        &OldConditionTerm::PointerEqual(
                            Box::new(actual.clone()), Box::new(stored_value.clone()),
                        ), true,
                    ))
            );
            let forced_context = context.clone().force_symbolic_external_loads();
            let forced = evaluate_logical_memory_load_paths(
                &memory,
                address.clone(),
                ty,
                ExecutionFacts::new(),
                vec![],
                &forced_context,
            );
            let [path] = forced.as_slice() else {
                panic!("one logical read")
            };
            let ExpressionOutcome::Value(ProgramValue::Pointer(read)) = &path.outcome else {
                panic!("typed pointer read")
            };
            assert_ne!(
                read.address(),
                &stored,
                "forced reads must retain a state term"
            );
            assert!(
                path.facts
                    .iter()
                    .any(ExecutionPureFact::is_logical_read_equation),
                "the stored value's checked equation remains available"
            );
            let known =
                assumptions_with_path_context(&forced_context, &path.facts, &path.obligations);
            assert!(known.pointers_known_equal(read.address(), &stored));
        }
    }

    #[test]
    fn logical_read_of_copied_pointer_retains_its_complete_value() {
        let complete_equalities = [false, true].map(|declare_after_store| {
            let _session = crate::kernel::VerificationSession::enter();
            let field = SymbolicMemory::frame_local_pointer(0, "copied_pointer");
            let stored = Pointer::new(
                Address::symbolic(Variable(210_399)),
                ProgramType::Int32Pointer,
            );
            let mut memory =
                SymbolicMemory::new().store(field.clone(), ProgramValue::Pointer(stored.clone()));
            // Aggregate parameter binding writes its fields, then declares
            // the private destination block. Compare the immediate store.
            if declare_after_store {
                memory = memory.with_block(field.base.clone(), 8);
            }
            let context = PureFactContext::new()
                .allow_symbolic_contract_loads()
                .force_symbolic_external_loads();
            let paths = evaluate_logical_memory_load_paths(
                &memory,
                field,
                ProgramType::Int32Pointer,
                ExecutionFacts::new(),
                vec![],
                &context,
            );
            let [path] = paths.as_slice() else {
                panic!("one logical read expected");
            };
            let ExpressionOutcome::Value(ProgramValue::Pointer(read)) = &path.outcome else {
                panic!("pointer read expected");
            };
            let known = assumptions_with_path_context(&context, &path.facts, &path.obligations);
            assert!(known.pointers_known_equal(read.address(), stored.address()));
            // Check entailment, not exact premise raising: the producer's
            // equation may name the endpoints in the opposite order.
            known.contains_known(&Proposition::condition_is(
                OldConditionTerm::pointer_equal(read.clone(), stored),
                true,
            ))
        });
        assert_eq!(
            complete_equalities,
            [true, true],
            "complete pointer equality immediately after store / after declaration"
        );
    }

    #[test]
    fn forced_logical_pointer_read_reuses_a_materialized_reads_definition() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let context = PureFactContext::new()
            .allow_symbolic_contract_loads()
            .force_symbolic_external_loads();
        let memory = SymbolicMemory::new();
        let first = evaluate_logical_memory_load_paths(
            &memory,
            address.clone(),
            ProgramType::Int32Pointer,
            ExecutionFacts::new(),
            vec![],
            &context,
        );
        let ExpressionOutcome::Value(value @ ProgramValue::Pointer(_)) = &first[0].outcome else {
            panic!("pointer read")
        };
        let retained = memory.store(address.clone(), value.clone());
        let second = evaluate_logical_memory_load_paths(
            &retained,
            address,
            ProgramType::Int32Pointer,
            ExecutionFacts::new(),
            vec![],
            &context,
        );
        let ProgramValue::Pointer(expected) = value else {
            unreachable!()
        };
        let ExpressionOutcome::Value(ProgramValue::Pointer(actual)) = &second[0].outcome else {
            panic!("retained pointer read")
        };
        // The cell holds its own read, so the read is that read: no stored
        // value stands in for it, and none needs an equation.
        assert_eq!(actual.address(), expected.address());
    }

    #[test]
    fn program_pointer_facts_retain_their_scoped_read_producer() {
        let _session = crate::kernel::VerificationSession::enter();
        let empty = PureFactContext::new();
        let registry_before = capture_load_variable_registry();
        let memory = SymbolicMemory::new();
        let address = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(8));
        let paths = evaluate_memory_load_paths(
            &memory,
            address,
            ProgramType::Int32Pointer,
            ExecutionFacts::new(),
            Vec::new(),
            &empty,
            true,
            false,
            None,
            None,
        );
        let [path] = paths.as_slice() else {
            panic!("one program read")
        };
        let ExpressionOutcome::Value(ProgramValue::Pointer(pointer)) = &path.outcome else {
            panic!("pointer value")
        };
        let ordinary: ExecutionFacts = path
            .facts
            .iter()
            .map(|fact| ExecutionPureFact::new(fact.proposition().clone()))
            .collect::<Vec<_>>()
            .into();
        let _ordinary_context = assumptions_with_path_context(&empty, &ordinary, &path.obligations);
        let context = assumptions_with_path_context(&empty, &path.facts, &path.obligations);
        // The program read's value is the read's own name: its definition
        // decodes from the value, not from a context-admitted producer.
        let defining_address =
            Address::new(AddressBase::ExternalArgument, AddressOffset::constant(8));
        let definition = pointer
            .address()
            .as_loaded_value()
            .expect("a program pointer read names its read");
        assert_eq!(definition.defining_address, defining_address);
        assert_eq!(definition.displacement, AddressOffset::constant(0));
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_term(pointer.address()).is_some()
        );
        assert!(
            crate::kernel::memory_history::checked_pointer_read_endpoint(
                pointer.address(),
                &context
            )
            .is_some()
        );
        assert!(
            ResourceContext::new()
                .memory_write_range(pointer.address(), 4, &context)
                .is_none()
        );
        restore_load_variable_registry(&registry_before);
        // A load carries its own point and cell (`design/loads.md`,
        // "Terms"): a restore of the interner forgets the identity for later
        // interning, but the term still decodes to the read it names, with
        // no registry lookup.
        let restored = pointer
            .address()
            .as_loaded_value()
            .expect("a load decodes from the term itself");
        assert_eq!(restored.defining_address, defining_address);
    }

    #[test]
    fn logical_read_equations_are_not_conditions_or_quantifier_guards() {
        let value = Address::symbolic(Variable(959_001));
        let read = Address::loaded_value(&intern_memory(SymbolicMemory::new()), &value);
        let fact = ExecutionPureFact::logical_read_equation(
            Pointer::new(value, ProgramType::Int32Pointer),
            read,
        );
        let facts: ExecutionFacts = vec![fact.clone()].into();
        assert!(!facts.has_path_conditions());
        let goal = Proposition::condition_is(OldConditionTerm::Constant(true), true);
        assert_eq!(wrap_path_context(goal.clone(), &facts, &[]), goal);
        let path = crate::kernel::spec::SpecPropositionPath {
            proposition: goal.clone(),
            facts: facts.clone(),
            obligations: Vec::new(),
            introductions: Vec::new(),
        };
        assert_eq!(crate::kernel::spec::existential_body_branch(&path), goal);
        let ordinary: ExecutionFacts =
            vec![ExecutionPureFact::new(fact.proposition().clone())].into();
        assert!(ordinary.has_path_conditions());
        assert_ne!(wrap_path_context(goal.clone(), &ordinary, &[]), goal);
        let changed: ExecutionFacts = vec![fact.with_proposition(goal)].into();
        assert!(
            changed.has_path_conditions(),
            "rewriting drops exact read-producer metadata"
        );
    }

    #[test]
    fn logical_pointer_read_does_not_export_a_narrow_scalar_as_a_full_cell() {
        let _session = crate::kernel::VerificationSession::enter();
        let context = PureFactContext::new();
        let address = Address::symbolic(Variable(959_101));
        let base = SymbolicMemory::new();
        let mut facts = ExecutionFacts::new();
        let value = canonicalized_symbolic_load_value_with_identity(
            &base,
            None,
            &address,
            ProgramType::Int32,
            &mut facts,
            &context,
            None,
            LoadPurpose::Logical,
        )
        .unwrap();
        let memory = base.materialize_named_cell(address.clone(), value);
        let paths = evaluate_logical_memory_load_paths(
            &memory,
            address,
            ProgramType::Int64Pointer,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
        );
        assert!(paths.iter().all(|path| path.facts.is_empty()));
    }

    // Typed observations must preserve the complete pointer, selected alias
    // premises, state changes, and session boundaries without corpus scans.
    // A cached pointer can still denote an older defining load after a frame
    // materializes its named scalar cell. A checked index must retain where
    // that value was read now, without publishing evidence to another context.
    #[test]
    fn checked_resource_index_retains_its_current_pointer_cell() {
        let _session = crate::kernel::VerificationSession::enter();
        let empty = PureFactContext::new();
        let base = SymbolicMemory::new();
        let source = Address::symbolic(Variable(955_001));
        let cached = logical_pointer_read(&base, &source, &empty);
        assert_eq!(
            cached
                .as_loaded_value()
                .expect("typed cached load")
                .defining_address,
            source
        );
        let address = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(955_002)), 4),
        );
        let alias = Address::symbolic(Variable(955_003));
        let current = base.clone().materialize_named_cell(
            address.clone(),
            ProgramValue::Pointer(Pointer::from_read(
                cached.clone(),
                ProgramType::Int64Pointer,
                &intern_memory_ref(&base),
                &source,
            )),
        );
        let logical = logical_pointer_read(&current, &alias, &empty);
        let model = Address::symbolic(Variable(955_004));
        let base_context = empty
            .clone()
            .assume_condition(
                OldConditionTerm::address_equal(alias.clone(), address.clone()),
                true,
            )
            .assume_condition(
                OldConditionTerm::PointerEqual(
                    Box::new(Pointer::new(model.clone(), ProgramType::Int64Pointer)),
                    Box::new(Pointer::from_read(
                        logical.clone(),
                        ProgramType::Int64Pointer,
                        &intern_memory(current.clone()),
                        &alias,
                    )),
                ),
                true,
            );
        let context = base_context.clone().require_owned_expression_loads();
        let isolated = context.clone();
        let paths = evaluate_memory_load_paths(
            &current,
            address.clone(),
            ProgramType::Int64Pointer,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
            true,
            false,
            None,
            None,
        );
        let [path] = paths.as_slice() else {
            panic!("one checked read");
        };
        let ExpressionOutcome::Value(ProgramValue::Pointer(value)) = &path.outcome else {
            panic!("a pointer-valued read");
        };
        let arguments_equal = |facts: &PureFactContext| {
            crate::kernel::resource_arguments_proven_equal(
                &AlgebraicValue::Program(ProgramValue::typed_pointer(
                    model.clone(),
                    ProgramType::Int64Pointer,
                )),
                &AlgebraicValue::Program(ProgramValue::Pointer(value.clone())),
                facts,
            )
        };
        assert!(
            !arguments_equal(&context),
            "the older definition is not the current observation"
        );
        for fact in &path.facts {
            fact.retain_pointer_read_definition(&context);
        }
        assert!(arguments_equal(&context));
        assert!(
            !arguments_equal(&isolated),
            "checked evidence must stay in its context"
        );
        assert!(context.pointers_known_equal(&model, value.address()));
        let mut checkpoint = context.equality_graph.input_root();
        assert!(checkpoint.append_inputs_from(&context.equality_graph));
        assert!(checkpoint.are_equal(&model, value.address()));
        let restricted = context.restricted_to_facts(&[], &[]);
        assert!(!restricted.pointers_known_equal(&model, value.address()));
        let missing_alias = empty.clone().assume_condition(
            OldConditionTerm::PointerEqual(
                Box::new(Pointer::new(model.clone(), ProgramType::Int64Pointer)),
                Box::new(Pointer::from_read(
                    logical.clone(),
                    ProgramType::Int64Pointer,
                    &intern_memory(current.clone()),
                    &alias,
                )),
            ),
            true,
        );
        for fact in &path.facts {
            fact.retain_pointer_read_definition(&missing_alias);
        }
        assert!(!arguments_equal(&missing_alias));
        for (ordinary, volatile) in [(true, false), (false, true)] {
            let control = if ordinary {
                base_context.clone()
            } else {
                isolated.clone()
            };
            let paths = evaluate_memory_load_paths(
                &current,
                address.clone(),
                ProgramType::Int64Pointer,
                ExecutionFacts::new(),
                Vec::new(),
                &control,
                true,
                volatile,
                None,
                None,
            );
            for path in paths {
                for fact in &path.facts {
                    fact.retain_pointer_read_definition(&control);
                }
            }
            assert!(!arguments_equal(&control));
        }
        let forged_context = isolated.clone();
        for fact in &path.facts {
            let mut forged = fact.clone();
            forged.certified = false;
            forged.retain_pointer_read_definition(&forged_context);
        }
        assert!(!arguments_equal(&forged_context));

        // A contract argument outlives its temporary expression fact stream.
        // It must keep the same certified read evidence as a recursive child.
        let argument_context = base_context.clone().require_owned_expression_loads();
        let state = ExecutionState::new()
            .with_memory(current.clone())
            .with_resource_context(ResourceContext::new().unchecked_with_fact(
                ResourceFact::view_memory(MemoryRange::new_with_element_width(
                    address.clone(),
                    0u32.into(),
                    1u32.into(),
                    8,
                )),
            ));
        let expression = crate::kernel::program_expression::typed_load(
            ProgramExpression::Value(ProgramValue::typed_pointer(
                address.clone(),
                ProgramType::Int64PointerPointer,
            )),
            ProgramType::Int64Pointer,
        );
        let value = crate::kernel::loops::evaluate_loop_effect_segment_value(
            &state,
            &expression,
            &argument_context,
            "checked resource argument",
            &mut ExecutionBudget::beside_live_state(),
        )
        .unwrap()
        .unwrap();
        assert!(crate::kernel::resource_arguments_proven_equal(
            &AlgebraicValue::Program(ProgramValue::typed_pointer(
                model,
                ProgramType::Int64Pointer
            )),
            &AlgebraicValue::Program(value),
            &argument_context,
        ));
    }

    #[test]
    fn a_retired_local_no_pointer_reaches_is_not_part_of_a_read_projection() {
        // A read through a pointer is named at the projection of its version
        // point. Ending the lifetime of a local whose address is never taken
        // changes nothing such a load can observe, so the projection, and
        // with it the read's name, stays the same; ending the lifetime of a
        // local whose address may be held changes it.
        let _session = crate::kernel::VerificationSession::enter();
        crate::kernel::primitives::set_never_address_taken_locals(
            ["hidden".into()].into_iter().collect(),
        );
        let hidden: AddressBase = "local:hidden".into();
        let escaped: AddressBase = "local:escaped".into();
        let cell = Address::symbolic(Variable(93_101));
        let base = SymbolicMemory::new()
            .with_block(hidden.clone(), 4)
            .with_block(escaped.clone(), 4);
        let project = |memory: SymbolicMemory| {
            crate::kernel::memory_history::canonical_projected_load_memory(
                &crate::kernel::intern_memory(memory),
                &cell,
            )
        };
        let after_hidden = base.without_local_block(&hidden);
        let after_escaped = base.without_local_block(&escaped);
        assert_ne!(after_hidden, base, "the states differ by the retired local");
        assert_eq!(
            project(after_hidden),
            project(base.clone()),
            "an unreachable retired local is not part of the read's projection"
        );
        assert_ne!(
            project(after_escaped),
            project(base),
            "a load through the pointer may observe a reachable retired local"
        );
    }

    #[test]
    fn a_loaded_pointer_cannot_reach_storage_created_after_the_read() {
        let storage = AddressBase::Heap(8710);
        let early: AddressBase = "local:early_object".into();
        let later: AddressBase = "local:later_object".into();
        let cell = Address::new(storage.clone(), AddressOffset::constant(0));
        let memory = SymbolicMemory::new()
            .with_block(storage.clone(), 16)
            .with_block(early.clone(), 4);
        let value_type = ProgramType::Int32Pointer;
        let assumptions = PureFactContext::new()
            .assume_proposition(Proposition::MemoryReadDefined {
                point: Default::default(),
                at: None,
                memory: memory.clone(),
                pointer: cell.clone(),
                value_type,
            })
            .assume_proposition(Proposition::MemoryLoadable {
                point: Default::default(),
                memory: memory.clone(),
                base: cell.clone(),
                bytes: (OldMachineTerm::constant(8)).into(),
                wide: false,
            });
        let paths = evaluate_spec_memory_load_paths(
            &memory,
            cell,
            value_type,
            Vec::new().into(),
            Vec::new(),
            &assumptions,
        );
        let [path] = paths.as_slice() else {
            panic!("one typed read expected");
        };
        let ExpressionOutcome::Value(ProgramValue::Pointer(value)) = &path.outcome else {
            panic!("pointer value expected");
        };
        let loaded = &value.address().base;
        assert!(loaded.proven_distinct(&later));
        assert!(later.proven_distinct(loaded));
        assert!(!loaded.proven_distinct(&early));
        // The same holds for a heap identity the read's state never
        // handed out, and not for one it already holds.
        assert!(loaded.proven_distinct(&AddressBase::Heap(8711)));
        assert!(AddressBase::Heap(8711).proven_distinct(loaded));
        assert!(!loaded.proven_distinct(&storage));
    }

    #[test]
    fn unknown_pointer_in_fresh_storage_does_not_inherit_storage_provenance() {
        for block in [AddressBase::Heap(8700), AddressBase::Temporary(8701)] {
            for offset in [0, 8] {
                let cell = Address::new(block.clone(), AddressOffset::constant(offset));
                // Another allocation live at the read, which the value may
                // point into as well as anything else that existed then.
                let memory = SymbolicMemory::new()
                    .with_block(block.clone(), 16)
                    .with_block(AddressBase::Heap(8702), 16);
                let value_type = ProgramType::Int32Pointer;
                let assumptions = PureFactContext::new()
                    .assume_proposition(Proposition::MemoryReadDefined {
                        point: Default::default(),
                        at: None,
                        memory: memory.clone(),
                        pointer: cell.clone(),
                        value_type,
                    })
                    .assume_proposition(Proposition::MemoryLoadable {
                        point: Default::default(),
                        memory: memory.clone(),
                        base: cell.clone(),
                        bytes: (OldMachineTerm::constant(8)).into(),
                        wide: false,
                    });
                for logical in [false, true] {
                    let paths = if logical {
                        evaluate_logical_memory_load_paths(
                            &memory,
                            cell.clone(),
                            value_type,
                            Vec::new().into(),
                            Vec::new(),
                            &assumptions,
                        )
                    } else {
                        evaluate_spec_memory_load_paths(
                            &memory,
                            cell.clone(),
                            value_type,
                            Vec::new().into(),
                            Vec::new(),
                            &assumptions,
                        )
                    };
                    let [path] = paths.as_slice() else {
                        panic!("one typed read expected");
                    };
                    let ExpressionOutcome::Value(ProgramValue::Pointer(value)) = &path.outcome
                    else {
                        panic!("pointer value expected");
                    };
                    assert!(matches!(value.address().base, AddressBase::Load(_)));
                    assert_eq!(
                        value.address().as_loaded_value().unwrap().defining_address,
                        cell
                    );
                    assert!(
                        !value
                            .address()
                            .base
                            .proven_distinct(&AddressBase::Heap(8702))
                    );
                    assert_eq!(value.program_type(), value_type);
                }
                let bits = crate::kernel::OldMachineTerm::read_named(
                    ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
                    cell.clone(),
                    crate::kernel::LoadKind::Int32,
                );
                let mut facts = crate::kernel::ExecutionFacts::new();
                let cached = canonicalized_pointer_value_from_int_cell(
                    &memory,
                    &cell,
                    &ProgramValue::Int32(bits),
                    value_type,
                    &mut facts,
                    &assumptions,
                    None,
                    LoadPurpose::Validity,
                    None,
                )
                .unwrap();
                let ProgramValue::Pointer(cached) = cached else {
                    panic!("cached pointer expected");
                };
                assert!(matches!(cached.address().base, AddressBase::Load(_)));
                let target = Address::new(AddressBase::Heap(8702), AddressOffset::constant(0));
                let stored = memory.store(
                    cell.clone(),
                    ProgramValue::typed_pointer(target.clone(), value_type),
                );
                let paths = evaluate_logical_memory_load_paths(
                    &stored,
                    cell,
                    value_type,
                    Vec::new().into(),
                    Vec::new(),
                    &assumptions,
                );
                // The read names the cell; the pointer stored there is what
                // the read-over-write authority relates it to.
                assert!(
                    matches!(&paths[0].outcome, ExpressionOutcome::Value(ProgramValue::Pointer(value))
                    if pointer_read_over_write_value(value.address()).as_ref() == Some(&target)
                        && assumptions.equality_graph.knows_condition(
                            &OldConditionTerm::PointerEqual(
                                Box::new(value.clone()),
                                Box::new(Pointer::new(target.clone(), value_type)),
                            ), true,
                        ))
                );
            }
        }
    }

    #[test]
    fn logical_scalar_read_preserves_cached_offset_spelling() {
        let pointer = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::raw_add(
                AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(944_021)), 4),
                AddressOffset::constant(16),
            ),
        );
        let expected = ProgramValue::Int32(OldMachineTerm::constant(7));
        let memory = SymbolicMemory::new().store(pointer.clone(), expected.clone());
        let paths = evaluate_logical_memory_load_paths(
            &memory,
            pointer,
            ProgramType::Int32,
            Vec::new().into(),
            Vec::new(),
            &PureFactContext::new(),
        );
        assert_eq!(paths.len(), 1);
        let ExpressionOutcome::Value(value) = &paths[0].outcome else {
            panic!("a logical read has a value: {:?}", paths[0].outcome);
        };
        assert_eq!(read_over_write_program_value(value), expected);
    }

    #[test]
    fn unknown_pointer_in_local_storage_has_opaque_provenance_with_and_without_call_havoc() {
        for (offset, call_havoc) in [(0, false), (8, false), (0, true), (8, true)] {
            let cell = Address::new(
                "local:pointer-holder".into(),
                AddressOffset::constant(offset),
            );
            let target = Address::new("local:other-object".into(), AddressOffset::constant(0));
            let value_type = ProgramType::Int32Pointer;
            let before = SymbolicMemory::new()
                .with_block(target.base.clone(), 4)
                .with_block(cell.base.clone(), 16)
                .store(
                    cell.clone(),
                    ProgramValue::typed_pointer(target.clone(), value_type),
                );
            let range =
                MemoryRange::new_with_element_width(cell.clone(), 0u32.into(), 8u32.into(), 1);
            let assumptions = PureFactContext::new();
            let memory = if call_havoc {
                before.with_call_memory_havoc(Variable(944_014), &[range], &assumptions, None)
            } else {
                // A loop head can forget the field's value without adding a
                // call-havoc node. The storage address still says nothing
                // about the pointee's allocation identity.
                before.with_loop_memory_havoc_preserving_borrows(
                    Variable(944_014),
                    &BTreeSet::new(),
                    Some(&[range]),
                    None,
                )
            };
            assert!(memory.known_value(&cell).is_none());
            for logical in [false, true] {
                let paths = if logical {
                    evaluate_logical_memory_load_paths(
                        &memory,
                        cell.clone(),
                        value_type,
                        Vec::new().into(),
                        Vec::new(),
                        &assumptions,
                    )
                } else {
                    evaluate_spec_memory_load_paths(
                        &memory,
                        cell.clone(),
                        value_type,
                        Vec::new().into(),
                        Vec::new(),
                        &assumptions,
                    )
                };
                let [path] = paths.as_slice() else {
                    panic!("one typed read expected");
                };
                let ExpressionOutcome::Value(ProgramValue::Pointer(value)) = &path.outcome else {
                    panic!("pointer value expected");
                };
                assert!(matches!(value.address().base, AddressBase::Load(_)));
                assert_eq!(
                    value.address().as_loaded_value().unwrap().defining_address,
                    cell
                );
                assert!(!value.address().base.proven_distinct(&target.base));
            }
            let bits = crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
                cell.clone(),
                crate::kernel::LoadKind::Int32,
            );
            let cached = canonicalized_pointer_value_from_int_cell(
                &memory,
                &cell,
                &ProgramValue::Int32(bits),
                value_type,
                &mut ExecutionFacts::new(),
                &assumptions,
                None,
                LoadPurpose::Validity,
                None,
            )
            .unwrap();
            let ProgramValue::Pointer(cached) = cached else {
                panic!("cached pointer expected");
            };
            assert!(matches!(cached.address().base, AddressBase::Load(_)));
            assert!(!cached.address().base.proven_distinct(&target.base));
        }
    }

    #[test]
    fn indexed_load_uses_proven_alias_without_inventing_initialization() {
        let index = OldMachineTerm::Variable(Variable(839));
        let base = Address::new("local:indexed".into(), AddressOffset::constant(0));
        let pointer = base.with_offset(AddressOffset::add(
            AddressOffset::constant(4),
            AddressOffset::scale_int32(index.clone(), 4),
        ));
        let assumptions = PureFactContext::new().assume_condition(
            OldConditionTerm::equal(index, OldMachineTerm::constant(1)),
            true,
        );
        let memory = SymbolicMemory::new()
            .with_block(base.base.clone(), 12)
            .store(base.offset_by_bytes(4), int32(3));
        for initialized in [false, true] {
            let memory = if initialized {
                memory.clone().store(base.offset_by_bytes(8), int32(7))
            } else {
                memory.clone()
            };
            let paths = evaluate_memory_load_paths(
                &memory,
                pointer.clone(),
                ProgramType::Int32,
                Vec::new().into(),
                Vec::new(),
                &assumptions,
                false,
                false,
                None,
                None,
            );
            assert_eq!(paths.len(), 1);
            assert_eq!(
                paths[0].outcome,
                if initialized {
                    ExpressionOutcome::Value(int32(7))
                } else {
                    ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead)
                }
            );
            assert!(paths[0].facts.is_empty());
        }
    }

    fn test_load_source(occurrence: u32) -> LoadSourceId {
        LoadSourceId {
            owner: LoadSourceOwnerId {
                source_unit: std::sync::Arc::from("load-source.c"),
                function: std::sync::Arc::from("read"),
            },
            occurrence,
            reference_access: None,
        }
    }

    #[test]
    fn alias_cache_keys_answers_by_assumption_context() {
        let left = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::variable(Variable(810)),
        );
        let right = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::variable(Variable(811)),
        );
        let mut cache = MemoryLoadAliasCache::default();
        let empty = PureFactContext::new();
        assert!(!cache.resolution_equal(&left, &right, &empty));

        let equal = empty.assume_condition(
            OldConditionTerm::address_offset_equal(left.offset.clone(), right.offset.clone()),
            true,
        );
        assert!(cache.resolution_equal(&left, &right, &equal));
    }

    #[test]
    fn ancestor_named_load_does_not_cross_into_an_aliasing_fact_context() {
        let retained_index = OldMachineTerm::Variable(Variable(812));
        let written_index = OldMachineTerm::Variable(Variable(813));
        let read_index = OldMachineTerm::Variable(Variable(814));
        let at = |index| {
            Address::new(
                AddressBase::ExternalArgument,
                AddressOffset::scale_int32(index, 4),
            )
        };
        let retained = at(retained_index);
        let written = at(written_index.clone());
        let read = at(read_index.clone());

        // Keep one unresolved cell so the reduced load is still symbolic.
        // Dropping only the later, proven-distinct write then makes the
        // reduced memory structurally equal to this already-interned ancestor.
        let ancestor_memory = SymbolicMemory::new().store(retained, int32(1));
        let ancestor = intern_memory_ref(&ancestor_memory);
        let current = ancestor_memory.store(written.clone(), int32(2));
        let distinct = PureFactContext::new().assume_condition(
            OldConditionTerm::equal(read_index.clone(), written_index.clone()),
            false,
        );
        let aliasing = PureFactContext::new()
            .assume_condition(OldConditionTerm::equal(read_index, written_index), true);
        let mut cache = MemoryLoadAliasCache::default();

        let distinct_paths = evaluate_memory_load_paths_with_alias_cache(
            &current,
            read.clone(),
            ProgramType::Int32,
            Vec::new().into(),
            Vec::new(),
            &distinct,
            true,
            LoadPurpose::Validity,
            &mut cache,
            None,
            None,
        );
        let [distinct_path] = distinct_paths.as_slice() else {
            panic!("the decided distinct load should have one path");
        };
        let ExpressionOutcome::Value(ProgramValue::Int32(OldMachineTerm::MemoryLoad(
            named_memory,
            named_pointer,
            LoadKind::Int32,
        ))) = &distinct_path.outcome
        else {
            panic!("the unresolved distinct load should have a symbolic identity");
        };
        assert_eq!(*named_memory.point(), ProgramPoint::at(&ancestor));
        assert_eq!(*named_pointer.address(), read);

        // Reuse the same per-load cache deliberately. Its assumption-context
        // key must prevent the distinct answer, and therefore the ancestor
        // name, from leaking into the sibling context where the write aliases.
        let aliasing_paths = evaluate_memory_load_paths_with_alias_cache(
            &current,
            read,
            ProgramType::Int32,
            Vec::new().into(),
            Vec::new(),
            &aliasing,
            true,
            LoadPurpose::Validity,
            &mut cache,
            None,
            None,
        );
        let [aliasing_path] = aliasing_paths.as_slice() else {
            panic!("the decided aliasing load should have one path");
        };
        assert_eq!(aliasing_path.outcome, ExpressionOutcome::Value(int32(2)));
    }

    #[test]
    fn load_variable_names_keep_distinct_points_with_equal_memory() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = SymbolicMemory::new();
        let address = Address::symbolic(Variable(89_007));
        for kind in [LoadKind::Int32, LoadKind::Bits64] {
            let read = || {
                crate::kernel::OldMachineTerm::read_named(
                    ProgramPoint::starting_at(&memory).for_exact_read(),
                    address.clone(),
                    kind,
                )
            };
            let first = read();
            let second = read();
            let (first_name, first_definition) =
                load_variable_for_term(&first).expect("first read");
            let (second_name, second_definition) =
                load_variable_for_term(&second).expect("second read");
            assert_ne!(first_name, second_name);
            assert_eq!(first_definition, first);
            assert_eq!(second_definition, second);
            assert_eq!(
                registered_load_origin_term_for_variable(&first_name),
                Some(first.clone())
            );
            if kind == LoadKind::Bits64 {
                assert_eq!(latest_wide_load_observation(&first_name), Some(first));
                assert_eq!(latest_wide_load_observation(&second_name), Some(second));
            }
        }
    }

    #[test]
    fn minted_load_fact_carries_exact_producer_binding() {
        let memory = crate::kernel::intern_memory(SymbolicMemory::new());
        let pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(12));
        let load = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&memory),
            pointer.clone(),
            crate::kernel::LoadKind::Int32,
        );
        let (variable, canonical) = load_variable_for_term(&load).expect("load identity");
        let mut facts = crate::kernel::ExecutionFacts::new();
        record_load_variable_defining_fact(variable, canonical.clone(), &mut facts);
        assert_eq!(facts.len(), 1);
        let fact = &facts[0];
        assert!(matches!(
            fact.generated_load_binding(),
            Some(GeneratedLoadBinding::Exact {
                variable: recorded,
                retained_state,
                pointer: recorded_pointer,
                load: recorded_load,
                ..
            }) if *recorded == variable
                && *retained_state == MemoryStateIdentity::of(memory.memory())
                && recorded_pointer == &pointer
                && recorded_load == &canonical
        ));
    }

    #[test]
    fn structural_read_definitions_keep_the_read_carrier_width() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = intern_memory(SymbolicMemory::new());
        let pointer = Address::symbolic(Variable(299_301));
        for (kind, format) in [
            (LoadKind::Int8, MachineIntegerType::Int8),
            (LoadKind::UInt8, MachineIntegerType::UInt8),
            (LoadKind::Int16, MachineIntegerType::Int16),
            (LoadKind::UInt16, MachineIntegerType::UInt16),
            (LoadKind::Int32, MachineIntegerType::Int32),
            (LoadKind::UInt32, MachineIntegerType::Int32),
            (LoadKind::Bits64, MachineIntegerType::Int64),
            (LoadKind::Int128, MachineIntegerType::Int128),
            (LoadKind::UInt128, MachineIntegerType::UInt128),
        ] {
            let raw = crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(&memory),
                pointer.clone(),
                kind,
            );
            let (variable, descriptor) = load_variable_for_term(&raw).unwrap();
            let mut facts = ExecutionFacts::new();
            record_load_variable_defining_fact(variable, descriptor.clone(), &mut facts);
            let expected = Proposition::condition_is(
                OldConditionTerm::Compare {
                    format,
                    relation: CompareRelation::Equal,
                    left: Box::new(OldMachineTerm::Variable(variable)),
                    right: Box::new(descriptor),
                },
                true,
            );
            assert_eq!(facts[0].proposition(), &expected, "{kind:?}");
            assert!(is_load_variable_defining_fact(facts[0].proposition()));
            assert!(crate::kernel::is_verified_load_variable_defining_fact(
                facts[0].proposition()
            ));
            assert!(
                facts[0]
                    .clone()
                    .with_proposition(expected.clone())
                    .generated_load_binding()
                    .is_some()
            );
            PureFactContext::new()
                .assume_proposition(expected)
                .assume_execution_pure_fact(&facts[0]);
        }
    }

    #[test]
    fn structural_read_binding_rejects_changed_width_address_and_epoch() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = intern_memory(SymbolicMemory::new());
        let address = Address::symbolic(Variable(299_201));
        let raw = |pointer, kind| {
            crate::kernel::OldMachineTerm::read_named(ProgramPoint::at(&memory), pointer, kind)
        };
        let (variable, definition) =
            load_variable_for_term(&raw(address.clone(), LoadKind::Int32)).unwrap();
        let mut facts = ExecutionFacts::new();
        record_load_variable_defining_fact(variable, definition, &mut facts);
        let fact = &facts[0];
        assert!(
            fact.clone()
                .with_proposition(fact.proposition().clone())
                .generated_load_binding()
                .is_some()
        );
        for (pointer, kind) in [
            (address.clone(), LoadKind::UInt32),
            (address.clone(), LoadKind::Bits64),
            (address.offset_by_bytes(4), LoadKind::Int32),
        ] {
            let other = load_variable_for_term(&raw(pointer, kind)).unwrap().0;
            let changed = Proposition::condition_is(
                OldConditionTerm::equal(
                    OldMachineTerm::Variable(variable),
                    OldMachineTerm::Variable(other),
                ),
                true,
            );
            assert!(!crate::kernel::is_verified_load_variable_defining_fact(
                &changed
            ));
            assert!(
                fact.clone()
                    .with_proposition(changed)
                    .generated_load_binding()
                    .is_none()
            );
        }
        crate::kernel::primitives::start_fresh_memory_arena();
        // Keeping the old handle still names the old descriptor. Replacing
        // it with an equal-content descriptor from this new arena does not.
        let replacement = Proposition::condition_is(
            OldConditionTerm::equal(
                OldMachineTerm::Variable(variable),
                crate::kernel::OldMachineTerm::read_named(
                    ProgramPoint::at(&(intern_memory(SymbolicMemory::new()))),
                    Address::symbolic(Variable(299_201)),
                    LoadKind::Int32,
                ),
            ),
            true,
        );
        assert!(
            fact.clone()
                .with_proposition(replacement)
                .generated_load_binding()
                .is_none()
        );
    }

    #[test]
    fn repeated_mint_keeps_each_exact_source_observation_on_one_fact() {
        let memory = crate::kernel::intern_memory(SymbolicMemory::new());
        let pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(12));
        let load = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&memory),
            pointer,
            crate::kernel::LoadKind::Int32,
        );
        let (variable, canonical) = load_variable_for_term(&load).expect("load identity");
        let mut facts = crate::kernel::ExecutionFacts::new();
        let first = test_load_source(0);
        let second = test_load_source(1);
        record_load_variable_defining_fact_with_source(
            variable,
            canonical.clone(),
            &mut facts,
            Some(&first),
        );
        record_load_variable_defining_fact_with_source(
            variable,
            canonical,
            &mut facts,
            Some(&second),
        );
        assert_eq!(facts.len(), 1);
        let fact = &facts[0];
        assert_eq!(fact.generated_load_source_events().len(), 2);
        assert_eq!(fact.generated_load_source_events()[0].source(), &first);
        assert_eq!(fact.generated_load_source_events()[1].source(), &second);
    }

    #[test]
    fn transported_equal_equation_from_a_new_epoch_drops_producer_source_events() {
        let pointer = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(20));
        let first_memory = crate::kernel::intern_memory(SymbolicMemory::new());
        let first_load = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&first_memory),
            pointer.clone(),
            crate::kernel::LoadKind::Int32,
        );
        let mut facts = crate::kernel::ExecutionFacts::new();
        let source = test_load_source(0);
        let variable = mint_load_variable(
            &first_load,
            &mut facts,
            &PureFactContext::new(),
            Some(&source),
        )
        .expect("load identity");
        assert_eq!(facts.len(), 1);
        let produced = &facts[0];
        assert!(produced.generated_load_binding().is_some());
        assert_eq!(produced.generated_load_source_events().len(), 1);
        // Exercise the raw descriptor form too: a proposition carried into a
        // new epoch must not carry producer authority.
        let fact = ExecutionPureFact::certified(Proposition::condition_is(
            OldConditionTerm::equal(OldMachineTerm::Variable(variable), first_load),
            true,
        ))
        .with_generated_load_binding(produced.generated_load_binding().unwrap().clone())
        .with_generated_load_source_event(produced.generated_load_source_events()[0].clone());

        // A fresh arena represents a new epoch. Its empty SymbolicMemory is
        // structurally equal to the first one, but its state identity is
        // different, and a read is its interned load: the read of the same
        // cell in the new epoch is another term.
        crate::kernel::primitives::start_fresh_memory_arena();
        let second_memory = crate::kernel::intern_memory(SymbolicMemory::new());
        let second_load = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&second_memory),
            pointer,
            crate::kernel::LoadKind::Int32,
        );
        let replacement = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(variable)),
                right: Box::new(second_load),
            },
            true,
        );
        assert_ne!(fact.proposition(), &replacement);
        assert_ne!(
            MemoryStateIdentity::of(first_memory.memory()),
            MemoryStateIdentity::of(second_memory.memory())
        );
        let transported = fact.clone().with_proposition(replacement);
        assert!(transported.generated_load_binding().is_none());
        assert!(transported.generated_load_source_events().is_empty());
    }

    /// A symbolic index over many concrete cells splits into a case per cell
    /// on one stack frame. The split used to recurse once per cell, and a
    /// file-scope array of a thousand elements overflowed the main thread's
    /// stack; a few hundred cells do the same on this small one.
    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 0.6s in the parallel gate"]
    fn a_symbolic_load_over_many_undecided_cells_splits_without_recursing() {
        const CELLS: u32 = 400;
        let paths = std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(|| {
                let block = AddressBase::from("global:split_table");
                let mut memory = SymbolicMemory::new().with_block(block.clone(), CELLS * 4);
                for index in 0..CELLS {
                    memory = memory.store(
                        Address::new(block.clone(), AddressOffset::constant(i64::from(index) * 4)),
                        int32(index),
                    );
                }
                let pointer = Address::new(
                    block,
                    AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(841)), 4),
                );
                evaluate_memory_load_paths(
                    &memory,
                    pointer,
                    ProgramType::Int32,
                    Vec::new().into(),
                    Vec::new(),
                    &PureFactContext::new(),
                    false,
                    false,
                    None,
                    None,
                )
                .into_iter()
                .map(|path| path.outcome)
                .collect::<Vec<_>>()
            })
            .expect("spawn the small-stack load")
            .join()
            .expect("the split must not overflow a small stack");
        // One aliasing case per cell, in cell order, then the case distinct
        // from every cell.
        assert_eq!(paths.len(), CELLS as usize + 1, "{:?}", paths.last());
        for (index, outcome) in paths.iter().take(CELLS as usize).enumerate() {
            assert_eq!(
                outcome,
                &ExpressionOutcome::Value(int32(u32::try_from(index).unwrap()))
            );
        }
    }

    fn logical_pointer_read(
        memory: &SymbolicMemory,
        address: &Address,
        context: &PureFactContext,
    ) -> Address {
        let paths = evaluate_logical_memory_load_paths(
            memory,
            address.clone(),
            ProgramType::Int64Pointer,
            Vec::new().into(),
            Vec::new(),
            context,
        );
        let [path] = paths.as_slice() else {
            panic!("one logical read expected");
        };
        assert!(
            !path.facts.has_path_conditions(),
            "logical read must not add path conditions"
        );
        assert!(
            path.obligations.is_empty(),
            "logical terms grant no read authority"
        );
        let ExpressionOutcome::Value(ProgramValue::Pointer(value)) = &path.outcome else {
            panic!("pointer value expected");
        };
        value.address().clone()
    }

    #[test]
    fn logical_pointer_field_alias_keeps_loaded_supplier_base_after_call() {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = Address::symbolic(Variable(955_920))
            .offset_by_elements(OldMachineTerm::Variable(Variable(955_921)), 4);
        let alias = Address::symbolic(Variable(955_922));
        let target = Address::symbolic(Variable(955_923));
        let right = owner.offset_by_bytes(8);
        let before = SymbolicMemory::new().store(
            right.clone(),
            ProgramValue::typed_pointer(target.clone(), ProgramType::Int64Pointer),
        );
        let bare = PureFactContext::new();
        let write = MemoryRange::new_with_element_width(owner.clone(), 0u32.into(), 2u32.into(), 4);
        let memory = before.with_call_memory_havoc(Variable(955_924), &[write], &bare, None);
        let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::view_memory(
            MemoryRange::new_with_element_width(owner.clone(), 2u32.into(), 4u32.into(), 4),
        ));
        resources.synchronize_memory_equalities(&bare);
        let without_alias = bare
            .clone()
            .assume_proposition(Proposition::ResourceComposition(resources));
        let context = without_alias.clone().assume_condition(
            OldConditionTerm::address_equal(owner.clone(), alias.clone()),
            true,
        );
        let read = |memory: &SymbolicMemory, address: Address, context: &PureFactContext| {
            let paths = evaluate_logical_memory_load_paths(
                memory,
                address,
                ProgramType::Int64Pointer,
                ExecutionFacts::new(),
                Vec::new(),
                context,
            );
            let [path] = paths.as_slice() else {
                panic!("one logical read");
            };
            path.outcome.clone()
        };
        let pointer = |outcome: &ExpressionOutcome| match outcome {
            ExpressionOutcome::Value(ProgramValue::Pointer(value)) => value.address().clone(),
            outcome => panic!("a pointer read, not {outcome:?}"),
        };
        // A logical read keeps the address it was written with and names its
        // version; the pointer stored there is related to it by memory alone.
        let direct = pointer(&read(&memory, right.clone(), &context));
        assert_eq!(pointer_read_over_write_value(&direct), Some(target));
        // A read through the alias is another name for the same cell, which
        // only the alias fact relates, through the frame it needs.
        let proven_equal =
            crate::kernel::reasoning::memory_resolution::pointers_proven_equal_for_memory_resolution;
        let through_alias = pointer(&read(&memory, alias.offset_by_bytes(8), &context));
        assert_ne!(through_alias, direct);
        assert!(proven_equal(&through_alias, &direct, &context));
        let without = pointer(&read(&memory, alias.offset_by_bytes(8), &without_alias));
        assert!(!proven_equal(&without, &direct, &without_alias));
        let past = pointer(&read(&memory, alias.offset_by_bytes(16), &context));
        assert!(!proven_equal(&past, &direct, &context));
        let changed = memory.store(
            right,
            ProgramValue::typed_pointer(
                Address::symbolic(Variable(955_925)),
                ProgramType::Int64Pointer,
            ),
        );
        let updated = pointer(&read(&changed, alias.offset_by_bytes(8), &context));
        assert!(proven_equal(
            &updated,
            &pointer(&read(&changed, owner.offset_by_bytes(8), &context)),
            &context
        ));
        assert!(!proven_equal(&updated, &direct, &context));
        assert!(!ResourceContext::new().permits_memory_read(
            &alias.offset_by_bytes(8),
            8,
            &context
        ));
    }

    #[test]
    fn symbolic_logical_wide_reads_keep_their_term_under_alias_facts() {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = Address::symbolic(Variable(989_960));
        let alias = Address::symbolic(Variable(989_961));
        let memory = SymbolicMemory::new().store(
            slot.clone(),
            ProgramValue::UInt64(OldMachineTerm::uint64_constant(7)),
        );
        let empty = PureFactContext::new()
            .allow_symbolic_contract_loads()
            .prefer_symbolic_external_loads()
            .keep_spec_loads_symbolic();
        let facts = empty
            .clone()
            .assume_condition(OldConditionTerm::address_equal(slot, alias.clone()), true);
        let read = |context: &PureFactContext| {
            let paths = evaluate_logical_memory_load_paths(
                &memory,
                alias.clone(),
                ProgramType::UInt64,
                ExecutionFacts::new(),
                Vec::new(),
                context,
            );
            let [path] = paths.as_slice() else {
                panic!("one logical read: {paths:?}");
            };
            path.outcome.clone()
        };
        assert_eq!(read(&facts), read(&empty));
    }

    #[test]
    fn indexed_scalar_read_keeps_cover_hits_and_other_alias_lines() {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::variable(Variable(95_010)),
        );
        let memory = SymbolicMemory::new()
            .with_constant_run(owner.clone(), ProgramType::Int32, 8, int32(7))
            .expect("compact constant cells");
        let indexed = owner.with_offset(AddressOffset::add(
            owner.offset.clone(),
            AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(95_011)), 4),
        ));
        let alias = owner.with_offset(AddressOffset::variable(Variable(95_012)));
        let context = PureFactContext::new()
            .allow_symbolic_contract_loads()
            .assume_condition(
                OldConditionTerm::equal(
                    OldMachineTerm::Variable(Variable(95_011)),
                    OldMachineTerm::constant(3),
                ),
                true,
            )
            .assume_condition(
                OldConditionTerm::address_equal(alias.clone(), owner.offset_by_bytes(12)),
                true,
            );
        for pointer in [indexed, alias] {
            assert!(memory.known_retained_value(&pointer).is_none());
            let paths = evaluate_memory_load_paths(
                &memory,
                pointer,
                ProgramType::Int32,
                ExecutionFacts::new(),
                Vec::new(),
                &context,
                true,
                false,
                None,
                None,
            );
            let [path] = paths.as_slice() else {
                panic!("expected one scalar program read: {paths:?}");
            };
            assert_eq!(path.outcome, ExpressionOutcome::Value(int32(7)));
        }
    }

    #[test]
    fn program_and_logical_reads_through_an_opaque_alias_are_equal_in_the_graph() {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(95_000)), 4),
        );
        let alias = Address::symbolic(Variable(95_001));
        let memory = SymbolicMemory::new();
        let empty = PureFactContext::new();
        let resources = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                owner.clone(),
                0u32.into(),
                1u32.into(),
                8,
            )),
        );
        let without_alias = empty
            .assume_proposition(Proposition::ResourceComposition(resources))
            .assume_proposition(Proposition::MemoryReadDefined {
                point: Default::default(),
                at: None,
                memory: memory.clone(),
                pointer: alias.clone(),
                value_type: ProgramType::UInt64,
            })
            .assume_proposition(Proposition::MemoryLoadable {
                point: Default::default(),
                memory: memory.clone(),
                base: alias.clone(),
                bytes: 8u32.into(),
                wide: false,
            });
        let context = without_alias.clone().assume_condition(
            OldConditionTerm::address_equal(owner.clone(), alias.clone()),
            true,
        );
        let logical = evaluate_logical_memory_load_paths(
            &memory,
            alias.clone(),
            ProgramType::UInt64,
            Vec::new().into(),
            Vec::new(),
            &context,
        );
        let program = evaluate_memory_load_paths(
            &memory,
            alias.clone(),
            ProgramType::UInt64,
            Vec::new().into(),
            Vec::new(),
            &context,
            true,
            false,
            None,
            None,
        );
        assert_eq!(logical.len(), 1);
        assert_eq!(program.len(), 1);
        let numeric = |outcome: &ExpressionOutcome| match outcome {
            ExpressionOutcome::Value(value) => {
                crate::kernel::spec::program_value_bitvector_term(value.numeric_value())
                    .expect("a scalar read")
            }
            _ => panic!("the read should denote a scalar value"),
        };
        // The logical read keeps its written address: its term is the same
        // whether or not the alias is known (lowering is fact-stable).
        let unrelated = evaluate_logical_memory_load_paths(
            &memory,
            alias.clone(),
            ProgramType::UInt64,
            Vec::new().into(),
            Vec::new(),
            &without_alias,
        );
        assert_eq!(unrelated[0].outcome, logical[0].outcome);
        // The C read selects the owned footprint's coordinates. The alias
        // makes the two reads equal in the graph; without it they are not.
        assert!(
            context
                .equality_graph
                .are_uint64_equal(&numeric(&program[0].outcome), &numeric(&logical[0].outcome))
        );
        let program_without_alias = evaluate_memory_load_paths(
            &memory,
            alias.clone(),
            ProgramType::UInt64,
            Vec::new().into(),
            Vec::new(),
            &without_alias,
            true,
            false,
            None,
            None,
        );
        // Without the alias the C read has no footprint to select either:
        // it is the same plain read.
        assert_eq!(program_without_alias[0].outcome, unrelated[0].outcome);
        let displaced = evaluate_logical_memory_load_paths(
            &memory,
            owner.offset_by_bytes(8),
            ProgramType::UInt64,
            Vec::new().into(),
            Vec::new(),
            &context,
        );
        assert!(
            !context.equality_graph.are_uint64_equal(
                &numeric(&displaced[0].outcome),
                &numeric(&logical[0].outcome)
            ),
            "different field offsets must retain different load identities"
        );
    }

    #[test]
    fn logical_pointer_read_definitions_are_not_hypotheses_or_read_authority() {
        let memory = SymbolicMemory::new();
        let a = Address::symbolic(Variable(92_200));
        let b = Address::symbolic(Variable(92_201));
        let before = PureFactContext::new();
        let sibling = before.clone();
        let x = logical_pointer_read(&memory, &a, &before);
        let y = logical_pointer_read(&memory, &b, &before);
        assert!(before.pure_facts().is_empty());
        assert!(!before.pointers_known_equal(&x, &y));
        let branch = before
            .clone()
            .assume_condition(OldConditionTerm::address_equal(a.clone(), b.clone()), true);
        assert!(branch.pointers_known_equal(&x, &y));
        assert!(!sibling.pointers_known_equal(&x, &y));
        assert!(!before.pointers_known_equal(&x, &y));
        assert!(!ResourceContext::new().permits_memory_read(&b, 8, &branch));
        let changed = memory.store(
            a.clone(),
            ProgramValue::typed_pointer(
                Address::symbolic(Variable(92_202)),
                ProgramType::Int64Pointer,
            ),
        );
        let z = logical_pointer_read(&changed, &a, &branch);
        assert!(!branch.pointers_known_equal(&x, &z));
        assert!(!branch.pointers_known_equal(&x, &x.offset_by_bytes(8)));
        // Definitions survive reconstruction, but the required address fact
        // must still be supplied by the new context itself.
        let reconstructed = PureFactContext::new()
            .assume_condition(OldConditionTerm::address_equal(a.clone(), b.clone()), true);
        assert!(reconstructed.pointers_known_equal(&x, &y));
        assert_eq!(reconstructed.pure_facts().len(), 1);
    }

    /// One cell's load answers its store the same way whichever selection
    /// of its version point built it first: the stored pointer is asked of
    /// the point's index, not read off the first selection's kind.
    #[test]
    fn a_loads_stored_pointer_does_not_depend_on_which_selection_built_it() {
        let slot = SymbolicMemory::local_pointer("selection_order_slot");
        let address = Address::symbolic(Variable(210_290));
        let value_type = ProgramType::Int32Pointer;
        let stored_pointer = |exact_first: bool| {
            let _session = crate::kernel::VerificationSession::enter();
            let initial = ExecutionState::new()
                .with_memory(SymbolicMemory::new().with_block(slot.base.clone(), 8));
            let stored = initial.clone().with_memory(initial.memory().clone().store(
                slot.clone(),
                ProgramValue::typed_pointer(address.clone(), value_type),
            ));
            // The memory no longer shows the cell, so only the index answers.
            let forgotten =
                stored
                    .clone()
                    .with_memory(stored.memory().without_possible_aliasing_cells(
                        &slot,
                        8,
                        &PureFactContext::new(),
                    ));
            assert!(forgotten.memory().known_value(&slot).is_none());
            let point = forgotten.program_point();
            let exact = point.clone().for_exact_read();
            let indexed = point.for_indexed_cell_read();
            assert_eq!(exact.read_key(), indexed.read_key());
            let (first, second) = if exact_first {
                (exact, indexed)
            } else {
                (indexed, exact)
            };
            let load = Load::at(first, &slot);
            assert_eq!(
                Load::at(second, &slot),
                load,
                "one point and cell, one load"
            );
            loaded_pointer_stored_address(&load, PointerLoadCategory::of_type(value_type))
        };
        assert_eq!(stored_pointer(true), Some(address.clone()));
        assert_eq!(stored_pointer(false), Some(address));
    }

    #[test]
    fn exact_pointer_address_uses_its_recorded_store_after_cache_forgetting() {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = SymbolicMemory::local_pointer("pointer_slot");
        let address = Address::symbolic(Variable(210_280)).offset_by_bytes(4);
        let value_type = ProgramType::Int32Pointer;
        let bytes = value_type.byte_width();
        let initial = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(slot.base.clone(), bytes));
        let stored = initial.clone().with_memory(initial.memory().clone().store(
            slot.clone(),
            ProgramValue::typed_pointer(address.clone(), value_type),
        ));
        let forgotten =
            stored
                .clone()
                .with_memory(stored.memory().without_possible_aliasing_cells(
                    &slot,
                    bytes,
                    &PureFactContext::new(),
                ));
        assert!(forgotten.memory().known_value(&slot).is_none());
        let read = |state: &ExecutionState, value_type| {
            let pointer =
                Pointer::from_point_read(state.program_point().for_exact_read(), value_type, &slot);
            let AddressBase::Load(load) = pointer.address().base.clone() else {
                panic!("an exact pointer read has a point-named identity");
            };
            load
        };
        // The load's identity is its point and cell, not the type that
        // decodes it (`design/loads.md`): the `int32 *` store answers a
        // `uint32 *` read of the cell, and no function-pointer decoding of
        // that same load.
        let function = ProgramType::FunctionPointer(crate::kernel::CallbackSignature::UNSPECIFIED);
        let load = read(&forgotten, ProgramType::UInt32Pointer);
        assert_eq!(read(&forgotten, function), load, "one cell is one load");
        assert_eq!(
            loaded_pointer_stored_address(&load, PointerLoadCategory::of_type(value_type)),
            Some(address.clone())
        );
        assert!(
            loaded_pointer_stored_address(&load, PointerLoadCategory::of_type(function)).is_none()
        );

        let other = SymbolicMemory::local_pointer("unrelated_word");
        let work = [1, 8, 64, 256].map(|count| {
            let mut state = forgotten.clone();
            for bits in 0..count {
                state = state.clone().with_memory(state.memory().clone().store(
                    other.clone(),
                    ProgramValue::Int32(OldMachineTerm::constant(bits)),
                ));
            }
            let load = read(&state, value_type);
            let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
                loaded_pointer_stored_address(&load, None)
            });
            assert_eq!(resolved.as_ref(), Some(&address));
            work
        });
        assert!(work.iter().all(|units| *units <= work[0] + 8), "{work:?}");
    }

    #[test]
    fn typed_read_validity_accepts_its_certified_pointer_equation() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Address::new(
            "global:defined-complete-pointer".into(),
            AddressOffset::constant(0),
        );
        let stored = ProgramValue::typed_pointer(
            Address::symbolic(Variable(210_290)),
            ProgramType::Int32Pointer,
        );
        // Forget the materialized cell without changing its stored value.
        // The typed read recovers the complete pointer, while the separately
        // recorded initialized bytes supply authority to read it.
        let memory = SymbolicMemory::new()
            .with_initialized_object(&field, 8)
            .store(field.clone(), stored.clone())
            .without_possible_aliasing_cells(
                &Address::symbolic(Variable(210_291)),
                8,
                &PureFactContext::new(),
            );
        assert!(memory.known_value(&field).is_none());
        let view = |bytes| {
            PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
                point: Default::default(),
                memory: memory.clone(),
                base: field.clone(),
                bytes: (OldMachineTerm::constant(bytes)).into(),
                wide: false,
            })
        };
        let context = view(8);
        let paths = evaluate_spec_memory_load_paths(
            &memory,
            field.clone(),
            ProgramType::Int32Pointer,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
        );
        let [path] = paths.as_slice() else {
            panic!("one typed read expected");
        };
        assert_eq!(path.outcome, ExpressionOutcome::Value(stored));
        assert!(path.obligations.is_empty());
        assert_eq!(path.facts.len(), 1);
        assert!(path.facts[0].is_logical_read_equation());
        assert!(!context.proves_exact(path.facts[0].proposition()));
        assert!(!is_load_variable_defining_fact(path.facts[0].proposition()));
        let before = context.fact_counts();
        assert!(context.proves_memory_read_defined(
            &memory,
            &Default::default(),
            &field,
            ProgramType::Int32Pointer
        ));
        assert_eq!(context.fact_counts(), before);
        // Recovering a value and its equation grants no missing read span.
        assert!(!PureFactContext::new().proves_memory_read_defined(
            &memory,
            &Default::default(),
            &field,
            ProgramType::Int32Pointer,
        ));
        assert!(!view(4).proves_memory_read_defined(
            &memory,
            &Default::default(),
            &field,
            ProgramType::Int32Pointer
        ));
    }

    #[test]
    fn a_symbolic_pointer_read_recovers_the_complete_stored_value() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Address::new(
            "global:symbolic-complete-pointer".into(),
            AddressOffset::constant(0),
        );
        let target = Address::symbolic(Variable(210_190));
        let class = crate::kernel::effective_type::CAccessClass::Scalar(
            crate::kernel::effective_type::CScalarClass::Int,
        );
        let stored = Pointer::new(target.clone(), ProgramType::Int32Pointer)
            .with_bounds(Some(SubobjectBounds::new(target, 4u32.into())))
            .with_object_class(Some(class.clone()));
        let context = PureFactContext::new();
        let memory = SymbolicMemory::new()
            .store(field.clone(), ProgramValue::Pointer(stored.clone()))
            .without_possible_aliasing_cells(&Address::symbolic(Variable(210_191)), 8, &context);
        assert!(memory.known_value(&field).is_none());
        let read = |memory: &SymbolicMemory| {
            let mut facts = ExecutionFacts::new();
            let ProgramValue::Pointer(value) = canonicalized_symbolic_load_value_with_identity(
                memory,
                None,
                &field,
                ProgramType::Int32Pointer,
                &mut facts,
                &context,
                None,
                LoadPurpose::Logical,
            )
            .unwrap() else {
                panic!("pointer read")
            };
            (value, facts)
        };
        let (value, facts) = read(&memory);
        // Naming stays structural; the graph retains the complete stored
        // pointer, including the provenance, bounds, and access class.
        assert_ne!(value.address(), stored.address());
        assert_eq!(value.provenance(), value.address());
        assert!(context.equality_graph.knows_condition(
            &OldConditionTerm::PointerEqual(Box::new(value.clone()), Box::new(stored.clone())),
            true,
        ));
        assert_eq!(
            pointer_read_over_write_value(value.address()),
            Some(stored.address().clone())
        );
        assert_eq!(
            context
                .equality_graph
                .pointer_value_representative(&value)
                .object_class(),
            Some(class)
        );
        // One equation relates the read to the stored value, and one the
        // state's raw read to the read.
        assert_eq!(facts.len(), 2);
        for fact in facts.iter() {
            assert!(fact.is_logical_read_equation());
            fact.retain_pointer_read_definition(&context);
        }
        let current = Pointer::new(
            Address::loaded_value(&crate::kernel::intern_memory_ref(&memory), &field),
            ProgramType::Int32Pointer,
        );
        assert!(context.pointer_provenance_match(&current, &stored));
        assert!(context.pointers_known_equal(current.address(), stored.address()));
        assert!(context.pure_facts().is_empty());
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_term(stored.address()).is_none()
        );
        let partial = memory.store(field.offset_by_bytes(4), ProgramValue::UInt32(0u32.into()));
        assert!(!context.pointer_provenance_match(&read(&partial).0, &stored));
    }

    #[test]
    fn a_pointer_cast_restores_complete_word_reads_inside_a_numeric_observation() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Address::new("global:scoped-word".into(), AddressOffset::constant(0));
        let target = Address::symbolic(Variable(210_199));
        let pointer = Pointer::new(target.clone(), ProgramType::Int32Pointer)
            .with_bounds(Some(SubobjectBounds::constant(target.clone(), 4)));
        let stored = ProgramValue::PointerInteger(PointerIntegerValue {
            numeric: Box::new(ProgramValue::UInt64(OldMachineTerm::integer_address(
                target,
            ))),
            pointer: Box::new(pointer.clone()),
            kind: PointerIntegerKind::Exact,
        });
        let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new_with_element_width(field.clone(), 0u32.into(), 1u32.into(), 8),
        ));
        let state = ExecutionState::new()
            .with_memory(SymbolicMemory::new().store(field.clone(), stored))
            .with_resource_context(resources)
            .with_local(
                "word",
                ProgramValue::typed_pointer(field, ProgramType::UInt64Pointer),
            );
        let context = PureFactContext::new();
        {
            let _numeric = WordRepresentationScope::enter(false);
            let paths = evaluate_program_expression_paths(
                &state,
                &crate::kernel::program_expression::cast(
                    ProgramExpression::Load(Box::new(crate::kernel::program_expression::variable(
                        "word",
                    ))),
                    ProgramType::Int32Pointer,
                ),
                &context,
                &mut ExecutionBudget::default(),
            )
            .unwrap();
            assert_eq!(paths.len(), 1);
            assert_eq!(
                paths[0].outcome,
                ExpressionOutcome::Value(ProgramValue::Pointer(pointer))
            );
            assert!(!WordRepresentationScope::keeps_representation());
        }
        assert!(WordRepresentationScope::keeps_representation());
    }

    #[test]
    fn a_symbolic_word_read_recovers_only_a_complete_stored_pointer_record() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Address::new("global:symbolic-word".into(), AddressOffset::constant(0));
        let target = Address::symbolic(Variable(210_192));
        let pointer = Pointer::new(target.clone(), ProgramType::Int32Pointer)
            .with_bounds(Some(SubobjectBounds::new(target.clone(), 4u32.into())));
        let context = PureFactContext::new();
        let read = |memory: &SymbolicMemory| {
            canonicalized_symbolic_load_value_with_identity(
                memory,
                None,
                &field,
                ProgramType::UInt64,
                &mut ExecutionFacts::new(),
                &context,
                None,
                LoadPurpose::Logical,
            )
            .unwrap()
        };
        for kind in [PointerIntegerKind::Exact, PointerIntegerKind::Tagged] {
            let bits = OldMachineTerm::integer_address(target.clone());
            let bits = if kind == PointerIntegerKind::Tagged {
                OldMachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::BitwiseOr,
                    left: Box::new(bits),
                    right: Box::new(OldMachineTerm::uint64_constant(1)),
                }
            } else {
                bits
            };
            let stored = ProgramValue::PointerInteger(PointerIntegerValue {
                numeric: Box::new(ProgramValue::UInt64(bits)),
                pointer: Box::new(pointer.clone()),
                kind,
            });
            let memory = SymbolicMemory::new()
                .store(field.clone(), stored.clone())
                .without_possible_aliasing_cells(
                    &Address::symbolic(Variable(210_193)),
                    8,
                    &context,
                );
            assert!(memory.known_value(&field).is_none());
            assert_eq!(read(&memory), stored);
            let partial = memory.store(
                field.clone().offset_by_bytes(4),
                ProgramValue::UInt32(0u32.into()),
            );
            assert_ne!(read(&partial), stored);
            let numeric =
                SymbolicMemory::new().store(field.clone(), stored.numeric_value().clone());
            let ProgramValue::PointerInteger(fresh) = read(&numeric) else {
                panic!("word read")
            };
            assert!(matches!(
                fresh.kind,
                PointerIntegerKind::Word { changed_bits: 0 }
            ));
            assert!(fresh.pointer.bounds().is_none());
        }
        assert!(context.pure_facts().is_empty());
    }

    #[test]
    fn explicit_numeric_word_frame_does_not_supply_pointer_origin() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Address::symbolic(Variable(210_194));
        let target = Address::symbolic(Variable(210_195));
        let pointer = Pointer::new(target.clone(), ProgramType::Int32Pointer)
            .with_bounds(Some(SubobjectBounds::new(target.clone(), 4u32.into())));
        let stored = ProgramValue::PointerInteger(PointerIntegerValue {
            numeric: Box::new(ProgramValue::UInt64(OldMachineTerm::integer_address(
                target,
            ))),
            pointer: Box::new(pointer.clone()),
            kind: PointerIntegerKind::Exact,
        });
        let before = SymbolicMemory::new().store(field.clone(), stored);
        // Forgetting a cache is not a write to the program's memory.
        let after = before.clone().without_possible_aliasing_cells(
            &Address::symbolic(Variable(210_196)),
            8,
            &PureFactContext::new(),
        );
        let (_, new, equality) = crate::kernel::tests::explicit_frame(
            &before,
            &after,
            &field,
            ProgramType::UInt64,
            &[Proposition::MemoryMutatesOnly {
                before: before.clone(),
                before_point: Default::default(),
                after: after.clone(),
                after_point: Default::default(),
                writes: vec![],
            }],
            &PureFactContext::new(),
        )
        .expect("the explicit empty footprint preserves the numeric word");
        let facts = PureFactContext::new().assume_proposition(equality);
        // Deliberately discard the representation record: a complete read
        // of unchanged memory legitimately retains it, independently of the
        // numeric equality. Only the bits are under test here.
        let recovered = super::cast_program_value_to_type(
            new.numeric_value().clone(),
            ProgramType::Int32Pointer,
            super::IntegerConversion::Modular,
            &mut Vec::new(),
            &facts,
        );
        match recovered {
            Err(RuntimeError::PointerConversion(_)) => {}
            Ok(ProgramValue::Pointer(recovered)) => assert!(
                !facts.pointer_provenance_match(&recovered, &pointer),
                "numeric equality alone cannot supply the original pointer bounds"
            ),
            other => panic!("unexpected numeric cast result: {other:?}"),
        }
    }

    #[test]
    fn a_cached_scalar_prefix_recovers_only_the_complete_stored_pointer() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Address::new("global:cached-pointer-a".into(), AddressOffset::constant(0));
        let other = Address::new("global:cached-pointer-b".into(), AddressOffset::constant(0));
        let address = Address::symbolic(Variable(210_172));
        let stored = Pointer::new(address.clone(), ProgramType::Int32Pointer)
            .with_bounds(Some(SubobjectBounds::new(address, 4u32.into())));
        let memory = SymbolicMemory::new()
            .store(field.clone(), ProgramValue::Pointer(stored.clone()))
            .store(other.clone(), ProgramValue::Pointer(stored.clone()));
        let memory = memory
            .without_possible_aliasing_cells(
                &Address::symbolic(Variable(210_173)),
                8,
                &PureFactContext::new(),
            )
            .materialize_symbolic_cell(field.clone(), ProgramType::Int32)
            .materialize_symbolic_cell(other.clone(), ProgramType::Int32);
        let context = PureFactContext::new();
        let read = |memory: &SymbolicMemory, field: &Address| {
            let prefix = memory.known_value(field).expect("cached prefix");
            assert!(matches!(prefix, ProgramValue::Int32(_)));
            let ProgramValue::Pointer(value) = canonicalized_pointer_value_from_int_cell(
                memory,
                field,
                &prefix,
                ProgramType::Int32Pointer,
                &mut ExecutionFacts::new(),
                &context,
                None,
                LoadPurpose::Program,
                None,
            )
            .unwrap() else {
                panic!("pointer read")
            };
            value
        };
        assert_eq!(read(&memory, &field), stored);
        assert_eq!(read(&memory, &other), stored);
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_term(stored.address()).is_none()
        );
        let overwritten = memory.store(
            field.clone().offset_by_bytes(4),
            ProgramValue::UInt32(0u32.into()),
        );
        let changed = read(&overwritten, &field);
        assert!(changed.bounds().is_none());
        assert!(!context.pointer_provenance_match(&changed, &stored));
    }

    #[test]
    fn a_pointer_read_through_a_cached_prefix_changes_with_its_upper_half() {
        // A pointer is the whole eight-byte cell. When only its lower four
        // bytes are cached, a store to the upper four bytes changes the
        // pointer, so the read after the store is not the read before it.
        let _session = crate::kernel::VerificationSession::enter();
        let field = Address::new("global:prefix-pointer".into(), AddressOffset::constant(0));
        let memory = SymbolicMemory::new()
            .materialize_symbolic_cell(field.clone(), ProgramType::Int32)
            .materialize_symbolic_cell(field.clone().offset_by_bytes(4), ProgramType::Int32);
        let context = PureFactContext::new();
        let read = |memory: &SymbolicMemory| {
            let prefix = memory.known_value(&field).expect("cached prefix");
            let ProgramValue::Pointer(value) = canonicalized_pointer_value_from_int_cell(
                memory,
                &field,
                &prefix,
                ProgramType::Int32Pointer,
                &mut ExecutionFacts::new(),
                &context,
                None,
                LoadPurpose::Program,
                None,
            )
            .unwrap() else {
                panic!("pointer read")
            };
            value
        };
        let before = read(&memory);
        let overwritten = memory.store(
            field.clone().offset_by_bytes(4),
            ProgramValue::UInt32(0u32.into()),
        );
        assert!(
            overwritten.known_value(&field).is_some(),
            "the lower half stays cached"
        );
        let after = read(&overwritten);
        assert_ne!(
            after.address(),
            before.address(),
            "the read after the upper-half store is a different pointer"
        );
    }

    #[test]
    fn checked_function_pointer_reads_reconcile_cached_aliases_without_leaking_evidence() {
        let _session = crate::kernel::VerificationSession::enter();
        let table = Address::new("global:callback-table".into(), AddressOffset::constant(0));
        let argument = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(210_510)), 4),
        );
        let target = Address::function("callback");
        let replacement = Address::function("replacement");
        let program_type = ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED);
        let memory = SymbolicMemory::new().store(
            table.offset_by_bytes(8),
            ProgramValue::typed_pointer(target.clone(), program_type),
        );
        let source = intern_memory_ref(&memory);
        let seeded = memory.clone().with_seeded_cells(
            argument.offset_by_bytes(8),
            4,
            program_type,
            0,
            2,
            source,
        );
        let bare = PureFactContext::new();
        let alias = Proposition::condition_is(
            OldConditionTerm::address_equal(argument.clone(), table.clone()),
            true,
        );
        let context = bare.clone().assume_proposition(alias.clone());
        let paths = evaluate_memory_load_paths(
            &seeded,
            argument.offset_by_bytes(8),
            program_type,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
            true,
            false,
            None,
            None,
        );
        let [path] = paths.as_slice() else {
            panic!("one checked read expected");
        };
        let ExpressionOutcome::Value(ProgramValue::Pointer(read)) = &path.outcome else {
            panic!("function pointer expected");
        };
        assert!(
            path.facts
                .iter()
                .any(|fact| fact.has_checked_pointer_read())
        );
        let known = path.facts.iter().fold(context.clone(), |context, fact| {
            context.assume_proposition(fact.proposition().clone())
        });
        let merged =
            crate::kernel::reasoning::merge_facts(&ExecutionFacts::new(), &path.facts, &known)
                .unwrap();
        assert!(merged.iter().any(|fact| fact.has_checked_pointer_read()));
        let plain: ExecutionFacts = path
            .facts
            .iter()
            .map(|fact| ExecutionPureFact::new(fact.proposition().clone()))
            .collect();
        assert!(
            crate::kernel::reasoning::merge_facts(&ExecutionFacts::new(), &plain, &known)
                .unwrap()
                .is_empty()
        );
        let mut published =
            crate::kernel::proof::PureFactStore::from_ordered(std::slice::from_ref(&alias));
        for fact in &path.facts {
            published = published.with_kernel_checked_fact(fact.proposition().clone());
        }
        let undecorated = published.clone();
        for fact in &path.facts {
            published.retain_checked_read_fact(fact);
        }
        assert!(
            published
                .assumptions()
                .pointers_known_equal(read.address(), &target)
        );
        assert!(
            !undecorated
                .assumptions()
                .pointers_known_equal(read.address(), &target)
        );
        assert!(!context.pointers_known_equal(read.address(), &target));
        for fact in &path.facts {
            fact.retain_pointer_read_definition(&context);
        }
        assert!(context.pointers_known_equal(read.address(), &target));
        assert!(!bare.pointers_known_equal(read.address(), &target));
        assert!(!ResourceContext::new().permits_memory_read(
            &argument.offset_by_bytes(8),
            8,
            &context
        ));
        let changed = memory.store(
            table.offset_by_bytes(8),
            ProgramValue::typed_pointer(replacement.clone(), program_type),
        );
        let changed_source = intern_memory_ref(&changed);
        let changed_seeded = changed.with_seeded_cells(
            argument.offset_by_bytes(8),
            4,
            program_type,
            0,
            2,
            changed_source,
        );
        let changed_paths = evaluate_memory_load_paths(
            &changed_seeded,
            argument.offset_by_bytes(8),
            program_type,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
            true,
            false,
            None,
            None,
        );
        let [changed_path] = changed_paths.as_slice() else {
            panic!("one changed read expected");
        };
        let ExpressionOutcome::Value(ProgramValue::Pointer(changed_read)) = &changed_path.outcome
        else {
            panic!("function pointer expected");
        };
        for fact in &changed_path.facts {
            fact.retain_pointer_read_definition(&context);
        }
        assert!(context.pointers_known_equal(changed_read.address(), &replacement));
        assert!(!context.pointers_known_equal(read.address(), changed_read.address()));
    }

    #[test]
    fn canonical_pointer_names_do_not_redefine_a_scalar_prefix_source() {
        // A cell caching a 4-byte scalar copied from `source` holds only a
        // prefix of a pointer: an 8-byte pointer read through it is not the
        // pointer read at `source`, whose name it must not take.
        let _session = crate::kernel::VerificationSession::enter();
        let base = SymbolicMemory::new();
        let source = Address::symbolic(Variable(940_095));
        let destination = Address::symbolic(Variable(940_096));
        let ProgramValue::Pointer(original) =
            base.symbolic_pointer_load(None, &source, ProgramType::Int32Pointer)
        else {
            unreachable!()
        };
        let source_word = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&(crate::kernel::intern_memory(base.clone()))),
            source.clone(),
            crate::kernel::LoadKind::Int32,
        );
        let (variable, _) = load_variable_for_term(&source_word).unwrap();
        let cached = base.store(
            destination.clone(),
            ProgramValue::Int32(OldMachineTerm::Variable(variable)),
        );
        let ProgramValue::Pointer(prefix) =
            cached.symbolic_pointer_load(None, &destination, ProgramType::Int32Pointer)
        else {
            unreachable!()
        };
        assert_ne!(prefix.address(), original.address());
        assert!(
            prefix
                .address()
                .as_loaded_value()
                .is_none_or(|read| read.defining_address != source),
            "{:?}",
            prefix.address()
        );
    }

    #[test]
    fn specification_pointer_reads_do_not_adopt_fact_supplied_bounds() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = SymbolicMemory::new();
        let address = Address::symbolic(Variable(989_920));
        let evaluate = |context: &PureFactContext| {
            let paths = evaluate_memory_load_paths(
                &memory,
                address.clone(),
                ProgramType::Int32Pointer,
                ExecutionFacts::new(),
                Vec::new(),
                context,
                true,
                false,
                None,
                None,
            );
            let ExpressionOutcome::Value(ProgramValue::Pointer(value)) = &paths[0].outcome else {
                panic!("pointer read");
            };
            value.clone()
        };
        let empty = PureFactContext::new();
        let value = evaluate(&empty);
        let bounded = value.clone().with_bounds(Some(SubobjectBounds::new(
            value.address().clone(),
            4u32.into(),
        )));
        let facts = empty.clone().assume_condition(
            OldConditionTerm::PointerEqual(Box::new(value.clone()), Box::new(bounded)),
            true,
        );
        let _scope = SpecificationReadScope::enter();
        assert_eq!(evaluate(&facts), evaluate(&empty));
    }

    #[test]
    fn specification_cached_pointer_value_does_not_follow_fact_supported_frames() {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = Address::symbolic(Variable(989_930));
        let write = Address::symbolic(Variable(989_931));
        let target = Address::symbolic(Variable(989_932));
        let stored = Pointer::new(target.clone(), ProgramType::Int32Pointer)
            .with_bounds(Some(SubobjectBounds::constant(target, 4)));
        let memory = SymbolicMemory::new()
            .store(slot.clone(), ProgramValue::Pointer(stored.clone()))
            .without_possible_aliasing_cells(&write, 4, &PureFactContext::new())
            .store(write.clone(), ProgramValue::Int32(7u32.into()));
        assert!(memory.known_value(&slot).is_none());
        let variable =
            load_variable_for_exact_cell(&intern_memory_ref(&memory), &slot, LoadKind::Int32, 8);
        let cached = ProgramValue::Int32(OldMachineTerm::Variable(variable));
        let own = |pointer| {
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                pointer,
                0u32.into(),
                1u32.into(),
                8,
            ))
        };
        let empty = PureFactContext::new();
        let context = empty
            .clone()
            .assume_proposition(Proposition::ResourceComposition(
                ResourceContext::new()
                    .unchecked_with_fact(own(slot.clone()))
                    .unchecked_with_fact(own(write)),
            ));
        let read = |facts: &PureFactContext, purpose| {
            canonicalized_pointer_value_from_int_cell(
                &memory,
                &slot,
                &cached,
                ProgramType::Int32Pointer,
                &mut ExecutionFacts::new(),
                facts,
                None,
                purpose,
                None,
            )
            .expect("typed cached read")
        };
        // Logical reads can enter directly, outside the scope used for
        // C expressions in specifications. They must still retain their term.
        assert_eq!(
            read(&context, LoadPurpose::Logical),
            read(&empty, LoadPurpose::Logical)
        );
        let _scope = SpecificationReadScope::enter();
        for purpose in [
            LoadPurpose::Logical,
            LoadPurpose::Validity,
            LoadPurpose::Program,
        ] {
            assert_eq!(read(&context, purpose), read(&empty, purpose));
            let uncached_read = |facts: &PureFactContext| {
                canonicalized_symbolic_load_value_with_identity(
                    &memory,
                    None,
                    &slot,
                    ProgramType::Int32Pointer,
                    &mut ExecutionFacts::new(),
                    facts,
                    None,
                    purpose,
                )
                .expect("typed uncached read")
            };
            assert_eq!(uncached_read(&context), uncached_read(&empty));
        }
    }

    #[test]
    fn specification_cached_pointer_prefix_identity_is_fact_stable() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = SymbolicMemory::new();
        let source = Address::symbolic(Variable(989_910));
        let destination = Address::symbolic(Variable(989_911));
        let read = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&(intern_memory_ref(&memory))),
            source.clone(),
            LoadKind::Int32,
        );
        let variable = load_variable_for_term(&read).unwrap().0;
        let value = ProgramValue::Int32(OldMachineTerm::Variable(variable));
        let empty = PureFactContext::new();
        let facts = empty.clone().assume_condition(
            OldConditionTerm::address_equal(source, destination.clone()),
            true,
        );
        let _scope = SpecificationReadScope::enter();
        for (label, purpose) in [
            ("logical", LoadPurpose::Logical),
            ("validity", LoadPurpose::Validity),
            ("program in specification", LoadPurpose::Program),
        ] {
            let evaluate = |context: &PureFactContext| {
                canonicalized_pointer_value_from_int_cell(
                    &memory,
                    &destination,
                    &value,
                    ProgramType::Int32Pointer,
                    &mut ExecutionFacts::new(),
                    context,
                    None,
                    purpose,
                    None,
                )
                .unwrap()
            };
            assert_eq!(evaluate(&facts), evaluate(&empty), "{label}");
        }
    }

    #[test]
    fn specification_program_pointer_reads_retain_their_logical_names() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = SymbolicMemory::new();
        let a = Address::symbolic(Variable(940_097));
        let b = Address::symbolic(Variable(940_098));
        let context = PureFactContext::new()
            .assume_condition(OldConditionTerm::address_equal(a.clone(), b.clone()), true);
        let read = |address: &Address| {
            let paths = evaluate_memory_load_paths(
                &memory,
                address.clone(),
                ProgramType::Int64Pointer,
                ExecutionFacts::new(),
                Vec::new(),
                &context,
                true,
                false,
                None,
                None,
            );
            let ExpressionOutcome::Value(ProgramValue::Pointer(pointer)) = &paths[0].outcome else {
                panic!("typed read");
            };
            pointer.address().clone()
        };
        let x = read(&a);
        let y = read(&b);
        // Program reads are named by their reads, so the selected address
        // equality alone joins them; without it they stay distinct.
        assert_eq!(x.as_loaded_value().unwrap().defining_address, a);
        assert_eq!(y.as_loaded_value().unwrap().defining_address, b);
        assert!(!PureFactContext::new().pointers_known_equal(&x, &y));
        {
            let _specification = SpecificationReadScope::enter();
            assert_eq!(read(&a), x);
            assert_eq!(read(&b), y);
        }
        assert!(context.pointers_known_equal(&x, &y));
        assert!(!PureFactContext::new().pointers_known_equal(&x, &y));
    }

    #[test]
    fn logical_cached_raw_pointer_reads_retain_their_load_variables() {
        let _session = crate::kernel::VerificationSession::enter();
        let base = SymbolicMemory::new();
        let origin = intern_memory_ref(&base);
        let a = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(940_091)), 4),
        );
        let b = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(940_092)), 4),
        );
        let field_a = a.clone().offset_by_bytes(8);
        let field_b = b.clone().offset_by_bytes(8);
        let first = base.symbolic_pointer_load(None, &field_a, ProgramType::Int32Pointer);
        let second = base.symbolic_pointer_load(None, &field_b, ProgramType::Int32Pointer);
        let slot_a = Address::new("local:raw-a".into(), AddressOffset::constant(0));
        let slot_b = Address::new("local:raw-b".into(), AddressOffset::constant(0));
        let memory = base
            .store(slot_a.clone(), first)
            .store(slot_b.clone(), second);
        let context = PureFactContext::new().assume_condition(
            OldConditionTerm::pointer_equal(
                Pointer::new(a, ProgramType::Int32Pointer),
                Pointer::new(b, ProgramType::Int32Pointer),
            ),
            true,
        );
        let canonical = |field: &Address| {
            Address::loaded(&canonical_term(&crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(&origin),
                field.clone(),
                LoadKind::Int32,
            )))
            .unwrap()
        };
        let direct = canonical(&field_a);
        let indirect = canonical(&field_b);
        // Each raw read is named by its own field read.
        assert_eq!(direct.as_loaded_value().unwrap().defining_address, field_a);
        assert_eq!(
            indirect.as_loaded_value().unwrap().defining_address,
            field_b
        );
        assert!(
            !PureFactContext::new()
                .equality_graph
                .are_equal(&direct, &indirect)
        );
        for (slot, expected) in [(&slot_a, &direct), (&slot_b, &indirect)] {
            let paths = evaluate_logical_memory_load_paths(
                &memory,
                slot.clone(),
                ProgramType::Int32Pointer,
                ExecutionFacts::new(),
                Vec::new(),
                &context,
            );
            let ExpressionOutcome::Value(ProgramValue::Pointer(value)) = &paths[0].outcome else {
                panic!("a cached pointer read");
            };
            // The slot's read keeps its name; the pointer stored there is the
            // field read, which the read-over-write authority relates it to.
            assert_eq!(
                pointer_read_over_write_value(value.address()).as_ref(),
                Some(expected)
            );
        }
        assert!(context.equality_graph.are_equal(&direct, &indirect));
        assert!(
            !context
                .equality_graph
                .are_equal(&direct, &indirect.offset_by_bytes(8))
        );
    }

    #[test]
    fn logical_pointer_read_registration_invalidates_an_earlier_memoized_miss() {
        let memory = SymbolicMemory::new();
        let a = Address::symbolic(Variable(92_210));
        let b = Address::symbolic(Variable(92_211));
        let before = PureFactContext::new();
        let program_read = |address: &Address| {
            let paths = evaluate_memory_load_paths(
                &memory,
                address.clone(),
                ProgramType::Int64Pointer,
                Vec::new().into(),
                Vec::new(),
                &before,
                true,
                false,
                None,
                None,
            );
            let ExpressionOutcome::Value(ProgramValue::Pointer(value)) = &paths[0].outcome else {
                panic!("pointer read");
            };
            value.address().clone()
        };
        let x = program_read(&a);
        let y = program_read(&b);
        // Program reads carry their own read definitions; what arrives late
        // is the address equality that joins them.
        let _scope = before.enter_id_scope();
        assert!(!pointers_proven_equal_for_memory_resolution(
            &x, &y, &before
        ));
        // Warm compound-query dependency misses before the address equality
        // appears. The late equality must invalidate those misses as well.
        for _ in 0..2 {
            assert!(!before.pointers_known_equal(&x.offset_by_bytes(8), &y.offset_by_bytes(8)));
        }
        let context = before
            .clone()
            .assume_condition(OldConditionTerm::address_equal(a.clone(), b.clone()), true);
        let _late_scope = context.enter_id_scope();
        assert_eq!(logical_pointer_read(&memory, &a, &context), x);
        assert_eq!(logical_pointer_read(&memory, &b, &context), y);
        assert!(pointers_proven_equal_for_memory_resolution(
            &x, &y, &context
        ));
        assert!(context.pointers_known_equal(&x.offset_by_bytes(8), &y.offset_by_bytes(8)));
        assert!(!context.pointers_known_equal(&x.offset_by_bytes(8), &y.offset_by_bytes(16)));
        assert!(!before.pointers_known_equal(&x.offset_by_bytes(8), &y.offset_by_bytes(8)));
    }

    #[test]
    fn cached_typed_pointer_read_emits_only_complete_owned_store_frames() {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = Address::symbolic(Variable(92_330));
        let write = Address::symbolic(Variable(92_331));
        let before = intern_memory(SymbolicMemory::new());
        let load = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&before),
            slot.clone(),
            LoadKind::Int32,
        );
        let (variable, _) = load_variable_for_term(&load).unwrap();
        for (owned_bytes, overlap, later_stores, expected) in [
            (0, false, 0, false),
            (4, false, 0, false),
            (8, false, 0, true),
            (8, false, 4, false),
            (8, true, 0, false),
        ] {
            let written = if overlap {
                slot.offset_by_bytes(4)
            } else {
                write.clone()
            };
            let mut memory = before.memory().clone().store(
                written.clone(),
                ProgramValue::UInt64(OldMachineTerm::uint64_constant(0)),
            );
            let mut transitions = vec![(before.memory().clone(), memory.clone(), written)];
            // Separation across more than one write requires an explicit
            // chain; the cached prefix alone is not a complete-pointer proof.
            for n in 0..later_stores {
                let previous = memory.clone();
                let write = slot.offset_by_bytes(16 + 8 * n);
                memory = memory.store(
                    write.clone(),
                    ProgramValue::UInt64(OldMachineTerm::uint64_constant(1)),
                );
                transitions.push((previous, memory.clone(), write));
            }
            let old_read = Address::loaded_value(&before, &slot);
            let mut context = PureFactContext::new();
            let mut resources = ResourceContext::new();
            if owned_bytes != 0 {
                resources = ResourceContext::new()
                    .unchecked_with_fact(ResourceFact::own_memory(
                        MemoryRange::new_with_element_width(
                            slot.clone(),
                            0u32.into(),
                            1u32.into(),
                            owned_bytes,
                        ),
                    ))
                    .unchecked_with_fact(ResourceFact::own_memory(
                        MemoryRange::new_with_element_width(
                            write.clone(),
                            0u32.into(),
                            1u32.into(),
                            8,
                        ),
                    ));
                context =
                    context.assume_proposition(Proposition::ResourceComposition(resources.clone()));
            }
            let mut facts = ExecutionFacts::new();
            let ProgramValue::Pointer(result) = canonicalized_pointer_value_from_int_cell(
                &memory,
                &slot,
                &ProgramValue::Int32(OldMachineTerm::Variable(variable)),
                ProgramType::Int64Pointer,
                &mut facts,
                &context,
                None,
                LoadPurpose::Program,
                None,
            )
            .expect("typed cached read") else {
                panic!("pointer read")
            };
            let new_read = result.provenance();
            let retained = facts.iter().fold(PureFactContext::new(), |context, fact| {
                context.assume_execution_pure_fact(fact)
            });
            assert_eq!(
                retained
                    .equality_graph
                    .provenance_equal(&old_read, new_read),
                expected,
                "owned bytes={owned_bytes}, overlap={overlap}, later stores={later_stores}"
            );
            assert!(
                !PureFactContext::new()
                    .equality_graph
                    .provenance_equal(&old_read, new_read)
            );
            if owned_bytes == 8 && !overlap {
                let left = Resource::Memory(MemoryRange::new_with_element_width(
                    write.clone(),
                    0u32.into(),
                    1u32.into(),
                    8,
                ));
                let right = Resource::Memory(MemoryRange::new_with_element_width(
                    slot.clone(),
                    0u32.into(),
                    1u32.into(),
                    8,
                ));
                assert!(context.proves_held_resources_separate(&resources, &left, &right));
                let separation = Proposition::ResourceSeparate {
                    left: Box::new(left),
                    right: Box::new(right),
                };
                let mut explicit = context.clone().assume_proposition(
                    crate::kernel::region_footprint::byte_premise(&separation).unwrap(),
                );
                for (index, (entry, exit, write)) in transitions.into_iter().enumerate() {
                    if index != 0 {
                        // These synthetic writes are at slot + 16, +24, ...;
                        // supply their separation as each certificate's premise.
                        explicit = explicit.assume_proposition(Proposition::ResourceSeparate {
                            left: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                                write.clone(),
                                0u32.into(),
                                8u32.into(),
                                1,
                            ))),
                            right: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                                slot.clone(),
                                0u32.into(),
                                8u32.into(),
                                1,
                            ))),
                        });
                    }
                    let (_, _, equality) = crate::kernel::tests::explicit_frame(
                        &entry,
                        &exit,
                        &slot,
                        ProgramType::Int64Pointer,
                        &[Proposition::MemoryMutatesOnly {
                            before: entry.clone(),
                            before_point: Default::default(),
                            after: exit.clone(),
                            after_point: Default::default(),
                            writes: vec![(write, crate::kernel::AccessExtent::from(8))],
                        }],
                        &explicit,
                    )
                    .expect("one explicitly supplied separated write");
                    explicit = explicit.assume_proposition(equality);
                }
                assert!(
                    explicit
                        .equality_graph
                        .provenance_equal(&old_read, new_read),
                    "explicit complete-pointer frames recover the long case"
                );
            }
        }
    }

    #[test]
    fn cached_typed_read_retains_exact_definition_without_admitting_facts() {
        let context = PureFactContext::new();
        let address = Address::symbolic(Variable(92_310));
        let retained_state = intern_memory(SymbolicMemory::new());
        let load = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&retained_state),
            address.clone(),
            crate::kernel::LoadKind::Int32,
        );
        let (variable, _) = load_variable_for_term(&load).expect("load identity");
        let mut facts = crate::kernel::ExecutionFacts::new();
        let source = test_load_source(0);
        let ProgramValue::Pointer(value) = canonicalized_pointer_value_from_int_cell(
            &retained_state,
            &address,
            &ProgramValue::Int32(OldMachineTerm::Variable(variable)),
            ProgramType::Int64Pointer,
            &mut facts,
            &context,
            Some(&source),
            LoadPurpose::Program,
            None,
        )
        .expect("cached typed pointer") else {
            panic!("expected pointer");
        };
        // The cached read is named by its exact definition, without any
        // producer fact being admitted first.
        let application = Address::loaded_value(&retained_state, &address);
        assert_eq!(value.address(), &application);
        assert!(
            facts.is_empty(),
            "the descriptor needs no defining equation"
        );
        assert!(context.pointers_known_equal(value.address(), &application));
        assert!(context.pure_facts().is_empty());
        assert!(
            ResourceContext::new()
                .memory_write_range(value.address(), 8, &context)
                .is_none()
        );
        let sibling = PureFactContext::new();
        assert!(sibling.pointers_known_equal(value.address(), &application));
        assert!(sibling.pure_facts().is_empty());
        let declared =
            intern_memory(SymbolicMemory::new().with_block(AddressBase::from("global:other"), 8));
        assert!(
            context
                .pointers_known_equal(value.address(), &Address::loaded_value(&declared, &address))
        );
        let later = intern_memory(
            declared
                .memory()
                .clone()
                .store(address.offset_by_bytes(4), crate::kernel::uint8(1u32)),
        );
        assert!(
            !context
                .pointers_known_equal(value.address(), &Address::loaded_value(&later, &address))
        );
    }

    #[test]
    fn cached_pointer_prefix_cannot_recover_bounds_after_an_upper_half_write() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Address::symbolic(Variable(92_312));
        let before = SymbolicMemory::new();
        let (variable, _) = load_variable_for_term(&crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&(intern_memory_ref(&before))),
            address.clone(),
            LoadKind::Int32,
        ))
        .unwrap();
        let cached = ProgramValue::Int32(OldMachineTerm::Variable(variable));
        let read = |memory: &SymbolicMemory, context: &PureFactContext| {
            let ProgramValue::Pointer(value) = canonicalized_pointer_value_from_int_cell(
                memory,
                &address,
                &cached,
                ProgramType::Int32Pointer,
                &mut ExecutionFacts::new(),
                context,
                None,
                LoadPurpose::Logical,
                None,
            )
            .unwrap() else {
                panic!("pointer read")
            };
            value
        };
        let original = read(&before, &PureFactContext::new());
        let base = Address::new(AddressBase::Heap(92_312), AddressOffset::constant(0));
        let bounded = Pointer::new(base.clone(), ProgramType::Int32Pointer)
            .with_bounds(Some(SubobjectBounds::new(base, 4u32.into())));
        let context = PureFactContext::new().assume_condition(
            OldConditionTerm::pointer_equal(original.clone(), bounded.clone()),
            true,
        );
        assert_eq!(
            context.pointer_domain(&original),
            crate::kernel::assumptions::PointerDomain::Selected(bounded.bounds().unwrap().clone())
        );
        let unchanged = before.clone().with_block("unrelated-pointer-cache", 4);
        assert_eq!(
            context.pointer_domain(&read(&unchanged, &context)),
            crate::kernel::assumptions::PointerDomain::Selected(bounded.bounds().unwrap().clone())
        );
        let observed = before
            .clone()
            .materialize_symbolic_cell(address.clone(), ProgramType::Int32)
            .materialize_symbolic_cell(address.clone().offset_by_bytes(4), ProgramType::Int32);
        let observed_read = read(&observed, &context);
        assert_eq!(observed_read.address(), original.address());
        assert!(context.pointer_provenance_match(&observed_read, &bounded));
        assert_eq!(
            context.pointer_domain(&observed_read),
            crate::kernel::assumptions::PointerDomain::Selected(bounded.bounds().unwrap().clone())
        );
        let overwritten = observed.store(
            address.clone().offset_by_bytes(4),
            ProgramValue::UInt32(0u32.into()),
        );
        let changed = read(&overwritten, &context);
        assert_eq!(
            changed.address(),
            original.address(),
            "the cached numeric prefix is unchanged; it cannot supply bounds"
        );
        assert!(!context.pointer_provenance_match(&changed, &bounded));
        assert_eq!(
            context.pointer_domain(&changed),
            crate::kernel::assumptions::PointerDomain::Unknown
        );
    }

    #[test]
    fn cached_volatile_pointer_read_has_no_retainable_definition() {
        let context = PureFactContext::new();
        let address = Address::symbolic(Variable(92_311));
        let retained_state = intern_memory(SymbolicMemory::new());
        let load = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&retained_state),
            address.clone(),
            crate::kernel::LoadKind::Int32,
        );
        let (variable, _) = load_variable_for_term(&load).expect("load identity");
        let mut facts = crate::kernel::ExecutionFacts::new();
        let ProgramValue::Pointer(value) = canonicalized_pointer_value_from_int_cell(
            &retained_state,
            &address,
            &ProgramValue::Int32(OldMachineTerm::Variable(variable)),
            ProgramType::Int64Pointer,
            &mut facts,
            &context,
            None,
            LoadPurpose::VolatileProgram,
            None,
        )
        .expect("cached volatile pointer") else {
            panic!("expected pointer");
        };
        for fact in &facts {
            fact.retain_pointer_read_definition(&context);
        }
        assert!(!context.pointers_known_equal(
            value.address(),
            &Address::loaded_value(&retained_state, &address)
        ));
    }

    #[test]
    fn completed_pointer_reads_join_through_later_graph_address_equality() {
        let memory = SymbolicMemory::new();
        let retained_state = intern_memory(memory.clone());
        let a = Address::symbolic(Variable(92_100));
        let b = Address::symbolic(Variable(92_101));
        let read = |address: &Address, volatile| {
            let paths = evaluate_memory_load_paths(
                &memory,
                address.clone(),
                ProgramType::Int64Pointer,
                Vec::new().into(),
                Vec::new(),
                &PureFactContext::new(),
                true,
                volatile,
                None,
                None,
            );
            assert_eq!(paths.len(), 1);
            let ExpressionOutcome::Value(ProgramValue::Pointer(value)) = &paths[0].outcome else {
                panic!("expected a pointer read: {:?}", paths[0].outcome);
            };
            (value.address().clone(), paths[0].facts.clone())
        };
        let (x, x_facts) = read(&a, false);
        let (y, y_facts) = read(&b, false);
        let empty = PureFactContext::new();
        // A completed program read is named by its own read.
        assert_eq!(x, Address::loaded_value(&retained_state, &a));
        assert_eq!(y, Address::loaded_value(&retained_state, &b));
        let available = x_facts
            .iter()
            .chain(&y_facts)
            .fold(empty.clone(), |context, fact| {
                context.assume_execution_pure_fact(fact)
            });
        assert!(available.pointers_known_equal(&x, &Address::loaded_value(&retained_state, &a)));
        assert!(!empty.pointers_known_equal(&x, &y));
        let branch = available
            .clone()
            .assume_condition(OldConditionTerm::address_equal(a.clone(), b.clone()), true);
        assert!(branch.equality_graph.are_equal(&a, &b));
        assert!(
            branch
                .equality_graph
                .are_pointer_loads_equal(&retained_state, &a, &b)
        );
        assert!(branch.pointers_known_equal(&x, &y));
        let owner = ResourceContext::new_with_equalities(&available).unchecked_with_fact(
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                x.clone(),
                0u32.into(),
                1u32.into(),
                4,
            )),
        );
        assert!(!owner.permits_memory_read(&y, 4, &available));
        assert!(owner.memory_write_range(&y, 4, &available).is_none());
        assert!(owner.permits_memory_read(&y, 4, &branch));
        assert!(owner.memory_write_range(&y, 4, &branch).is_some());
        let address_first = empty
            .clone()
            .assume_condition(OldConditionTerm::address_equal(a.clone(), b.clone()), true);
        let address_first = x_facts
            .iter()
            .chain(&y_facts)
            .fold(address_first, |context, fact| {
                context.assume_execution_pure_fact(fact)
            });
        assert!(address_first.pointers_known_equal(&x, &y));
        assert!(!empty.pointers_known_equal(&x, &y));
        // The reads are their own names, so no bridge fact is needed to
        // identify either with its read: the address equality alone joins
        // them. Authority still comes only from the owner.
        let address_only = empty
            .clone()
            .assume_condition(OldConditionTerm::address_equal(a.clone(), b), true);
        assert!(address_only.pointers_known_equal(&x, &y));
        assert!(owner.permits_memory_read(&y, 4, &address_only));
        assert!(!ResourceContext::new().permits_memory_read(&y, 4, &address_only));
        assert!(!address_only.pointers_known_equal(&x, &y.offset_by_bytes(8)));
        let declared = intern_memory(
            memory
                .clone()
                .with_block(AddressBase::from("global:later"), 8),
        );
        assert!(available.pointers_known_equal(&x, &Address::loaded_value(&declared, &a)));
        let later = intern_memory(
            declared
                .memory()
                .clone()
                .store(a.offset_by_bytes(4), crate::kernel::uint8(1u32)),
        );
        assert!(!available.pointers_known_equal(&x, &Address::loaded_value(&later, &a)));
        let volatile_address = Address::symbolic(Variable(92_102));
        let (volatile_value, volatile_facts) = read(&volatile_address, true);
        let volatile_context = volatile_facts.iter().fold(empty, |context, fact| {
            context.assume_execution_pure_fact(fact)
        });
        assert!(!volatile_context.pointers_known_equal(
            &volatile_value,
            &Address::loaded_value(&retained_state, &volatile_address),
        ));
        let (volatile_same, volatile_same_facts) = read(&a, true);
        let volatile_only = volatile_same_facts
            .iter()
            .fold(PureFactContext::new(), |context, fact| {
                context.assume_execution_pure_fact(fact)
            });
        let normal_only = x_facts
            .iter()
            .fold(PureFactContext::new(), |context, fact| {
                context.assume_execution_pure_fact(fact)
            });
        // A normal read is its own name and needs no defining fact; a
        // volatile read keeps an opaque load variable with its defining fact.
        assert_ne!(normal_only.condition_facts, volatile_only.condition_facts);
        assert_ne!(
            normal_only.memo_fingerprint(),
            volatile_only.memo_fingerprint()
        );
        assert_ne!(normal_only, volatile_only);
        assert!(
            !volatile_only
                .pointers_known_equal(&volatile_same, &Address::loaded_value(&retained_state, &a),)
        );
        let scalar_paths = evaluate_memory_load_paths(
            &memory,
            a.clone(),
            ProgramType::Int64,
            Vec::new().into(),
            Vec::new(),
            &PureFactContext::new(),
            true,
            false,
            None,
            None,
        );
        assert_eq!(scalar_paths.len(), 1);
        assert!(!matches!(
            scalar_paths[0].outcome,
            ExpressionOutcome::Value(ProgramValue::Pointer(_))
        ));
        let scalar_only = scalar_paths[0]
            .facts
            .iter()
            .fold(PureFactContext::new(), |context, fact| {
                context.assume_execution_pure_fact(fact)
            });
        assert!(!scalar_only.pointers_known_equal(&x, &y));
    }

    /// Explicit normalization checks a typed full-width pointer read and its
    /// cited value relation; offsets alone and stale/partial stores do not suffice.
    #[test]
    fn normalize_recorded_pointer_values_checks_selected_facts_and_width() {
        use crate::kernel::proof::PureFactStore;
        use crate::kernel::proof::fact_reasoning::normalize_using_conditions;
        let _session = crate::kernel::VerificationSession::enter();
        let address = Address::symbolic(Variable(99_100));
        let stored = Address::symbolic(Variable(99_101));
        let wrong = Address::symbolic(Variable(99_102));
        let empty = PureFactContext::new();
        let equality = |left: &Address, right: &Address| {
            Proposition::condition_is(
                OldConditionTerm::address_equal(left.clone(), right.clone()),
                true,
            )
        };
        let memory = SymbolicMemory::new().store(
            address.clone(),
            ProgramValue::typed_pointer(stored.clone(), ProgramType::Int32Pointer),
        );
        let read = |memory: SymbolicMemory, address: &Address, variable, width| {
            record_load_access_width(&memory, address, width);
            let value = Address::symbolic(Variable(variable));
            empty.register_pointer_read(&value, &intern_memory(memory), address);
            value
        };
        let value = read(memory.clone(), &address, 99_103, 8);
        let premise = equality(&stored, &Address::null());
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&premise));
        for goal in [
            equality(&value, &Address::null()),
            equality(&Address::null(), &value),
        ] {
            assert!(
                normalize_using_conditions(&goal, std::slice::from_ref(&premise), &facts).is_ok()
            );
            assert!(
                normalize_using_conditions(&goal, &[], &PureFactStore::from_ordered(&[])).is_err()
            );
        }
        assert!(
            normalize_using_conditions(
                &equality(&value, &wrong),
                std::slice::from_ref(&premise),
                &facts
            )
            .is_err()
        );
        assert!(
            normalize_using_conditions(
                &equality(&value.offset_by_bytes(4), &Address::null()),
                std::slice::from_ref(&premise),
                &facts
            )
            .is_err()
        );
        let changed = memory
            .without_possible_aliasing_cells(&address.offset_by_bytes(4), 4, &empty)
            .store(
                address.offset_by_bytes(4),
                ProgramValue::Int32(OldMachineTerm::constant(0)),
            );
        let changed = read(changed, &address, 99_104, 8);
        assert!(
            normalize_using_conditions(
                &equality(&changed, &Address::null()),
                std::slice::from_ref(&premise),
                &facts
            )
            .is_err()
        );
        let narrow_address = Address::symbolic(Variable(99_105));
        let narrow = read(
            SymbolicMemory::new().store(
                narrow_address.clone(),
                ProgramValue::typed_pointer(stored, ProgramType::Int32Pointer),
            ),
            &narrow_address,
            99_106,
            4,
        );
        assert!(
            normalize_using_conditions(
                &equality(&narrow, &Address::null()),
                std::slice::from_ref(&premise),
                &facts
            )
            .is_err()
        );
        let scalar_address = Address::symbolic(Variable(99_107));
        let scalar = read(
            SymbolicMemory::new().store(
                scalar_address.clone(),
                ProgramValue::UInt64(OldMachineTerm::uint64_constant(0)),
            ),
            &scalar_address,
            99_108,
            8,
        );
        assert!(
            normalize_using_conditions(
                &equality(&scalar, &Address::null()),
                &[],
                &PureFactStore::from_ordered(&[])
            )
            .is_err()
        );
    }

    /// Same-block pointer equality is lowered to offset equality. It still
    /// needs an exact typed read, including its stride and unambiguous origin.
    #[test]
    fn normalize_recorded_pointer_reads_checks_definition() {
        use crate::kernel::proof::PureFactStore;
        use crate::kernel::proof::fact_reasoning::normalize_using_conditions;
        let _session = crate::kernel::VerificationSession::enter();
        let context = PureFactContext::new();
        let facts = PureFactStore::from_ordered(&[]);
        let address = Address::symbolic(Variable(103_001));
        let stored = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(103_002)), 4),
        );
        let memory = SymbolicMemory::new().store(
            address.clone(),
            ProgramValue::typed_pointer(stored.clone(), ProgramType::Int32Pointer),
        );
        record_load_access_width(&memory, &address, 8);
        let read = Address::loaded_value(&intern_memory(memory.clone()), &address);
        let equality = |left: &Address, right: &Address| {
            Proposition::condition_is(
                OldConditionTerm::AddressEqual(Box::new(left.clone()), Box::new(right.clone())),
                true,
            )
        };
        for goal in [equality(&read, &stored), equality(&stored, &read)] {
            assert!(normalize_using_conditions(&goal, &[], &facts).is_ok());
        }
        assert!(
            normalize_using_conditions(&equality(&read.offset_by_bytes(4), &stored), &[], &facts)
                .is_err()
        );
        let wrong_value = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(103_004)), 4),
        );
        assert!(normalize_using_conditions(&equality(&read, &wrong_value), &[], &facts).is_err());
        let partial = memory
            .without_possible_aliasing_cells(&address.offset_by_bytes(4), 4, &context)
            .store(
                address.offset_by_bytes(4),
                ProgramValue::Int32(OldMachineTerm::constant(0)),
            );
        record_load_access_width(&partial, &address, 8);
        let changed = Address::loaded_value(&intern_memory(partial), &address);
        assert!(normalize_using_conditions(&equality(&changed, &stored), &[], &facts).is_err());
    }
    /// Canonical read states retain an exact projection edge back to the
    /// execution source. The selected alias is still required to find its store.
    #[test]
    fn normalize_recorded_pointer_value_follows_exact_projection_source() {
        use crate::kernel::proof::PureFactStore;
        use crate::kernel::proof::fact_reasoning::normalize_using_conditions;
        let _session = crate::kernel::VerificationSession::enter();
        let context = PureFactContext::new();
        let address = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(104_001)), 4),
        );
        let written = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(104_002)), 4),
        );
        let stored = Address::symbolic(Variable(104_003));
        let source = SymbolicMemory::new()
            .with_block_without_derivation("local:projection", 4)
            .store(
                written.clone(),
                ProgramValue::typed_pointer(stored.clone(), ProgramType::Int32Pointer),
            );
        record_load_access_width(&source, &address, 8);
        let source = intern_memory(source);
        let original = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&source),
            address.clone(),
            LoadKind::Int32,
        );
        let projected = crate::kernel::memory_history::canonicalize_atomic_loads_deep(&original);
        let OldMachineTerm::MemoryLoad(projected, _, _) = projected else {
            panic!("an unresolved aliased read must remain a load");
        };
        assert_ne!(source, *projected.shared_memory());
        record_load_access_width(projected.memory(), &address, 8);
        let read = Address::symbolic(Variable(104_004));
        context.register_pointer_read(&read, projected.shared_memory(), &address);
        let alias =
            Proposition::condition_is(OldConditionTerm::address_equal(address, written), true);
        let goal = Proposition::condition_is(OldConditionTerm::address_equal(read, stored), true);
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&alias));
        assert!(normalize_using_conditions(&goal, std::slice::from_ref(&alias), &facts).is_ok());
        assert!(normalize_using_conditions(&goal, &[], &PureFactStore::from_ordered(&[])).is_err());
    }
    #[test]
    fn symbolic_storage_pointer_cells_share_logical_read_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Address::symbolic(Variable(190_101));
        let memory = SymbolicMemory::new();
        assert!(
            cached_symbolic_storage_cell_value(&memory, &address, ProgramType::Int32Pointer)
                .is_none()
        );
        for program_type in [
            ProgramType::Int32Pointer,
            ProgramType::UInt8Pointer,
            ProgramType::VoidPointer,
        ] {
            let stored =
                symbolic_storage_cell_value(&memory, None, &address, program_type, false).unwrap();
            let logical = memory.symbolic_pointer_load(None, &address, program_type);
            assert!(
                stored == logical,
                "storage and logical reads must have identical values and provenance"
            );
            assert!(
                cached_symbolic_storage_cell_value(&memory, &address, program_type)
                    == Some(logical)
            );
        }
        // Changing the upper half invalidates the whole pointer observation.
        let changed = memory
            .clone()
            .store(address.offset_by_bytes(4), ProgramValue::Int32(7.into()));
        let old =
            symbolic_storage_cell_value(&memory, None, &address, ProgramType::Int32Pointer, false)
                .unwrap();
        let new =
            symbolic_storage_cell_value(&changed, None, &address, ProgramType::Int32Pointer, false)
                .unwrap();
        assert!(old != new);
    }

    #[test]
    fn symbolic_pointer_load_factory_retains_exact_read_definition() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Address::symbolic(Variable(190_001));
        let memory = SymbolicMemory::new();
        let ProgramValue::Pointer(value) =
            memory.symbolic_pointer_load(None, &address, ProgramType::Int32Pointer)
        else {
            panic!("typed pointer read")
        };
        assert_eq!(
            crate::kernel::equality_graph::logical_pointer_read_term(value.address()),
            Some(crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(&(intern_memory(memory.clone()))),
                address.clone(),
                LoadKind::Int32
            )),
        );
        // Recording a definition does not settle a value or grant a cell.
        let assumptions = PureFactContext::new();
        assert_eq!(
            assumptions.decide(&OldConditionTerm::address_equal(
                value.address().clone(),
                Address::symbolic(Variable(190_002)),
            )),
            None
        );
        assert!(!memory.is_loadable_concretely(&address, 8));
        let cell_bits = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&(intern_memory(memory))),
            address.clone(),
            LoadKind::Int32,
        );
        // The pointee width does not enter the read's identity.
        assert_eq!(
            &Address::loaded(&cell_bits.clone()).unwrap(),
            value.address()
        );
        // A displaced read, or an address indexed by the cell's scalar, has
        // no read definition of its own.
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_term(
                &value.address().offset_by_bytes(8)
            )
            .is_none()
        );
        let scalar_indexed = address.offset_by_elements(cell_bits, 8);
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_term(&scalar_indexed).is_none()
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/eval/memory_loads/tests.rs");
    }
}

#[cfg(test)]
mod pointer_comparison_tests {
    use super::*;
    use crate::kernel::VerificationSession;

    #[test]
    fn pointer_read_comparison_preserves_the_complete_stored_bounds() {
        let _session = VerificationSession::enter();
        let slot = Address::symbolic(Variable(989_001));
        let target = Address::symbolic(Variable(989_002));
        let stored = Pointer::new(target.clone(), ProgramType::Int32Pointer)
            .with_bounds(Some(SubobjectBounds::new(target.clone(), 4u32.into())));
        let memory = intern_memory(
            SymbolicMemory::new().store(slot.clone(), ProgramValue::Pointer(stored.clone())),
        );
        let read = Pointer::new(
            Address::loaded_value(&memory, &slot),
            ProgramType::Int32Pointer,
        );
        let equal = Proposition::condition_is(
            OldConditionTerm::PointerEqual(Box::new(read.clone()), Box::new(stored)),
            true,
        );
        assert!(holds_by_read_over_write(&equal));
        let larger = Pointer::new(target.clone(), ProgramType::Int32Pointer)
            .with_bounds(Some(SubobjectBounds::new(target, 8u32.into())));
        let unequal = Proposition::condition_is(
            OldConditionTerm::PointerEqual(Box::new(read), Box::new(larger)),
            true,
        );
        assert!(!holds_by_read_over_write(&unequal));
    }

    #[test]
    fn pointer_read_comparison_keeps_explicit_bounds_on_the_read() {
        let _session = VerificationSession::enter();
        let slot = Address::symbolic(Variable(989_020));
        let target = Address::symbolic(Variable(989_021));
        let stored = Pointer::new(target.clone(), ProgramType::Int32Pointer)
            .with_bounds(Some(SubobjectBounds::new(target.clone(), 4u32.into())));
        let memory = intern_memory(
            SymbolicMemory::new().store(slot.clone(), ProgramValue::Pointer(stored.clone())),
        );
        let read = Pointer::new(
            Address::loaded_value(&memory, &slot),
            ProgramType::Int32Pointer,
        )
        .with_bounds(Some(SubobjectBounds::new(target, 8u32.into())));
        let unequal = Proposition::condition_is(
            OldConditionTerm::PointerEqual(Box::new(read), Box::new(stored)),
            true,
        );
        assert!(!holds_by_read_over_write(&unequal));
    }

    #[test]
    fn integer_read_over_write_follows_a_stored_pointer_address() {
        let _session = VerificationSession::enter();
        let slot = Address::new(AddressBase::Heap(989_003), AddressOffset::constant(0));
        let target = Address::new(AddressBase::Heap(989_004), AddressOffset::constant(0));
        let memory = intern_memory(
            SymbolicMemory::new()
                .store(
                    slot.clone(),
                    ProgramValue::typed_pointer(target.clone(), ProgramType::Int32Pointer),
                )
                .store(target.offset_by_bytes(4), ProgramValue::Int32(37u32.into())),
        );
        let address = Address::loaded_value(&memory, &slot).offset_by_bytes(4);
        let raw = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&memory),
            address,
            LoadKind::Int32,
        );
        let (name, _) = load_variable_for_term(&raw).expect("the integer read has a version name");
        assert_eq!(
            read_over_write_value(&OldMachineTerm::Variable(name)),
            Some(37u32.into())
        );
    }

    mod scaling_tests {
        include!("../../scaling_tests/kernel/eval/memory_loads/pointer_comparison_tests.rs");
    }
}

#[cfg(test)]
mod pointer_read_value_definition_tests {
    use super::*;

    #[test]
    fn named_pointer_read_definitions_follow_later_observations() {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let unrelated = Address::new(AddressBase::Heap(985_003), AddressOffset::constant(0));
        let first = crate::kernel::intern_memory(
            SymbolicMemory::new().store(unrelated.clone(), ProgramValue::UInt32(1u32.into())),
        );
        let named = Address::version_read(&first, &cell);
        let context = PureFactContext::new();
        assert!(context.pointers_known_equal(&named, &Address::loaded_value(&first, &cell)));
        let later = crate::kernel::intern_memory(
            first
                .memory()
                .clone()
                .store(unrelated, ProgramValue::UInt32(2u32.into())),
        );
        let later_read = Address::loaded_value(&later, &cell);
        assert_eq!(named, Address::version_read(&later, &cell));
        assert!(PureFactContext::new().pointers_known_equal(&named, &later_read));
        assert!(
            crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
                &named,
                &later_read,
                &context
            )
        );
        assert!(context.pointers_known_equal(&named, &later_read));
        assert!(
            PureFactContext::new()
                .pointers_known_equal(&named, &Address::loaded_value(&first, &cell))
        );
    }

    #[test]
    fn named_pointer_reads_retain_the_original_state_definition() {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let source = crate::kernel::intern_memory(SymbolicMemory::new().store(
            Address::new(AddressBase::Heap(985_001), AddressOffset::constant(0)),
            ProgramValue::UInt32(1u32.into()),
        ));
        let named = Pointer::new(
            Address::version_read(&source, &cell),
            ProgramType::Int32Pointer,
        );
        let original = Pointer::new(
            Address::loaded_value(&source, &cell),
            ProgramType::Int32Pointer,
        );
        assert_ne!(named.address(), original.address());
        let context = PureFactContext::new();
        assert!(context.equality_graph.knows_condition(
            &OldConditionTerm::PointerEqual(Box::new(named.clone()), Box::new(original)),
            true,
        ));
        let changed = crate::kernel::intern_memory(
            source
                .memory()
                .clone()
                .store(cell.offset_by_bytes(4), ProgramValue::UInt32(9u32.into())),
        );
        let changed = Pointer::new(
            Address::loaded_value(&changed, &cell),
            ProgramType::Int32Pointer,
        );
        assert!(!context.equality_graph.knows_condition(
            &OldConditionTerm::PointerEqual(Box::new(named), Box::new(changed)),
            true,
        ));
    }

    #[test]
    fn named_pointer_reads_retain_complete_stored_values_in_the_graph() {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = Address::symbolic(Variable(981_301));
        let target = Address::symbolic(Variable(981_302));
        let stored = Pointer::new(target.clone(), ProgramType::Int32Pointer)
            .with_bounds(Some(SubobjectBounds::new(target.clone(), 4u32.into())));
        let memory = crate::kernel::intern_memory(
            SymbolicMemory::new().store(slot.clone(), ProgramValue::Pointer(stored.clone())),
        );
        let named = Pointer::new(
            Address::version_read(&memory, &slot),
            ProgramType::Int32Pointer,
        );
        assert_ne!(named.address(), stored.address());
        assert_ne!(named.provenance(), stored.provenance());
        let context = PureFactContext::new();
        assert!(context.equality_graph.knows_condition(
            &OldConditionTerm::PointerEqual(Box::new(named.clone()), Box::new(stored.clone())),
            true,
        ));
        let other_bounds = stored
            .clone()
            .with_bounds(Some(SubobjectBounds::new(target, 8u32.into())));
        assert!(!context.equality_graph.knows_condition(
            &OldConditionTerm::PointerEqual(Box::new(named), Box::new(other_bounds)),
            true,
        ));
    }
}

#[test]
fn arithmetic_comparison_normalizes_selected_read_addresses_without_changing_terms() {
    use crate::kernel::{MachineBinaryOp, MachineIntegerType};
    let _session = crate::kernel::VerificationSession::enter();
    let index = OldMachineTerm::Variable(Variable(989_784));
    let written = OldMachineTerm::logical_machine_binary(
        MachineIntegerType::UInt64,
        MachineBinaryOp::Add,
        OldMachineTerm::uint64_constant(0),
        index.clone(),
    );
    let pointer = |value| {
        Address::new(
            Address::symbolic(Variable(989_785)).base.clone(),
            AddressOffset::scaled_int64_node(value, 4, true),
        )
    };
    let memory = crate::kernel::intern_memory(SymbolicMemory::new());
    let read = |memory, value| {
        crate::kernel::canonical_form_of_load(memory, pointer(value), LoadKind::Int32)
    };
    let original = read(memory.clone(), written.clone());
    let simple = read(memory.clone(), index.clone());
    let equality =
        |left, right| Proposition::condition_is(OldConditionTerm::equal(left, right), true);
    let fact = equality(original.clone(), simple.clone());
    let comparison =
        arithmetic_comparison_form(&fact).expect("the addresses have an arithmetic identity");
    assert!(
        crate::kernel::proposition_holds_without_facts(&comparison),
        "{comparison:?}"
    );
    assert_ne!(
        original, simple,
        "the original read must retain its written address"
    );
    assert!(matches!(
        written,
        OldMachineTerm::Binary {
            op: MachineBinaryOp::Add,
            ..
        }
    ));
    let changed = SymbolicMemory::new().store(
        pointer(index.clone()),
        ProgramValue::Int32(OldMachineTerm::constant(17)),
    );
    let different_state = equality(original, read(crate::kernel::intern_memory(changed), index));
    assert!(!crate::kernel::proposition_holds_without_facts(
        &comparison_form(&different_state).unwrap_or(different_state)
    ));
}

#[cfg(test)]
mod structural_read_connective_tests {
    use super::*;
    use crate::kernel::VerificationSession;

    #[test]
    fn canonical_facts_retain_written_logical_roots_and_polarity() {
        use crate::kernel::{
            AlgebraicType, IntegerComparisonOperator, KernelType, StoredConditionTerm,
        };
        let _session = VerificationSession::enter();
        let variable = KernelTerm::variable(KernelType::Bool, Variable(982211));
        let literal = KernelTerm::boolean_literal(false);
        let algebraic = KernelTerm::variable(
            KernelType::Algebraic(AlgebraicType::parameter("T".into())),
            Variable(982212),
        );
        let pointer = Pointer::new(
            Address::symbolic(Variable(982213)),
            ProgramType::UInt8Pointer,
        );
        let integer = KernelTerm::variable(KernelType::Integer, Variable(982214));
        let equality = KernelTerm::boolean_equal_raw([variable.clone(), literal.clone()]);
        let conditional =
            KernelTerm::boolean_if_raw([variable.clone(), equality.clone(), literal.clone()]);
        let call = OldConditionTerm::bool_application("canonical_fact_predicate", vec![]);
        let roots = [
            variable,
            literal,
            equality,
            conditional,
            KernelTermImport::default().condition(&call),
            KernelTerm::integer_comparison(
                IntegerComparisonOperator::LessEqual,
                [integer.clone(), integer],
            )
            .unwrap(),
            KernelTerm::algebraic_equal_raw([algebraic.clone(), algebraic]),
            KernelTerm::pointer_equal_raw([pointer.shared().clone(), pointer.shared().clone()]),
        ];
        for root in roots {
            let condition = StoredConditionTerm::from_root(root.clone()).unwrap();
            for truth in [false, true] {
                let fact = Proposition::condition_is(condition.clone(), truth);
                let Proposition::ConditionIs(result, polarity) = canonical_condition_fact(&fact)
                else {
                    unreachable!()
                };
                assert_eq!(result.root(), Some(&root));
                assert_eq!(polarity, truth);
                assert!(!root.has_cached_native_argument());
            }
        }
    }

    #[test]
    fn exact_read_occurrences_match_names_before_stored_value_folding() {
        let _session = VerificationSession::enter();
        let address = Address::symbolic(Variable(989_032));
        let memory = intern_memory(
            SymbolicMemory::new().store(address.clone(), ProgramValue::Int32(37u32.into())),
        );
        let name = load_variable_for_cell(&memory, &address, LoadKind::Int32);
        let read = registered_load_term_for_variable(&name).unwrap();
        let named = OldMachineTerm::Variable(name);
        assert!(terms_have_same_canonical_form(&read, &named));
        assert!(terms_have_same_canonical_form(&named, &read));
        let other = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&memory),
            address.offset_by_bytes(4),
            LoadKind::Int32,
        );
        assert!(!terms_have_same_canonical_form(&other, &named));
    }

    #[test]
    fn stored_structural_reads_compare_inside_logical_connectives() {
        let _session = VerificationSession::enter();
        let address = Address::symbolic(Variable(989_031));
        let memory = intern_memory(
            SymbolicMemory::new().store(address.clone(), ProgramValue::Int32(37u32.into())),
        );
        let read = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&memory),
            address,
            LoadKind::Int32,
        );
        let observed = IntegerTerm::from_machine(MachineIntegerType::Int32, read).unwrap();
        let leaf = Proposition::condition_is(
            OldConditionTerm::integer_equal(observed, IntegerTerm::constant_i64(37)),
            true,
        );
        let expected = comparison_form(&leaf).expect("stored value comparison");
        let guard = Proposition::condition_is(OldConditionTerm::Constant(true), true);
        let wrap = |body: Proposition| {
            Proposition::Implies(
                Box::new(guard.clone()),
                Box::new(Proposition::And(
                    Box::new(body.clone()),
                    Box::new(Proposition::Or(
                        Box::new(body.clone()),
                        Box::new(Proposition::Not(Box::new(body))),
                    )),
                )),
            )
        };
        clear_load_variable_registry();
        assert_eq!(comparison_form(&wrap(leaf)), Some(wrap(expected)));
        assert_eq!(load_variable_registry_len(), 0);
    }
}

#[cfg(test)]
mod float_conversion_load_tests {
    use super::*;

    #[test]
    fn retained_float_conversion_load_detection_keeps_opaque_integer_source_payloads() {
        let _session = crate::kernel::VerificationSession::enter();
        let read = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&(crate::kernel::intern_memory(SymbolicMemory::new()))),
            Address::symbolic(Variable(999977)),
            LoadKind::Int32,
        );
        for source in [read, OldMachineTerm::Variable(Variable(999978))] {
            let native = OldMachineTerm::opaque_conversion(
                "c_float32_to_int32",
                OldMachineTerm::opaque_conversion(
                    "c_int32_to_float32",
                    OldMachineTerm::PureFunctionApplication {
                        name: "opaque_integer_source".into(),
                        arguments: vec![source],
                    },
                ),
            );
            let root = crate::kernel::KernelTermImport::default()
                .machine(MachineIntegerType::Int32, &native);
            let exports = crate::kernel::KernelTermExport::machine_export_count();
            assert_eq!(
                operand_mentions_a_memory_load(crate::kernel::MachineOperandView::Shared(&root)),
                term_mentions_a_memory_load(&native)
            );
            assert_eq!(
                crate::kernel::KernelTermExport::machine_export_count(),
                exports
            );
        }
    }
}

#[test]
fn symbolic_copied_run_reads_keep_the_original_source_address_and_point() {
    let _session = crate::kernel::VerificationSession::enter();
    let entry = ExecutionState::new().begin_function_entry_memory();
    let source_base = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(16));
    let destination = Address::new("copied-run-destination".into(), AddressOffset::constant(4));
    let value_type = ProgramType::Int32;
    let stride = value_type.byte_width();
    let index = OldMachineTerm::Variable(Variable(986_235));
    for source in [
        entry.program_point(),
        ProgramPoint::of_memory(entry.memory()),
    ] {
        for wide in [false, true] {
            let assumptions = PureFactContext::new().assume_condition(
                if wide {
                    OldConditionTerm::uint64_equal(
                        index.clone(),
                        OldMachineTerm::uint64_constant(0),
                    )
                } else {
                    OldConditionTerm::equal(index.clone(), OldMachineTerm::constant(0))
                },
                true,
            );
            let destination_index = destination
                .offset_by_bytes(stride)
                .offset_by_typed_elements(index.clone(), stride, wide, wide);
            let source_index = source_base
                .offset_by_bytes(2 * stride)
                .offset_by_typed_elements(index.clone(), stride, wide, wide);
            let work = [2, 8, 64, 256].map(|count| {
                let memory = SymbolicMemory::new()
                    .with_block("copied-run-destination", (count + 1) * stride)
                    .with_named_cell_run(
                        source_base.clone(),
                        stride,
                        value_type,
                        0,
                        count + 1,
                        source.clone(),
                    )
                    .unwrap();
                let copied = memory
                    .write_scalar_array_state(
                        &destination,
                        value_type,
                        count,
                        ProgramValue::typed_pointer(
                            source_base.offset_by_bytes(stride),
                            ProgramType::Int32Pointer,
                        ),
                        true,
                        false,
                        &assumptions,
                    )
                    .expect("copy a complete subrange of the named run");
                let (read, work) = crate::instrumentation::measure_deterministic_work(|| {
                    symbolic_index_run_load(
                        &copied,
                        &destination_index,
                        value_type,
                        &mut ExecutionFacts::new(),
                        &assumptions,
                        None,
                        LoadPurpose::Logical,
                    )
                });
                let Some(ProgramValue::Int32(OldMachineTerm::MemoryLoad(point, address, kind))) =
                    read
                else {
                    panic!("expected a copied word read");
                };
                assert_eq!(*address, source_index);
                assert_eq!(kind, LoadKind::Int32);
                assert_eq!(point.read_version_id(), source.id());
                work
            });
            assert!(work.iter().all(|units| *units <= work[0] + 8), "{work:?}");
        }
    }
}

#[cfg(test)]
mod float_memory_handoff_tests {
    use super::*;

    #[test]
    fn ordinary_symbolic_float_reads_keep_the_observation_point() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        let first = ExecutionState::new().begin_function_entry_memory();
        let second = first.clone().begin_function_entry_memory();
        assert_eq!(first.memory(), second.memory());
        assert_ne!(first.program_point_id(), second.program_point_id());

        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            for state in [&first, &second] {
                let origin = state.program_point();
                let expected = format.value(crate::kernel::OldMachineTerm::read_named(
                    origin.clone().for_exact_read(),
                    address.clone(),
                    format.load_kind(),
                ));
                let value_type = format.program_type();
                let ordinary = PureFactContext::new().prefer_symbolic_external_loads();
                let forced = ordinary.clone().force_symbolic_external_loads();
                for assumptions in [&ordinary, &forced] {
                    let logical = evaluate_logical_memory_load_paths_at(
                        &origin,
                        address.clone(),
                        value_type,
                        ExecutionFacts::new(),
                        vec![],
                        assumptions,
                    );
                    let [path] = logical.as_slice() else {
                        panic!("expected one logical read");
                    };
                    assert_eq!(path.outcome, ExpressionOutcome::Value(expected.clone()));
                }

                let program = evaluate_retained_memory_load_paths(
                    &origin,
                    address.clone(),
                    value_type,
                    ExecutionFacts::new(),
                    vec![],
                    &ordinary,
                    true,
                    false,
                    None,
                    None,
                    true,
                );
                let [path] = program.as_slice() else {
                    panic!("expected one program read");
                };
                let ExpressionOutcome::Value(value) = &path.outcome else {
                    panic!("expected a symbolic program value");
                };
                assert_eq!(value.native().as_ref(), &expected);
            }
        }
    }

    #[test]
    fn symbolic_float_run_reads_name_the_source_point_without_visiting_slots() {
        let _session = crate::kernel::VerificationSession::enter();
        let source = ExecutionState::new().begin_function_entry_memory();
        let point = source.program_point();
        let base = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let value_type = format.program_type();
            let bytes = value_type.byte_width();
            let index = OldMachineTerm::Variable(Variable(986_234));
            let pointer =
                base.with_offset(AddressOffset::scale_int32(index.clone(), i64::from(bytes)));
            let assumptions = PureFactContext::new().assume_condition(
                OldConditionTerm::equal(index, OldMachineTerm::constant(0)),
                true,
            );
            let expected = format.value(crate::kernel::OldMachineTerm::read_named(
                point.clone().for_exact_read(),
                pointer.clone(),
                format.load_kind(),
            ));
            let work = [1, 8, 64, 256].map(|count| {
                let memory = source
                    .memory()
                    .clone()
                    .with_named_cell_run(base.clone(), bytes, value_type, 0, count, point.clone())
                    .unwrap();
                let (read, work) = crate::instrumentation::measure_deterministic_work(|| {
                    symbolic_index_run_load(
                        &memory,
                        &pointer,
                        value_type,
                        &mut ExecutionFacts::new(),
                        &assumptions,
                        None,
                        LoadPurpose::Logical,
                    )
                });
                assert_eq!(read, Some(expected.clone()));
                work
            });
            assert!(work.iter().all(|units| *units <= work[0] + 8), "{work:?}");
        }
    }

    #[test]
    fn float_cells_preserve_exact_bits_and_retained_load_roots() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let negative_zero = match format {
                KernelFloatType::Float32 => OldMachineTerm::uint32_constant(0x80000000),
                KernelFloatType::Float64 => OldMachineTerm::uint64_constant(0x8000000000000000),
            };
            let nan = match format {
                KernelFloatType::Float32 => OldMachineTerm::uint32_constant(0x7fc00123),
                KernelFloatType::Float64 => OldMachineTerm::uint64_constant(0x7ff8000000000123),
            };
            for root in [
                KernelTermImport::default().float(format, &negative_zero),
                KernelTermImport::default().float(format, &nan),
                KernelTerm::float_call(format, "stored_float_call".into(), vec![]),
            ] {
                let value = ExecutionValue::Shared(root.clone());
                let native = value.clone().into_native();
                let address = SymbolicMemory::local_pointer("float_cell");
                let memory = SymbolicMemory::new()
                    .with_block(address.base.clone(), format.program_type().byte_width())
                    .store_retained(address.clone(), value);
                assert_eq!(
                    memory.known_retained_value(&address).unwrap().shared(),
                    Some(&root)
                );
                assert_eq!(memory.known_value(&address), Some(native.clone()));
                let paths = evaluate_retained_memory_load_paths(
                    &ProgramPoint::of_memory(&memory),
                    address,
                    format.program_type(),
                    ExecutionFacts::new(),
                    vec![],
                    &PureFactContext::new(),
                    false,
                    false,
                    None,
                    None,
                    false,
                );
                assert_eq!(paths.len(), 1);
                let ExpressionOutcome::Value(loaded) = &paths[0].outcome else {
                    panic!("stored float should load: {:?}", paths[0].outcome);
                };
                assert_eq!(loaded.shared(), Some(&root));
                assert_eq!(loaded.clone().into_native(), native);
            }
        }
    }
}
