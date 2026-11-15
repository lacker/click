use super::*;
use crate::kernel::CompareRelation;
use crate::kernel::MachineCastSpelling;
use crate::kernel::{bits32_constant, int64_constant, native_constant, uint64_constant};

fn retained_cell_conversion(source: &ExecutionValue, value: ProgramValue) -> ExecutionValue {
    if source.shared().is_some_and(|root| {
        root.ty() == &KernelType::Bool || matches!(root.ty(), KernelType::Algebraic(_))
    }) && value.program_type() == source.program_type()
    {
        // Same-type cell conversion leaves Boolean and algebraic values unchanged.
        source.clone()
    } else if source.shared().is_some() {
        source.retain_checked_pointer(value)
    } else {
        value.into()
    }
}

#[derive(Default)]
struct MemoryLoadAliasCache {
    resolution_equal: BTreeMap<(u64, Pointer), bool>,
    resolution_distinct: BTreeMap<(u64, Pointer), bool>,
    equal: BTreeMap<(u64, Pointer), bool>,
}

impl MemoryLoadAliasCache {
    fn resolution_equal(
        &mut self,
        pointer: &Pointer,
        stored_pointer: &Pointer,
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
        pointer: &Pointer,
        stored_pointer: &Pointer,
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
        pointer: &Pointer,
        stored_pointer: &Pointer,
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
pub(in crate::kernel) fn evaluate_memory_load_paths(
    memory: &Memory,
    pointer: Pointer,
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
        memory,
        pointer,
        value_type,
        facts,
        obligations,
        assumptions,
        has_external_read_resource,
        volatile,
        source,
        byte_order,
    )
    .into_iter()
    .map(ExecutionValuePath::into_native)
    .collect()
}

#[allow(clippy::too_many_arguments)]
pub(in crate::kernel) fn evaluate_retained_memory_load_paths(
    memory: &Memory,
    pointer: Pointer,
    value_type: ProgramType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    has_external_read_resource: bool,
    volatile: bool,
    source: Option<&LoadSourceId>,
    byte_order: Option<ByteOrder>,
) -> Vec<ExecutionValuePath> {
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
    );
    if let Some(address) = word_storage {
        for path in &mut paths {
            if let ExpressionOutcome::Value(value) = &mut path.outcome {
                *value = retained_cell_conversion(
                    value,
                    complete_loaded_word(value.native().into_owned(), memory, &address),
                );
            }
        }
    }
    if !volatile && !SpecificationReadScope::is_active() {
        for path in &mut paths {
            if let ExpressionOutcome::Value(value) = &mut path.outcome
                && let Some(pointer) = value.pointer()
            {
                *value = retained_cell_conversion(
                    value,
                    ProgramValue::Pointer(assumptions.pointer_value_at_entry(pointer)),
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
            let read = Pointer::loaded_value(&observed.0, &observed.1);
            path.facts.push(
                if matches!(value.program_type(), ProgramType::FunctionPointer(_)) {
                    ExecutionPureFact::checked_pointer_read_equation(value.clone(), read)
                } else {
                    ExecutionPureFact::logical_read_equation(value.clone(), read)
                },
            );
            let mut read_facts = ExecutionFacts::new();
            if let Some(variable) = typed_pointer_read_variable(value.pointer())
                && let Some(load) =
                    crate::kernel::equality_graph::logical_pointer_read_term(value.pointer())
            {
                // Build the selected evidence in a fresh stream, without
                // searching or rewriting unrelated incoming path facts.
                record_load_variable_defining_fact_with_source_and_pointer(
                    variable,
                    load,
                    &mut read_facts,
                    source,
                    Some(value.pointer()),
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
    memory: &Memory,
    pointer: Pointer,
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
pub(in crate::kernel) fn evaluate_logical_memory_load_paths(
    memory: &Memory,
    pointer: Pointer,
    value_type: ProgramType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<ExpressionPath> {
    let mut paths = evaluate_logical_memory_load_paths_unbridged(
        memory,
        pointer.clone(),
        value_type,
        facts,
        obligations,
        assumptions,
    );
    retain_indexed_scalar_cell_value(memory, &pointer, value_type, assumptions, &mut paths);
    if let [path] = paths.as_slice()
        && let ExpressionOutcome::Value(value) = &path.outcome
    {
        super::typed_reads::record(memory, &pointer, value);
    }
    paths
}

fn evaluate_logical_memory_load_paths_unbridged(
    memory: &Memory,
    pointer: Pointer,
    value_type: ProgramType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<ExpressionPath> {
    // The read keeps the address it was written with: lowering is
    // fact-stable (`docs/internals/spellability.md`). A value stored under
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
        let mut paths = evaluate_memory_load_paths_with_alias_cache(
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
        );
        for path in &mut paths {
            // An invalid typed read still denotes a logical value. The C
            // evaluator's refusal is retained only by checked evaluation.
            if matches!(path.outcome, ExpressionOutcome::RuntimeError(_))
                && let Some(value) = canonicalized_symbolic_load_value_with_identity(
                    memory,
                    &pointer,
                    value_type,
                    &mut path.facts,
                    assumptions,
                    None,
                    LoadPurpose::Logical,
                )
            {
                path.outcome = ExpressionOutcome::Value(value);
            }
            if let ExpressionOutcome::Value(value) = &mut path.outcome {
                *value = complete_loaded_word(value.clone(), memory, &pointer);
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
                        || matches!(&stored, ProgramValue::Int32(MachineTerm::Variable(variable))
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
                    )
                    .or_else(|| value_type.read_cell(&stored))
                    .inspect(|value| {
                        if let ProgramValue::Pointer(value) = value {
                            record_pointer_read_observation(value.pointer(), memory, &pointer);
                            let current = Pointer::loaded_value(
                                &crate::kernel::intern_memory_ref(memory),
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
        .or_else(|| {
            canonicalized_symbolic_load_value_with_identity(
                memory,
                &pointer,
                value_type,
                &mut facts,
                assumptions,
                None,
                LoadPurpose::Logical,
            )
        });
    facts.retain(|fact| !is_load_variable_defining_fact(fact.proposition()));
    value
        .into_iter()
        .map(|value| ExpressionPath {
            outcome: ExpressionOutcome::Value(complete_loaded_word(value, memory, &pointer)),
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
    pointer: &Pointer,
    stored_pointer: &Pointer,
    stored_value: &ProgramValue,
) -> bool {
    pointer.block.is_static_storage_block()
        && stored_pointer.block != pointer.block
        && holds_its_own_read(stored_value, stored_pointer)
}

/// Whether a cell was seeded with a read of its own address. The retained
/// descriptor supplies its version; a legacy pointer carrier may still name it.
fn holds_its_own_read(stored: &ProgramValue, pointer: &Pointer) -> bool {
    crate::kernel::spec::program_value_bitvector_term(stored)
        .and_then(|term| viewed_as_memory_load(&term))
        .is_some_and(
            |term| matches!(term, MachineTerm::MemoryLoad(_, address, _) if *address == *pointer),
        )
}

/// Whether a logical read of a `value_type` cell lowers to the read at the
/// cell's version rather than to a value the cell holds
/// (`docs/internals/spellability.md`). Integer and pointer cells keep their
/// read identities; abstract values still read their stored value.
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
}

/// A selected footprint supplies an equal address, not a replacement read
/// term or access permission. Retain its stored word as a path-local equation.
fn retain_indexed_scalar_cell_value(
    memory: &Memory,
    pointer: &Pointer,
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
            ..ExecutionPureFact::certified(Proposition::ConditionIs(
                ConditionTerm::equal(read, stored),
                true,
            ))
        });
    }
}

/// Use a published footprint only to select coordinates for this logical
/// address. Equality of the address grants no access or state transport.
fn logical_memory_load_address(
    memory: &Memory,
    pointer: Pointer,
    value_type: ProgramType,
    assumptions: &PureFactContext,
) -> Pointer {
    // Only opaque model pointers and external pointers with an admitted
    // cross-block alias can need another spelling. Wide scalar loads need
    // the cached coordinate because their equalities do not use int32 load
    // congruence. Keep ordinary and loaded-pointer reads on their fast path.
    let model_pointer = match &pointer.block {
        PointerBlock::Symbolic(variable) if !crate::kernel::is_load_variable(variable) => true,
        PointerBlock::ExternalArgument
            if matches!(value_type, ProgramType::Int64 | ProgramType::UInt64)
                && assumptions
                    .equality_graph
                    .pointer_is_classed(&pointer.block) =>
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

fn has_pending_reallocation_for_pointer(memory: &Memory, pointer: &Pointer) -> bool {
    memory
        .heap
        .pending_reallocations
        .values()
        .any(|pending| pending.old_pointer.block == pointer.block)
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
    memory: &Memory,
    pointer: Pointer,
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
    )
    .into_iter()
    .map(ExecutionValuePath::into_native)
    .collect()
}

#[allow(clippy::too_many_arguments)]
fn evaluate_retained_memory_load_paths_with_alias_cache(
    memory: &Memory,
    pointer: Pointer,
    value_type: ProgramType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    has_external_read_resource: bool,
    purpose: LoadPurpose,
    alias_cache: &mut MemoryLoadAliasCache,
    source: Option<&LoadSourceId>,
    byte_order: Option<ByteOrder>,
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
    memory: Memory,
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
    memory: &Memory,
    written: &Memory,
    pointer: Pointer,
    value_type: ProgramType,
    facts: ExecutionFacts,
    mut obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    has_external_read_resource: bool,
    purpose: LoadPurpose,
    alias_cache: &mut MemoryLoadAliasCache,
    source: Option<&LoadSourceId>,
    byte_order: Option<ByteOrder>,
    splits: bool,
    distinct_case: &mut Option<DistinctLoadCase>,
) -> Vec<ExecutionValuePath> {
    let branches_on_unresolved_aliases =
        splits && matches!(purpose, LoadPurpose::Program | LoadPurpose::VolatileProgram);
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
                .map(|(condition, value)| Proposition::ConditionIs(condition.clone(), value))
                .collect::<Vec<_>>()
        }
    } else {
        Default::default()
    };
    for source in candidates {
        let Some(theorem) = prove_program_condition_fact_transport(&source, memory, assumptions)
        else {
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
            || assumptions.has_memory_read_defined_evidence(memory, &pointer, value_type));
    // A typed union overlay is the authoritative view for an exact typed
    // load, including in provenance-sensitive symbolic-load mode. Selecting
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

    // Provenance-sensitive lowering asks for the load identity even when this
    // state has already materialized the cell's concrete value. Checking
    // `known_value` first would collapse `at(mark, field == 11)` to `true` and
    // erase the address needed for later frame transport.
    // An abstract value has no frame history to transport: a stored one is
    // the value, found by the lookups below.
    if allow_symbolic_external_load
        && assumptions.should_force_symbolic_external_loads()
        && !matches!(value_type, ProgramType::Parameter(_))
    {
        let Some(value) = canonicalized_retained_symbolic_load_value_with_identity(
            if purpose == LoadPurpose::Program && value_type.pointee_type().is_none() {
                written
            } else {
                memory
            },
            &pointer,
            value_type,
            &mut facts,
            assumptions,
            source,
            purpose,
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
    if let Some(value) =
        known.filter(|stored| !names_version || holds_its_own_read(&stored.native(), &pointer))
    {
        if let Some(value) = canonicalized_pointer_value_from_int_cell(
            memory,
            &pointer,
            &value.native(),
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
        if let Some(converted) = value_type.read_cell(&value.native()) {
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
                    (AlgebraicTermNode::parameter_load(source, pointer, parameter)).into(),
                ),
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
    } else if let Some(value) = crate::instrumentation::measure_operation(
        "kernel",
        "memory load",
        "memory load: equal-cell scan",
        || {
            // A cell in a block proven distinct from the load's is never
            // resolution-equal to it, so only the candidates can match, and
            // they are visited in the whole map's order.
            let candidates = AliasCandidates::of_block(&pointer.block);
            let normalized = std::cell::OnceCell::new();
            let (found, visited) = memory.cells.find_retained_candidate_by(
                &candidates,
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
        && !assumptions.has_memory_read_defined_evidence(memory, &pointer, value_type)
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

    if allow_symbolic_external_load && assumptions.should_prefer_symbolic_external_loads() {
        let Some(value) = canonicalized_retained_symbolic_load_value_with_identity(
            if purpose == LoadPurpose::Program && value_type.pointee_type().is_none() {
                written
            } else {
                memory
            },
            &pointer,
            value_type,
            &mut facts,
            assumptions,
            source,
            purpose,
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
            let candidates = AliasCandidates::of_block(&pointer.block);
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
                            cell_access_byte_width(stored_value),
                            &pointer,
                            load_bytes,
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
        let Some(value) = canonicalized_retained_symbolic_load_value_with_identity(
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
        .candidate_runs(&AliasCandidates::of_block(&pointer.block))
        .filter(|run| {
            matches!(
                crate::kernel::reasoning::memory_resolution::run_access(run, &pointer),
                crate::kernel::reasoning::memory_resolution::RunAccess::Scaled { .. }
            )
        })
        .cloned()
        .collect::<Vec<_>>();
    let in_symbolically_indexed_run = |stored_pointer: &Pointer| {
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
        let stored_bytes = cell_access_byte_width(&stored_value.native());
        // General equality can resolve an indexed address that the narrower
        // memory resolver leaves open. A proven alias supplies this cell's
        // value; merely skipping its alias branch would lose an initialized
        // cell and eventually report an uninitialized read.
        let known_equal = !assumptions.should_defer_non_exact_condition_reasoning()
            && alias_cache.equal(&pointer, &stored_pointer, assumptions);

        let mut equal_facts = facts.clone();
        if known_equal
            || add_pointer_offset_equality_execution_pure_facts(
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
        if add_pointer_offset_equality_execution_pure_facts(
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
                stored_bytes,
                &pointer,
                value_type.byte_width(),
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
                        ConditionTerm::pointer_offset_equal(
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
                let outcome = match canonicalized_retained_symbolic_load_value_with_identity(
                    if purpose == LoadPurpose::Program && value_type.pointee_type().is_none() {
                        written
                    } else {
                        &memory
                    },
                    &pointer,
                    value_type,
                    &mut distinct_facts,
                    assumptions,
                    source,
                    purpose,
                ) {
                    Some(value) => ExpressionOutcome::Value(value.into()),
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
            ProgramType::Int8 => int8(MachineTerm::constant(0)),
            ProgramType::Int16 => int16(MachineTerm::constant(0)),
            ProgramType::Int32 => int32(MachineTerm::constant(0)),
            ProgramType::UInt8 => uint8(MachineTerm::constant(0)),
            ProgramType::UInt16 => uint16(MachineTerm::constant(0)),
            ProgramType::UInt32 => ProgramValue::UInt32(MachineTerm::uint32_constant(0)),
            ProgramType::Int64 => ProgramValue::Int64(MachineTerm::int64_constant(0)),
            ProgramType::UInt64 => ProgramValue::UInt64(MachineTerm::uint64_constant(0)),
            ProgramType::Int128 => match crate::kernel::program_expression::int128_literal(0) {
                ProgramExpression::Value(value) => value,
                _ => unreachable!("wide literal is a value"),
            },
            ProgramType::UInt128 => match crate::kernel::program_expression::uint128_literal(0) {
                ProgramExpression::Value(value) => value,
                _ => unreachable!("wide literal is a value"),
            },
            ProgramType::Float32 => ProgramValue::Float32(MachineTerm::constant(0)),
            ProgramType::Float64 => ProgramValue::Float64(MachineTerm::uint64_constant(0)),
            _ if value_type.is_pointer() => {
                ProgramValue::typed_pointer(Pointer::null(), value_type)
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
        ) {
            return vec![ExpressionPath {
                outcome: ExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        let Some(value) = canonicalized_retained_symbolic_load_value_with_identity(
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
        let proposition = Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: pointer.clone(),
            bytes: MachineTerm::constant(value_type.byte_width()),
            wide: false,
        };
        if purpose == LoadPurpose::Validity {
            if add_proof_obligation(&mut obligations, assumptions, proposition).is_none() {
                return Vec::new();
            }
        } else if assumptions.should_defer_non_exact_loadability_obligations() {
            if !assumptions.proves_memory_loadable_for_memory_resolution(
                &memory,
                &pointer,
                &MachineTerm::constant(value_type.byte_width()),
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
        && ((pointer.block.is_local_block() && memory.has_block(&pointer.block))
            || memory.may_read_uninitialized_object(&pointer, value_type.byte_width()))
        && !written.has_initialized_bytes_under(&pointer, value_type.byte_width(), assumptions)
        && !assumptions.has_memory_read_defined_evidence(&memory, &pointer, value_type)
    {
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead),
            facts,
            obligations,
        }];
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
    ) {
        return vec![ExpressionPath {
            outcome: ExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    let Some(value) = canonicalized_retained_symbolic_load_value_with_identity(
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
    memory: &Memory,
    pointer: &Pointer,
) -> Option<SharedMemory> {
    let mut source: Option<SharedMemory> = None;
    for word in 0..ABSTRACT_VALUE_WIDTH / 4 {
        let address = pointer.offset_by_bytes(word * 4);
        let ProgramValue::Int32(term) = memory.known_value(&address)? else {
            return None;
        };
        let MachineTerm::MemoryLoad(loaded, loaded_address, LoadKind::Int32) =
            viewed_as_memory_load(&term)?
        else {
            return None;
        };
        if *loaded_address != address || source.as_ref().is_some_and(|source| *source != loaded) {
            return None;
        }
        source = Some(loaded);
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
fn cell_value_recorded_on_path(
    memory: &Memory,
    pointer: &Pointer,
    value_type: ProgramType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
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
        let entry = crate::kernel::resource_tracker::static_cell_unwritten_since_entry_on_path(
            &at,
            pointer,
            value_type.byte_width(),
            assumptions,
        )?;
        return canonicalized_retained_symbolic_load_value_with_identity(
            entry.memory(),
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
    ) {
        return Some(value.into());
    }
    value_type
        .read_cell(&value.native())
        .map(|converted| retained_cell_conversion(&value, converted))
}

/// Reinterprets a cached scalar read as a pointer while retaining its selected
/// descriptor. Complete-pointer frame evidence remains separate from the
/// numeric prefix. Only the legacy volatile route still allocates a name.
fn canonicalized_pointer_value_from_int_cell(
    memory: &Memory,
    pointer: &Pointer,
    value: &ProgramValue,
    value_type: ProgramType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
) -> Option<ProgramValue> {
    value_type.pointee_type()?;
    let (fresh, defining_load) = match value {
        ProgramValue::Int8(bits @ MachineTerm::MemoryLoad(..)) => {
            return Some(ProgramValue::Int8(canonical_scalar_read(bits)));
        }
        ProgramValue::Int16(bits @ MachineTerm::MemoryLoad(..)) => {
            return Some(ProgramValue::Int16(canonical_scalar_read(bits)));
        }
        ProgramValue::Int32(bits @ MachineTerm::MemoryLoad(..)) => {
            if purpose == LoadPurpose::VolatileProgram {
                let fresh = load_variable_for_term(bits)?.0;
                (Some(fresh), registered_load_term_for_variable(&fresh))
            } else {
                (None, Some(canonical_scalar_read(bits)))
            }
        }
        ProgramValue::Int32(MachineTerm::Variable(variable)) if is_load_variable(variable) => (
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
        Some(MachineTerm::MemoryLoad(_, address, _))
            if address.as_ref() != pointer
                && (purpose != LoadPurpose::Program || SpecificationReadScope::is_active()
                    || !crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
                        address, pointer, assumptions,
                    ))
    );
    // A volatile read may observe a value memory does not record, so it is
    // never named as the state's read of the cell.
    let loaded = if let Some(fresh) = fresh {
        Pointer::symbolic(fresh)
    } else if copied_prefix {
        Pointer::loaded_value(
            &crate::kernel::intern_memory_ref(memory).unchanged_bytes_source(),
            pointer,
        )
    } else {
        Pointer::loaded(defining_load.as_ref()?).expect("selected pointer read")
    };
    let result = PointerValue::from_read(
        loaded.clone(),
        value_type,
        &crate::kernel::intern_memory_ref(memory),
        pointer,
    );
    if purpose == LoadPurpose::Program
        && let Some(boundary) = result.designation().as_loaded_value()
        && let Some(previous) =
            assumptions.pointer_read_source(&boundary.defining_memory, &boundary.defining_address)
    {
        // The complete read already names the memoized fact-free stopping
        // point. Check that one edge's frame; a scalar prefix alone cannot
        // establish equality of complete pointer domains.
        let ProgramValue::Pointer(before) =
            previous.symbolic_pointer_version_load(&boundary.defining_address, value_type)
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
        && let Some(stored) = crate::kernel::memory_provenance::complete_pointer_read_value(
            result.designation(),
            assumptions,
        )
    {
        return Some(ProgramValue::Pointer(stored.with_type(value_type)));
    }
    if let Some(load) = defining_load {
        if !copied_prefix
            && (matches!(purpose, LoadPurpose::Logical | LoadPurpose::Validity)
                || purpose == LoadPurpose::Program && SpecificationReadScope::is_active())
            && let MachineTerm::MemoryLoad(memory, address, _) = &load
        {
            assumptions.register_pointer_read(&loaded, memory, address);
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
    memory: &Memory,
    pointer: &Pointer,
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
    let run = memory
        .cells
        .candidate_runs(&AliasCandidates::of_block(&pointer.block))
        .find(|run| {
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
                _ => return false,
            };
            let width = i64::from(run.element_width());
            if run.element_type() != value_type
                || width == 0
                || scale != width
                || shift.rem_euclid(width) != 0
            {
                return false;
            }
            let first_element = shift.div_euclid(width);
            // An unsigned 64-bit index starts at zero, so its slots begin at
            // `first_element`; they all lie in one live interval when the
            // index is decided below that interval's remaining length.
            if wide {
                let Ok(first) = u32::try_from(first_element) else {
                    return false;
                };
                return run
                    .live_intervals()
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
                                    crate::kernel::MachineOperandView::Legacy(
                                        &MachineTerm::uint64_constant(u64::from(
                                            *live_high - first,
                                        )),
                                    ),
                                ),
                            ) == Some(true)
                    });
            }
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
        })?
        .clone();
    // A constant run's slots are not loads of its source, which is empty:
    // every live slot holds the run's one value, so the load reads it.
    if let crate::kernel::primitives::RunValueMode::Constant(value) = run.value_mode() {
        return value_type.read_cell(value);
    }
    canonicalized_symbolic_load_value_with_identity(
        run.source().memory(),
        pointer,
        value_type,
        facts,
        assumptions,
        source,
        purpose,
    )
}

fn complete_loaded_word(value: ProgramValue, memory: &Memory, address: &Pointer) -> ProgramValue {
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
    let pointer = PointerValue::from_read(
        Pointer::integer_address(bits),
        ProgramType::VoidPointer,
        &crate::kernel::intern_memory_ref(memory),
        address,
    );
    ProgramValue::PointerInteger(PointerIntegerValue {
        numeric: Box::new(value),
        pointer: Box::new(pointer),
        kind: PointerIntegerKind::Word { changed_bits: 0 },
    })
}

fn canonicalized_symbolic_load_value_with_identity(
    memory: &Memory,
    pointer: &Pointer,
    value_type: ProgramType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
) -> Option<ProgramValue> {
    canonicalized_retained_symbolic_load_value_with_identity(
        memory,
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
    memory: &Memory,
    pointer: &Pointer,
    value_type: ProgramType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
) -> Option<ExecutionValue> {
    // A logical read keeps the address it was written with: lowering is
    // fact-stable (`docs/internals/spellability.md`). The equality graph
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
        return Some((complete_loaded_word(value, memory, &address)).into());
    }
    if WordRepresentationScope::keeps_representation()
        && matches!(value_type, ProgramType::Int64 | ProgramType::UInt64)
        && let Some(value @ ProgramValue::PointerInteger(_)) =
            crate::kernel::memory_provenance::complete_pointer_carrier_read_value(
                &Pointer::loaded_value(&crate::kernel::intern_memory_ref(memory), &address),
                assumptions,
            )
        && value_type.accepts(&value)
    {
        return Some((complete_loaded_word(value, memory, &address)).into());
    }
    // A logical pointer read names the cell's version, whatever pointer the
    // cell holds (`docs/internals/spellability.md`).
    let names_version = purpose == LoadPurpose::Logical && value_type.is_pointer();
    // Canonical address selection can expose a materialized pointer cell that
    // the original spelling did not name. Reuse its complete stored value;
    // manufacturing another read here would discard the selected designation.
    if !names_version
        && let Some(value) = memory.known_retained_value(&address)
        && value.pointer().is_some()
        && value_type.accepts(&value.native())
    {
        let stored = value.pointer().expect("selected complete pointer cell");
        facts.push(ExecutionPureFact::logical_read_equation(
            stored.clone(),
            Pointer::loaded_value(&crate::kernel::intern_memory_ref(memory), &address),
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
    let value = if names_version {
        record_load_access_width(memory, &address, value_type.byte_width());
        memory.symbolic_pointer_version_load(&address, value_type)
    } else {
        symbolic_load_value(memory, &address, value_type)?
    };
    // Ordinary scalar reads retain their selected memory and address directly.
    match &value {
        // A signed byte read is its own load (byte R-mem relates it to the
        // byte's unsigned read).
        ProgramValue::Int8(bits @ MachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some((ProgramValue::Int8(read)).into());
        }
        ProgramValue::Int16(bits @ MachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some((ProgramValue::Int16(read)).into());
        }
        ProgramValue::Int32(bits @ MachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some((ProgramValue::Int32(read)).into());
        }
        ProgramValue::UInt8(bits @ MachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some((ProgramValue::UInt8(read)).into());
        }
        ProgramValue::UInt16(bits @ MachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some((ProgramValue::UInt16(read)).into());
        }
        ProgramValue::UInt32(bits @ MachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some((ProgramValue::UInt32(read)).into());
        }
        ProgramValue::Int64(bits @ MachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some(
                (complete_loaded_word(ProgramValue::Int64(read), memory, &address)).into(),
            );
        }
        ProgramValue::UInt64(bits @ MachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some(
                (complete_loaded_word(ProgramValue::UInt64(read), memory, &address)).into(),
            );
        }
        ProgramValue::Int128(bits @ MachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some((ProgramValue::Int128(read)).into());
        }
        ProgramValue::UInt128(bits @ MachineTerm::MemoryLoad(_, _, _)) => {
            let read = canonical_scalar_read(bits);
            return Some((ProgramValue::UInt128(read)).into());
        }
        _ => {}
    }
    let ProgramValue::Pointer(pointer_value) = &value else {
        return Some((complete_loaded_word(value, memory, &address)).into());
    };
    // The read keeps its version name. The equality graph relates it to the
    // pointer stored there whenever a query names the read and memory alone
    // shows that pointer (`EqualityGraph::register_logical_read_values`); the
    // read equation beside it lets a context that keeps it reach the read from
    // the stored pointer too.
    if names_version {
        if let Some(stored) = pointer_read_over_write_program_value(pointer_value.pointer()) {
            facts.push(ExecutionPureFact::logical_read_equation(
                stored.with_type(value_type),
                pointer_value.pointer().clone(),
            ));
        }
        // The raw read of this state is the read the version names: one
        // place, so a read through an alias of the address reaches it.
        let raw = Pointer::loaded_value(&crate::kernel::intern_memory_ref(memory), &address);
        if raw != *pointer_value.pointer() {
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
    let complete_read = PointerValue::from_read(
        pointer_value.pointer().clone(),
        value_type,
        &crate::kernel::intern_memory_ref(memory),
        &address,
    );
    // A logical or specification read keeps its term; recovery belongs to
    // executed reads, with equality reasoning in the shared graph.
    if !names_version
        && !SpecificationReadScope::is_active()
        && !assumptions.should_force_symbolic_external_loads()
        && let Some(stored) = crate::kernel::memory_provenance::complete_pointer_read_retained_value(
            complete_read.designation(),
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
            Pointer::loaded_value(&crate::kernel::intern_memory_ref(memory), &address),
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
        && matches!(
            pointer_value.pointer().block,
            PointerBlock::LoadedPointer(_)
        )
    {
        let retained_state = crate::kernel::intern_memory_ref(memory);
        let bits = MachineTerm::MemoryLoad(
            retained_state.clone(),
            Box::new(address.clone()),
            LoadKind::Int32,
        );
        let (fresh, load) = load_variable_for_term(&bits)?;
        record_load_variable_defining_fact_with_source_and_pointer(
            fresh, load, facts, source, None,
        );
        return Some(
            (ProgramValue::Pointer(PointerValue::from_read(
                Pointer::symbolic(fresh),
                value_type,
                &retained_state,
                &address,
            )))
            .into(),
        );
    }
    Some(value.into())
}

const LOAD_VARIABLE_BASE: u64 = 1 << 40;
const LOAD_VARIABLE_RANGE_SIZE: u64 = 1 << 40;
#[allow(
    dead_code,
    reason = "the typed load producer migrates after this identity foundation"
)]
const POINTER_LOAD_ID_RANGE: u64 = 1 << 40;

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
pub(crate) fn typed_pointer_read_variable(value: &Pointer) -> Option<Variable> {
    Some(match (&value.block, &value.offset) {
        (
            PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable),
            PointerOffsetTerm::Constant(0),
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
    LOAD_VARIABLE_RANGE.contains(&variable.0)
}

/// Whether a proposition is a load-variable defining equation
/// (a reserved read handle equated to its own structural read). Raw
/// descriptors remain recognized for retained internal equations. These
/// equations are true by construction, so path wrapping treats them as
/// ambient truths rather than premises.
pub(crate) fn is_load_variable_defining_fact(proposition: &Proposition) -> bool {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: _,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        true,
    ) = proposition
    else {
        return false;
    };
    match (left.as_ref(), right.as_ref()) {
        (MachineTerm::Variable(variable), MachineTerm::MemoryLoad(_, _, _)) => {
            is_load_variable(variable)
        }
        (MachineTerm::Variable(variable), MachineTerm::Variable(read)) => {
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
    address: Option<crate::kernel::SharedPointerAddress>,
    /// Shared structural forms of this immutable descriptor. Capture/restore
    /// keeps them with the entry they describe; origins and widths do not
    /// change the value. None records an unmigrated native address payload.
    terms: std::collections::HashMap<MachineIntegerType, Option<crate::kernel::KernelTerm>>,
    /// The canonical state, address and kind: the load itself.
    memory: SharedMemory,
    pointer: Pointer,
    kind: LoadKind,
    /// Observation ownership is independent of this compatibility name.
    observation: read_observations::Id,
}

thread_local! {
    // Latest complete pointer and wide-word reads, indexed by value and
    // function epoch. Observations never change the defining name.
    // Persistent roots keep session capture/restore from copying the table.
    static POINTER_READ_OBSERVATIONS: std::cell::RefCell<
        imbl::HashMap<(u64, Pointer), (SharedMemory, Pointer)>,
    > = std::cell::RefCell::new(imbl::HashMap::new());
    static WIDE_LOAD_OBSERVATIONS: std::cell::RefCell<
        imbl::HashMap<(u64, Variable), (SharedMemory, Pointer)>,
    > = std::cell::RefCell::new(imbl::HashMap::new());
    /// Separate pointer-valued load names. The defining key is one canonical
    /// state and address at the fixed eight-byte pointer interpretation;
    /// neither a scalar load variable nor its mutable maximum access width
    /// decides membership in this registry.
    static POINTER_LOAD_REGISTRY: std::cell::RefCell<
        std::collections::HashMap<PointerLoadId, (SharedMemory, Pointer)>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    /// The read observation a pointer-load name was first produced from, whose
    /// epoch-scoped live origin answers what existed when the value was read
    /// (`loaded_pointer_read_predates_block`). The defining state cannot:
    /// it may be a canonical projection that keeps only the load's own block.
    static POINTER_LOAD_SOURCES: std::cell::RefCell<
        std::collections::HashMap<PointerLoadId, read_observations::Id>,
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
        std::collections::HashMap<MachineTerm, (Variable, MachineTerm)>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    // The flag retains whether version selection used an observed width.
    // Such hits need no second metadata lookup; widening clears this cache.
    static SCALAR_READ_IDENTITY_CACHE: std::cell::RefCell<
        std::collections::HashMap<MachineTerm, (ScalarReadComparisonIdentity, bool)>,
    > = Default::default();
    static TERM_CACHE: std::cell::RefCell<
        std::collections::HashMap<MachineTerm, MachineTerm>,
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
    pointer_observations: imbl::HashMap<(u64, Pointer), (SharedMemory, Pointer)>,
    wide_observations: imbl::HashMap<(u64, Variable), (SharedMemory, Pointer)>,
    variables: std::collections::HashMap<Variable, RegisteredLoad>,
    read_observations: read_observations::State,
    pointers: std::collections::HashMap<PointerLoadId, (SharedMemory, Pointer)>,
    pointer_sources: std::collections::HashMap<PointerLoadId, read_observations::Id>,
    widths: std::collections::HashMap<(SharedMemory, Pointer), u32>,
    widths_at_address: std::collections::HashMap<Pointer, u32>,
    origin_epoch: u64,
    logical_pointer_reads: crate::kernel::equality_graph::LogicalPointerReadsState,
}

/// How many load and pointer-load names are registered.
#[cfg(test)]
pub(crate) fn load_registry_entry_count() -> usize {
    LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow().len())
        + POINTER_LOAD_REGISTRY.with(|registry| registry.borrow().len())
}

pub(crate) fn capture_load_variable_registry() -> LoadRegistryState {
    LoadRegistryState {
        pointer_observations: POINTER_READ_OBSERVATIONS.with(|registry| registry.borrow().clone()),
        wide_observations: WIDE_LOAD_OBSERVATIONS.with(|registry| registry.borrow().clone()),
        variables: LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow().clone()),
        read_observations: read_observations::capture(),
        pointers: POINTER_LOAD_REGISTRY.with(|registry| registry.borrow().clone()),
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
    POINTER_LOAD_REGISTRY.with(|registry| *registry.borrow_mut() = state.pointers.clone());
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
    POINTER_LOAD_REGISTRY.with(|registry| registry.borrow_mut().clear());
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
pub(crate) fn read_over_write_value(term: &MachineTerm) -> Option<MachineTerm> {
    let MachineTerm::MemoryLoad(memory, pointer, kind) = viewed_as_memory_load(term)? else {
        return None;
    };
    let stored = memory
        .known_value(&pointer)
        .or_else(|| memory.known_value(&stored_pointer_address(&pointer)?))?;
    let read = kind.read_cell(&stored)?;
    let value = crate::kernel::spec::program_value_bitvector_term(&read)?;
    (value != *term).then_some(value)
}

/// `address` with its base read through the pointer read-over-write
/// authority: an address offset from a pointer read whose state stores a
/// pointer at the read's address is that pointer, offset alike. Both steps
/// read memory, never facts.
fn stored_pointer_address(address: &Pointer) -> Option<Pointer> {
    let PointerBlock::LoadedPointer(_) = &address.block else {
        return None;
    };
    let read = Pointer {
        block: address.block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let stored = pointer_read_over_write_value(&read)?;
    Some(Pointer {
        block: stored.block,
        offset: PointerOffsetTerm::add(stored.offset, address.offset.clone()),
    })
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
/// spelled and written (`docs/internals/spellability.md`); two facts that
/// differ only by a read on one side and its stored value on the other are
/// one fact. Exact matching therefore compares comparison forms: the fact
/// stores file each fact under its comparison form as well as its own
/// (`ProofFacts::with_fact`, `PureFactContext::assume_condition_once`), an
/// exact lookup also asks for the comparison form of what it looks up, and a
/// kernel rule that compares a stated term with the one it derives compares
/// their comparison forms. This is the one place the authority enters
/// matching; a check does not resolve reads on its own.
pub(crate) fn comparison_form(proposition: &Proposition) -> Option<Proposition> {
    if crate::instrumentation::deadline_exceeded_with_work(0) {
        return None;
    }
    if let Some(result) = COMPARISON_FORMS.with(|cache| cache.borrow().get(proposition).cloned()) {
        return result;
    }
    let result = comparison_form_uncached(proposition);
    if crate::instrumentation::deadline_exceeded_with_work(0) {
        return None;
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

fn comparison_form_uncached(proposition: &Proposition) -> Option<Proposition> {
    // Memory states stay opaque: only the proposition's own terms are
    // visited, never the cells of a state a read names.
    let mut collector =
        crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector::uncharged();
    collector.collect_read_terms();
    collector.collect(proposition);
    let mut variables = std::collections::BTreeSet::new();
    collector.extend_into(&mut variables);
    let reads = collector.take_read_terms().collect::<Vec<_>>();
    // A read of a library or enum value is the value its state stores
    // at that address, as a scalar read is: one cell lookup, no walk.
    let algebraic_reads = reads
        .iter()
        .filter_map(|read| {
            let MachineTerm::MemoryLoad(memory, pointer, LoadKind::Bits64) = read else {
                return None;
            };
            let ProgramValue::Parameter(stored) = memory.known_value(pointer)? else {
                return None;
            };
            Some(((memory.arena_id(), pointer.as_ref().clone()), *stored))
        })
        .collect::<std::collections::HashMap<_, _>>();
    let replacements = variables
        .into_iter()
        .map(MachineTerm::Variable)
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
    if let Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), value) = &resolved {
        let left_value = pointer_read_over_write_value(left);
        let right_value = pointer_read_over_write_value(right);
        if left_value.is_some() || right_value.is_some() {
            let left = left_value.unwrap_or_else(|| left.as_ref().clone());
            let right = right_value.unwrap_or_else(|| right.as_ref().clone());
            // Two reads of one stored pointer compare equal; the comparison
            // form is a lookup aid, so it states that outright.
            let condition = if left == right {
                ConditionTerm::Constant(true)
            } else {
                ConditionTerm::pointer_equal(left, right)
            };
            resolved = Proposition::ConditionIs(condition, *value);
        }
    }
    // A pointer value carries a designation and an extent beside its address,
    // so each read side resolves to the whole stored value, and the
    // comparison is rebuilt from the two values: equal addresses alone never
    // make two pointer values equal.
    if let Proposition::ConditionIs(ConditionTerm::PointerValueEqual(left, right), value) =
        &resolved
    {
        let resolve = |side: &PointerValue| {
            // The whole stored value defines the unmodified read. An
            // explicitly selected subobject or changed domain is a different
            // value even when it carries that same numeric read address.
            if side != &PointerValue::new(side.pointer().clone(), side.program_type()) {
                return None;
            }
            pointer_read_over_write_program_value(side.pointer())
                .map(|stored| stored.with_type(side.program_type()))
        };
        let (left_value, right_value) = (resolve(left), resolve(right));
        if left_value.is_some() || right_value.is_some() {
            let left = left_value.unwrap_or_else(|| left.as_ref().clone());
            let right = right_value.unwrap_or_else(|| right.as_ref().clone());
            let condition = match ConditionTerm::pointer_value_equal(left, right) {
                ConditionTerm::PointerEqual(left, right) if left == right => {
                    ConditionTerm::Constant(true)
                }
                condition => condition,
            };
            resolved = Proposition::ConditionIs(condition, *value);
        }
    }
    (&resolved != proposition).then_some(resolved)
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
pub(crate) fn pointer_read_over_immediate_store(pointer: &Pointer) -> Option<Pointer> {
    crate::instrumentation::record_deterministic_work(1);
    let read = pointer.as_loaded_value()?;
    if read.displacement != PointerOffsetTerm::Constant(0) {
        return None;
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
    (written == &read.defining_address).then(|| value.pointer().clone())
}

/// The read-over-write authority for a pointer read: the pointer stored at
/// the read's address in the state it reads, as a cell or as the pointer
/// view of a union cell, when that state records one. A cell holding the
/// read itself resolves to nothing.
pub(crate) fn pointer_read_over_write_value(pointer: &Pointer) -> Option<Pointer> {
    pointer_read_over_write_program_value(pointer).map(|stored| stored.pointer().clone())
}

/// The complete pointer stored at this read's address, when the state's
/// fact-free version walk establishes it. Retained caches alone are not evidence.
pub(crate) fn pointer_read_over_write_program_value(pointer: &Pointer) -> Option<PointerValue> {
    let read = pointer.as_loaded_value()?;
    if read.displacement != PointerOffsetTerm::Constant(0) {
        return None;
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
    (stored.pointer() != pointer).then_some(stored)
}

thread_local! {
    // [`memory_shown_cell_value`] is a function of the interned state, the
    // address and the width, so it is memoized per session; a query met again
    // while its own walk runs (the walk asks block distinctness, which asks
    // this) answers nothing rather than recursing.
    static MEMORY_SHOWN_CELLS: std::cell::RefCell<
        std::collections::HashMap<(SharedMemory, Pointer, u32), Option<ProgramValue>>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    static MEMORY_SHOWN_IN_PROGRESS: std::cell::RefCell<
        std::collections::HashSet<(SharedMemory, Pointer, u32)>,
    > = std::cell::RefCell::new(std::collections::HashSet::new());
}

/// Whether `memory` caches a whole pointer at exactly `address`, as a cell or
/// as a union cell's pointer view.
fn holds_pointer_cell(memory: &Memory, address: &Pointer) -> bool {
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
    address: &Pointer,
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
    address: &Pointer,
    bytes: u32,
) -> Option<ProgramValue> {
    // The read's own state must hold the cell: a projection interned from
    // several sources names its oldest, which need not be this read's.
    let held = memory
        .known_value(address)
        .or_else(|| memory.known_union_pointer(address))?;
    let source = crate::kernel::prelude::canonical_load_projection_source(memory, address)
        .unwrap_or_else(|| memory.clone());
    let last = crate::kernel::resource_tracker::last_same_named_cell(
        address,
        bytes,
        &crate::kernel::resource_tracker::VersionPoint::at(&source),
    )?;
    // The step the walk stopped at must have left the cached cell standing
    // for the cell's bytes by memory alone. A store elsewhere that overlaps
    // the cell changed some of them, whatever a cached cell still says; a
    // havoc keeps a cell only where a frame fact showed it separate, and that
    // fact, not the cache, is the authority for it.
    match last.point.shared_memory().derivation().as_deref() {
        Some(MemoryDerivation::Store { pointer, value, .. })
            if last.stopped_by.reason == crate::kernel::resource_tracker::StopReason::Affected
                && (pointer != address || value.byte_width() < bytes) =>
        {
            None
        }
        Some(MemoryDerivation::CallHavoc { .. } | MemoryDerivation::LoopHavoc { .. }) => None,
        // A step the walk could not show separate from the cell (a store or a
        // release through an unrelated address) left the cache standing only
        // where a fact shows it separate.
        _ if matches!(
            last.stopped_by.reason,
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
    let resolve = |term: &MachineTerm| read_over_write_value(term).unwrap_or(term.clone());
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
/// have triggered provenance evidence.
pub(crate) fn registered_load_for_variable(variable: &Variable) -> Option<(SharedMemory, Pointer)> {
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        registry
            .borrow()
            .get(variable)
            .map(|load| (load.memory.clone(), load.pointer.clone()))
    })
}

/// The load term a load variable names, kind included: the right-hand side
/// of its defining equation.
pub(crate) fn registered_load_term_for_variable(variable: &Variable) -> Option<MachineTerm> {
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        registry.borrow().get(variable).map(|load| {
            MachineTerm::MemoryLoad(
                load.memory.clone(),
                Box::new(load.pointer.clone()),
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
                        &read.memory,
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
    pub memory: SharedMemory,
    pub pointer: Pointer,
    pub kind: LoadKind,
    pub bytes: u32,
    pub origin: Option<SharedMemory>,
}

mod read_observations;
mod scalar_reads;

use scalar_reads::{ScalarReadComparisonIdentity, ScalarReadDescriptor};

pub(crate) fn scalar_read_observation(
    operand: crate::kernel::MachineOperandView<'_>,
) -> Option<ScalarReadObservation> {
    read_observations::for_operand(operand)
}

/// Build an exact read and publish its typed observation. This does not
/// select a comparison identity or change the supplied memory state. Use
/// `MachineTerm::memory_read` when no observation needs to be published.
pub(crate) fn scalar_read_for_exact_cell(
    memory: &SharedMemory,
    pointer: &Pointer,
    kind: LoadKind,
    bytes: u32,
) -> MachineTerm {
    let id = read_observations::record(memory, pointer, kind, memory, bytes);
    read_observations::select(id);
    MachineTerm::memory_read(memory.clone(), pointer.clone(), kind)
}

pub(crate) fn is_selected_scalar_read(
    memory: &SharedMemory,
    pointer: &Pointer,
    kind: LoadKind,
) -> bool {
    read_observations::selected(memory, pointer, kind)
}

/// Existing observation metadata is evidence of an access width too. Merely
/// inspecting a retained read must not replace it with the unknown-width default.
fn existing_read_access_width(
    memory: &SharedMemory,
    pointer: &Pointer,
    kind: LoadKind,
) -> Option<u32> {
    read_observations::existing(memory, pointer, kind).and_then(read_observations::bytes)
}

/// The kind of read a load variable names.
pub(crate) fn registered_load_kind_for_variable(variable: &Variable) -> Option<LoadKind> {
    LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow().get(variable).map(|load| load.kind))
}

/// Intern an eight-byte pointer load by its assumption-free defining
/// state and address. Hashing only chooses a candidate slot: a collision
/// probes until the full key matches or an unused slot is found.
#[allow(
    dead_code,
    reason = "the typed load producer migrates after this identity foundation"
)]
pub(crate) fn pointer_load_identity(memory: &SharedMemory, address: &Pointer) -> PointerLoadId {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    memory.arena_id().hash(&mut hasher);
    address.hash(&mut hasher);
    let mut slot = hasher.finish() % POINTER_LOAD_ID_RANGE;
    POINTER_LOAD_REGISTRY.with(|registry| {
        let mut registry = registry.borrow_mut();
        loop {
            let identity = PointerLoadId(slot);
            match registry.get(&identity) {
                Some((known_memory, known_address))
                    if known_memory.arena_id() == memory.arena_id() && known_address == address =>
                {
                    return identity;
                }
                Some(_) => {
                    crate::instrumentation::record_deterministic_work(1);
                    slot = (slot + 1) % POINTER_LOAD_ID_RANGE;
                }
                None => {
                    assert!(
                        registry.len() < LOAD_VARIABLE_REGISTRY_CAPACITY,
                        "pointer-load registry capacity exhausted"
                    );
                    registry.insert(identity, (memory.clone(), address.clone()));
                    return identity;
                }
            }
        }
    })
}

/// The block a pointer read's value lies in by the read-over-write authority:
/// the block of the pointer memory alone shows stored at the read's address
/// (`memory_shown_cell_value`). `None` when memory shows no pointer there.
pub(crate) fn loaded_pointer_stored_block(identity: PointerLoadId) -> Option<PointerBlock> {
    let mut current = identity;
    let mut path = Vec::new();
    let (terminal, complete) = loop {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(cached) =
            STORED_POINTER_BLOCKS.with(|cache| cache.borrow().get(&current).cloned())
        {
            break (
                Some(cached.unwrap_or(PointerBlock::LoadedPointer(current))),
                true,
            );
        }
        if !STORED_POINTER_BLOCKS_RUNNING.with(|running| running.borrow_mut().insert(current)) {
            // A memory naming walk can ask about the read it is resolving.
            // That recursive question supplies no definition and is not memoized.
            break (None, false);
        }
        path.push(current);
        match immediate_stored_pointer_block(current) {
            Some(PointerBlock::LoadedPointer(next)) => current = next,
            Some(block) => break (Some(block), true),
            None => break (Some(PointerBlock::LoadedPointer(current)), true),
        }
    };
    for read in path {
        STORED_POINTER_BLOCKS_RUNNING.with(|running| running.borrow_mut().remove(&read));
        if complete {
            let value = terminal
                .clone()
                .filter(|block| *block != PointerBlock::LoadedPointer(read));
            STORED_POINTER_BLOCKS.with(|cache| cache.borrow_mut().insert(read, value));
        }
    }
    terminal.filter(|block| *block != PointerBlock::LoadedPointer(identity))
}

thread_local! {
    static STORED_POINTER_BLOCKS: std::cell::RefCell<std::collections::HashMap<PointerLoadId, Option<PointerBlock>>> = std::cell::RefCell::new(std::collections::HashMap::new());
    static STORED_POINTER_BLOCKS_RUNNING: std::cell::RefCell<std::collections::HashSet<PointerLoadId>> = std::cell::RefCell::new(std::collections::HashSet::new());
}

fn immediate_stored_pointer_block(identity: PointerLoadId) -> Option<PointerBlock> {
    let (memory, address) = registered_pointer_load(identity)?;
    if !holds_pointer_cell(memory.memory(), &address) {
        return None;
    }
    let ProgramValue::Pointer(stored) =
        memory_shown_cell_value(&memory, &address, crate::kernel::C_POINTER_BYTE_WIDTH)?
    else {
        return None;
    };
    (stored.pointer().block != PointerBlock::LoadedPointer(identity))
        .then(|| stored.pointer().block.clone())
}

/// Decode a pointer-load name without consulting scalar-load metadata.
pub(crate) fn registered_pointer_load(identity: PointerLoadId) -> Option<(SharedMemory, Pointer)> {
    POINTER_LOAD_REGISTRY.with(|registry| registry.borrow().get(&identity).cloned())
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
        std::collections::HashMap<(SharedMemory, Pointer), u32>,
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
        std::collections::HashMap<Pointer, u32>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// Remembers that a load of `bytes` bytes happens at this address in this
/// state. Widening on conflict: the entry has to cover every access that
/// resolves through it. A declared array element counts as already recorded
/// at its declared width.
pub(in crate::kernel) fn record_load_access_width(memory: &Memory, pointer: &Pointer, bytes: u32) {
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
pub(in crate::kernel) fn declare_load_access_width(pointer: &Pointer, bytes: u32) {
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
pub(crate) fn recorded_load_access_width(memory: &SharedMemory, pointer: &Pointer) -> Option<u32> {
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
fn recorded_load_access_width_at_address(pointer: &Pointer) -> Option<u32> {
    LOAD_ACCESS_WIDTH_AT_ADDRESS.with(|widths| widths.borrow().get(pointer).copied())
}

/// The access width to use for a load named only by a term.
pub(crate) fn load_access_width_or_widest(memory: &SharedMemory, pointer: &Pointer) -> u32 {
    recorded_load_access_width(memory, pointer)
        .unwrap_or_else(crate::kernel::resource_tracker::widest_scalar_access_bytes)
}

/// The access width a framing walk uses for a `kind` read at this address:
/// the width recorded there, never narrower than the read itself.
pub(crate) fn load_term_access_width(
    memory: &SharedMemory,
    pointer: &Pointer,
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
/// `Memory` it would have to intern only to ask the question, where the C
/// type at the address is the whole answer anyway: every framing comparison
/// runs at a state later than the load it is carrying, so the exact key
/// would miss and fall through to this table regardless.
pub(crate) fn load_access_width_at_address_or_widest(pointer: &Pointer) -> u32 {
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
) -> Option<(SharedMemory, Pointer)> {
    let read = scalar_read_observation(crate::kernel::MachineOperandView::Legacy(
        &MachineTerm::Variable(*variable),
    ))?;
    Some((read.origin?, read.pointer))
}

/// [`registered_load_origin_for_variable`] as the load term it names there:
/// the same read, kind included, at the live origin.
pub(crate) fn registered_load_origin_term_for_variable(variable: &Variable) -> Option<MachineTerm> {
    let (origin, pointer) = registered_load_origin_for_variable(variable)?;
    let kind = registered_load_kind_for_variable(variable)?;
    Some(MachineTerm::MemoryLoad(origin, Box::new(pointer), kind))
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
pub(crate) fn loaded_pointer_predates_block(variable: &Variable, block: &PointerBlock) -> bool {
    if !block.is_local_block() && !matches!(block, PointerBlock::Heap(_)) {
        return false;
    }
    let Some((origin, _)) = registered_load_origin_for_variable(variable) else {
        return false;
    };
    match block {
        PointerBlock::Heap(identity) => !origin.heap_identity_allocated(*identity),
        _ => !origin.has_block(block) && !origin.forgotten.ended_local_blocks.contains(block),
    }
}

/// Retain the selected read's observation independently of any scalar name.
pub(crate) fn record_pointer_load_source(identity: PointerLoadId, read: &MachineTerm) {
    let MachineTerm::MemoryLoad(memory, address, kind) = read else {
        return;
    };
    if let Some(observation) = read_observations::existing(memory, address, *kind) {
        POINTER_LOAD_SOURCES.with(|sources| {
            sources.borrow_mut().entry(identity).or_insert(observation);
        });
    }
}

fn pointer_load_origin(identity: PointerLoadId) -> Option<SharedMemory> {
    let observation =
        POINTER_LOAD_SOURCES.with(|sources| sources.borrow().get(&identity).copied())?;
    read_observations::observation(observation)?.origin
}

pub(crate) fn loaded_pointer_read_predates_block(
    identity: PointerLoadId,
    block: &PointerBlock,
) -> bool {
    if !block.is_local_block() && !matches!(block, PointerBlock::Heap(_)) {
        return false;
    }
    let Some(origin) = pointer_load_origin(identity) else {
        return false;
    };
    match block {
        PointerBlock::Heap(identity) => !origin.heap_identity_allocated(*identity),
        _ => !origin.has_block(block) && !origin.forgotten.ended_local_blocks.contains(block),
    }
}

pub(crate) fn loaded_pointer_read_heap_identities(identity: PointerLoadId) -> Option<Vec<u64>> {
    Some(pointer_load_origin(identity)?.allocated_heap_identities())
}

/// Views a term as a memory load for equality reasoning: load terms pass
/// through, and registered load variables resolve to the loads they
/// represent. Other terms are not loads.
pub(crate) fn viewed_as_memory_load(term: &MachineTerm) -> Option<MachineTerm> {
    match term {
        MachineTerm::MemoryLoad(_, _, _) => Some(term.clone()),
        MachineTerm::Variable(variable) => registered_load_term_for_variable(variable),
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

/// Whether the selected proposition contains a state-bearing scalar read,
/// in structural form or through the transitional registered name.
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

/// The comparison form: assumption-free read-over-write canonicalization
/// followed by structural selection of unresolved scalar reads. This is a
/// checker operation; lowering retains the read even when its value is known.
/// Deterministic and idempotent. The traversal is linear and uses explicit
/// worklists. Shallow terms are memoized; deep terms bypass the recursive
/// structural key and take the same complete path directly.
///
/// [`canonicalize_atomic_loads`]: crate::kernel::memory_provenance::canonicalize_atomic_loads
pub(crate) fn canonical_term(term: &MachineTerm) -> MachineTerm {
    let cacheable = crate::kernel::memory_provenance::term_is_shallow_structural_cache_key(term);
    if cacheable && let Some(hit) = TERM_CACHE.with(|cache| cache.borrow().get(term).cloned()) {
        return hit;
    }
    let structural = crate::kernel::memory_provenance::canonicalize_atomic_loads(term);
    // Register the live observation before its projected form can claim the
    // load's origin. Keep the established projected canonical identity.
    if matches!(term, MachineTerm::MemoryLoad(..))
        && matches!(structural, MachineTerm::MemoryLoad(..))
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
pub(crate) fn canonical_offset_term(offset: &PointerOffsetTerm) -> PointerOffsetTerm {
    enum Task<'a> {
        Visit(&'a PointerOffsetTerm),
        RebuildAdd,
    }
    let mut tasks = vec![Task::Visit(offset)];
    let mut results = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(offset) => match offset {
                PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {
                    results.push(offset.clone())
                }
                PointerOffsetTerm::Add(left, right) => {
                    tasks.push(Task::RebuildAdd);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                }
                PointerOffsetTerm::Int32Scaled { value, .. }
                | PointerOffsetTerm::Int64Scaled { value, .. }
                    if value.shared_operand().is_some() =>
                {
                    // This child was constructed already. Reopening its read
                    // would change its identity and repeatedly walk its prefix.
                    results.push(offset.clone());
                }
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    results.push(PointerOffsetTerm::scale_int32(
                        canonical_term(
                            value
                                .retained_written_operand()
                                .expect("shared indices handled above"),
                        ),
                        *byte_width,
                    ));
                }
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => results.push(PointerOffsetTerm::scale_int64(
                    canonical_term(
                        value
                            .retained_written_operand()
                            .expect("shared indices handled above"),
                    ),
                    *byte_width,
                    *unsigned,
                )),
            },
            Task::RebuildAdd => {
                let right = results.pop().expect("visited right offset");
                let left = results.pop().expect("visited left offset");
                results.push(PointerOffsetTerm::add(left, right));
            }
        }
    }
    results.pop().expect("canonicalization produces one offset")
}

/// Keep an index's read structure at the producer boundary.
pub(crate) fn canonicalized_offset_index_term(
    bits: MachineTerm,
    _facts: &mut ExecutionFacts,
) -> MachineTerm {
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
/// `MachineTerm::memory_read`; this adapter still retains the comparison
/// identity as the read term until those callers migrate to exact states.
pub(crate) fn canonical_form_of_load(
    memory: SharedMemory,
    pointer: Pointer,
    kind: LoadKind,
) -> MachineTerm {
    canonical_scalar_read(&MachineTerm::memory_read(memory, pointer, kind))
}

/// Resource cells retain structural descriptors for integers and pointers.
pub(crate) fn canonical_cell_load(
    memory: SharedMemory,
    pointer: Pointer,
    ty: ProgramType,
) -> MachineTerm {
    let kind = LoadKind::of_type(ty).expect("scalar cell read kind");
    let read = MachineTerm::memory_read(memory, pointer, kind);
    canonical_scalar_read(&read)
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
pub(crate) fn check_canonical_at_creation(condition: &ConditionTerm, value: bool) {
    thread_local! {
        static SEEN: std::cell::RefCell<std::collections::BTreeSet<(String, String)>> =
            const { std::cell::RefCell::new(std::collections::BTreeSet::new()) };
    }
    if !CANONICAL_AT_CREATION_VIOLATIONS.with(|count| count.get().is_some()) {
        return;
    }
    let proposition = Proposition::ConditionIs(condition.clone(), value);
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
        "ProofFacts::",
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
pub(crate) fn is_store_fact(condition: &ConditionTerm, value: bool) -> bool {
    if !value {
        return false;
    }
    let ConditionTerm::Compare {
        format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
        relation: CompareRelation::Equal,
        left,
        right,
    } = condition
    else {
        return false;
    };
    let (load, stored) = match (left.as_ref(), right.as_ref()) {
        (MachineTerm::MemoryLoad(memory, pointer, kind), stored)
        | (stored, MachineTerm::MemoryLoad(memory, pointer, kind)) => {
            ((memory, pointer, kind), stored)
        }
        _ => return false,
    };
    let Some(value) = load.0.known_value(load.1) else {
        return false;
    };
    matches!(
        load.2.read_cell(&value),
        Some(crate::kernel::integer32_c_value!(recorded)) if &recorded == stored
    )
}

/// The canonical form for a condition: every operand takes its
/// [`canonical_term`] form, so terms that are equal by definition compare
/// identically. The comparison direction of the canonical model for
/// whole facts.
pub(crate) fn canonical_condition(condition: &ConditionTerm) -> ConditionTerm {
    match condition {
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => condition.clone(),
        ConditionTerm::AlgebraicEqual(_, _) | ConditionTerm::PointerValueEqual(..) => {
            condition.clone()
        }
        // `Bool` values are kept as built, as algebraic equalities are.
        condition if condition.is_bool_value_form() => condition.clone(),
        ConditionTerm::Float32(float_condition) => {
            ConditionTerm::Float32(float_condition.map_bitvector_terms(canonical_term))
        }
        ConditionTerm::Float64(float_condition) => {
            ConditionTerm::Float64(float_condition.map_bitvector_terms(canonical_term))
        }
        ConditionTerm::PointerOffsetEqual(left, right) => ConditionTerm::PointerOffsetEqual(
            Box::new(canonical_offset_term(left)),
            Box::new(canonical_offset_term(right)),
        ),
        ConditionTerm::PointerEqual(left, right) => ConditionTerm::PointerEqual(
            Box::new(Pointer {
                block: left.block.clone(),
                offset: canonical_offset_term(&left.offset),
            }),
            Box::new(Pointer {
                block: right.block.clone(),
                offset: canonical_offset_term(&right.offset),
            }),
        ),
        crate::kernel::integer_comparison_condition!(_, _) => condition.clone(),
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
    Proposition::ConditionIs(canonical_condition(condition), *value)
}

/// Select unresolved read descriptors with an explicit worklist. Range-fold
/// bodies remain scoped and are not assigned a global read identity.
fn select_scalar_reads(term: &MachineTerm) -> MachineTerm {
    enum Task<'a> {
        VisitTerm(&'a MachineTerm),
        VisitCondition(&'a ConditionTerm),
        VisitOffset(&'a PointerOffsetTerm),
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
                    bits32_constant!(_)
                    | int64_constant!(_)
                    | uint64_constant!(_)
                    | native_constant!(_, _) => term_results.push(term.clone()),
                    MachineTerm::Variable(variable) => {
                        term_results.push(
                            registered_load_term_for_variable(variable)
                                .unwrap_or_else(|| term.clone()),
                        );
                    }
                    MachineTerm::MemoryLoad(_, _, _) => {
                        term_results.push(canonical_scalar_read(term));
                    }
                    MachineTerm::PointerAddress(_, _) | MachineTerm::IntegerToMachine { .. } => {
                        term_results.push(term.clone())
                    }
                    MachineTerm::ClickFunctionApplication { .. }
                    | MachineTerm::AlgebraicMatch { .. } => term_results.push(term.clone()),
                    MachineTerm::If {
                        condition,
                        then_term,
                        else_term,
                    } => {
                        tasks.push(Task::RebuildIf);
                        tasks.push(Task::VisitTerm(else_term));
                        tasks.push(Task::VisitTerm(then_term));
                        tasks.push(Task::VisitCondition(condition));
                    }
                    MachineTerm::BoolCast { to, value } => {
                        tasks.push(Task::RebuildBoolCast(*to));
                        tasks.push(Task::VisitCondition(value));
                    }
                    // A fold is a binder boundary: loads in its body can mention
                    // bound variables and therefore do not have a global load
                    // identity. Preserve the whole scoped term verbatim.
                    MachineTerm::RangeFold { .. } => term_results.push(term.clone()),
                    MachineTerm::PureFunctionApplication { name, arguments } => {
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
                ConditionTerm::AlgebraicEqual(_, _) | ConditionTerm::PointerValueEqual(..) => {
                    condition_results.push(condition.clone())
                }
                // `Bool` values keep their reads, as algebraic equalities do.
                condition if condition.is_bool_value_form() => {
                    condition_results.push(condition.clone())
                }
                crate::kernel::integer_comparison_condition!(_, _) => {
                    condition_results.push(condition.clone())
                }
                ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {
                    condition_results.push(condition.clone())
                }
                ConditionTerm::Float32(float_condition) => {
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
                ConditionTerm::Float64(float_condition) => {
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
                ConditionTerm::PointerOffsetEqual(left, right) => {
                    tasks.push(Task::RebuildPointerOffsetEqual);
                    tasks.push(Task::VisitOffset(right));
                    tasks.push(Task::VisitOffset(left));
                }
                ConditionTerm::PointerEqual(left, right) => {
                    tasks.push(Task::RebuildPointerEqual {
                        left_block: left.block.clone(),
                        right_block: right.block.clone(),
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
            Task::VisitOffset(offset) => match offset {
                PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {
                    offset_results.push(offset.clone())
                }
                PointerOffsetTerm::Add(left, right) => {
                    tasks.push(Task::RebuildOffsetAdd);
                    tasks.push(Task::VisitOffset(right));
                    tasks.push(Task::VisitOffset(left));
                }
                PointerOffsetTerm::Int32Scaled { value, .. }
                | PointerOffsetTerm::Int64Scaled { value, .. }
                    if value.shared_operand().is_some() =>
                {
                    // This child was constructed already. Reopening its read
                    // would change its identity and repeatedly walk its prefix.
                    offset_results.push(offset.clone());
                }
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    tasks.push(Task::RebuildInt32Scaled(*byte_width));
                    tasks.push(Task::VisitTerm(
                        value
                            .retained_written_operand()
                            .expect("shared indices handled above"),
                    ));
                }
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => {
                    tasks.push(Task::RebuildInt64Scaled {
                        byte_width: *byte_width,
                        unsigned: *unsigned,
                    });
                    tasks.push(Task::VisitTerm(
                        value
                            .retained_written_operand()
                            .expect("shared indices handled above"),
                    ));
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
                term_results.push(MachineTerm::BoolCast {
                    to,
                    value: Box::new(value),
                });
            }
            Task::RebuildIf => {
                let else_term = term_results.pop().expect("visited else term");
                let then_term = term_results.pop().expect("visited then term");
                let condition = condition_results.pop().expect("visited condition");
                term_results.push(MachineTerm::If {
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
                term_results.push(MachineTerm::PureFunctionApplication { name, arguments });
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
                    ConditionTerm::Float64(rebuilt)
                } else {
                    ConditionTerm::Float32(rebuilt)
                });
            }
            Task::RebuildPointerOffsetEqual => {
                let right = offset_results.pop().expect("visited right pointer offset");
                let left = offset_results.pop().expect("visited left pointer offset");
                condition_results.push(ConditionTerm::PointerOffsetEqual(
                    Box::new(left),
                    Box::new(right),
                ));
            }
            Task::RebuildPointerEqual {
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
            Task::RebuildOffsetAdd => {
                let right = offset_results.pop().expect("visited right pointer offset");
                let left = offset_results.pop().expect("visited left pointer offset");
                offset_results.push(PointerOffsetTerm::add(left, right));
            }
            Task::RebuildInt32Scaled(byte_width) => {
                let value = term_results.pop().expect("visited scaled term");
                offset_results.push(PointerOffsetTerm::scale_int32(value, byte_width));
            }
            Task::RebuildInt64Scaled {
                byte_width,
                unsigned,
            } => {
                let value = term_results.pop().expect("visited scaled term");
                offset_results.push(PointerOffsetTerm::scale_int64(value, byte_width, unsigned));
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
pub(crate) fn terms_have_same_canonical_form(left: &MachineTerm, right: &MachineTerm) -> bool {
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
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
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
        let V::Legacy(term) = operand else {
            unreachable!()
        };
        return term_mentions_a_memory_load(term);
    };
    if operand.read().is_some() {
        return true;
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
        ) || term_mentions_a_memory_load(leaf.machine_conversion_leaf().expect("conversion leaf"))
    })
}

pub(in crate::kernel) fn term_mentions_a_memory_load(term: &MachineTerm) -> bool {
    match term {
        bits32_constant!(_)
        | MachineTerm::Variable(_)
        | int64_constant!(_)
        | uint64_constant!(_)
        | native_constant!(_, _) => false,
        MachineTerm::MemoryLoad(_, _, _) => true,
        MachineTerm::PointerAddress(pointer, _) => pointer
            .offset
            .any_scaled_operand(|value| operand_mentions_a_memory_load(value.operand_view())),
        MachineTerm::If {
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
        MachineTerm::RangeFold { .. } => true,
        MachineTerm::PureFunctionApplication { name: _, arguments } => {
            arguments.iter().any(term_mentions_a_memory_load)
        }
        MachineTerm::ClickFunctionApplication { .. } => true,
        MachineTerm::AlgebraicMatch { arms, .. } => arms
            .iter()
            .any(|arm| term_mentions_a_memory_load(&arm.body)),
        MachineTerm::IntegerToMachine { .. } => true,
        MachineTerm::BoolCast { value, .. } => condition_mentions_a_memory_load(value),
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

fn condition_mentions_a_memory_load(condition: &ConditionTerm) -> bool {
    match condition {
        ConditionTerm::PointerValueEqual(left, right) => {
            left.pointers().chain(right.pointers()).any(|p| {
                p.offset.any_scaled_operand(|value| {
                    operand_mentions_a_memory_load(value.operand_view())
                })
            })
        }

        // Until memory canonicalization traverses ADTs, conservatively disable
        // the memory-free fast path for this logical condition.
        ConditionTerm::AlgebraicEqual(_, _) => true,
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => false,
        crate::kernel::binary_bitvector_condition!(left, right) => {
            term_mentions_a_memory_load(left) || term_mentions_a_memory_load(right)
        }
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            let mut mentions = false;
            float_condition.for_each_bitvector_term(|term| {
                mentions |= term_mentions_a_memory_load(term);
            });
            mentions
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            offset_mentions_a_memory_load(left) || offset_mentions_a_memory_load(right)
        }
        ConditionTerm::PointerEqual(left, right) => {
            offset_mentions_a_memory_load(&left.offset)
                || offset_mentions_a_memory_load(&right.offset)
        }
        crate::kernel::integer_comparison_condition!(_, _) => false,
        ConditionTerm::BoolApplication(_) | ConditionTerm::BoolLoad(..) => true,
        ConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => [condition, then_condition, else_condition]
            .into_iter()
            .any(|condition| condition_mentions_a_memory_load(condition)),
        ConditionTerm::BoolEqual(left, right) => {
            condition_mentions_a_memory_load(left) || condition_mentions_a_memory_load(right)
        }
    }
}

fn offset_mentions_a_memory_load(offset: &PointerOffsetTerm) -> bool {
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
    pointer: &Pointer,
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
    pointer: &Pointer,
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
    pointer: &Pointer,
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
        crate::kernel::resource_tracker::TrackedResource::Cell { pointer, bytes },
        &crate::kernel::resource_tracker::VersionPoint::at(memory),
    )
    .map(|point| point.shared_memory().clone());
    let memory = version.as_ref().unwrap_or(memory);
    #[cfg(test)]
    duplicate_read_names::observe(memory, pointer, kind);
    mint_load_variable_identity(memory, pointer, kind, origin, bytes)
}

/// A test-only audit of one read, one name (`docs/internals/spellability.md`):
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
        seen: std::collections::HashMap<(u64, Pointer, LoadKind), Vec<SharedMemory>>,
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

    pub(super) fn observe(version: &SharedMemory, pointer: &Pointer, kind: LoadKind) {
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
            MachineTerm::MemoryLoad(memory.clone(), Box::new(pointer.clone()), kind)
        };
        let empty = PureFactContext::new();
        let duplicate = earlier.iter().any(|earlier| {
            !(stored.is_some() && earlier.memory().known_value(pointer) == stored)
                && crate::kernel::memory_provenance::checked_atomic_load_equality(
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
    pointer: &Pointer,
    kind: LoadKind,
    origin: &SharedMemory,
    bytes: u32,
) -> Variable {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    memory.hash(&mut hasher);
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
                    memory: known_memory,
                    pointer: known_pointer,
                    kind: known_kind,
                    observation,
                    ..
                }) if known_memory == memory && known_pointer == pointer && *known_kind == kind => {
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
                            memory: memory.clone(),
                            pointer: pointer.clone(),
                            kind,
                            observation: {
                                let id =
                                    read_observations::record(memory, pointer, kind, origin, bytes);
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
fn record_wide_load_observation(term: &MachineTerm, variable: Variable) {
    let MachineTerm::MemoryLoad(memory, pointer, LoadKind::Bits64) = term else {
        return;
    };
    if registered_load_kind_for_variable(&variable) != Some(LoadKind::Bits64) {
        return;
    }
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    crate::instrumentation::record_deterministic_work(1);
    WIDE_LOAD_OBSERVATIONS.with(|registry| {
        let mut registry = registry.borrow_mut();
        let key = (epoch, variable);
        if registry
            .get(&key)
            .is_some_and(|(known_memory, known_pointer)| {
                known_memory == memory && known_pointer == pointer.as_ref()
            })
        {
            return;
        }
        crate::instrumentation::record_deterministic_work(1);
        registry.insert(key, (memory.clone(), pointer.as_ref().clone()));
    });
}

// Only a typed producer records an unconditional pointer-read expression.
fn record_pointer_read_observation(value: &Pointer, memory: &Memory, address: &Pointer) {
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

pub(crate) fn latest_pointer_read_observation(value: &Pointer) -> Option<(SharedMemory, Pointer)> {
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    crate::instrumentation::record_deterministic_work(1);
    POINTER_READ_OBSERVATIONS
        .with(|registry| registry.borrow().get(&(epoch, value.clone())).cloned())
}

pub(crate) fn latest_wide_load_observation(variable: &Variable) -> Option<MachineTerm> {
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    crate::instrumentation::record_deterministic_work(1);
    WIDE_LOAD_OBSERVATIONS.with(|registry| {
        registry
            .borrow()
            .get(&(epoch, *variable))
            .map(|(memory, pointer)| {
                MachineTerm::MemoryLoad(memory.clone(), Box::new(pointer.clone()), LoadKind::Bits64)
            })
    })
}

/// Compatibility adapter for the existing selected-version read policy.
/// Exact construction, comparison identity selection, and observation
/// publication are separate operations. Until exact-state lowering migrates,
/// callers still retain the selected identity as their read term.
pub(in crate::kernel) fn canonical_scalar_read(bits: &MachineTerm) -> MachineTerm {
    let Some(descriptor) = ScalarReadDescriptor::from_term(bits) else {
        return bits.clone();
    };
    if let Some((identity, typed)) =
        SCALAR_READ_IDENTITY_CACHE.with(|cache| cache.borrow().get(bits).cloned())
    {
        let MachineTerm::MemoryLoad(memory, pointer, kind) = identity.as_legacy_read() else {
            unreachable!("cached scalar read identity");
        };
        // A conservative, untyped selection is not an observed access width.
        // Once a producer supplies the width, select its version with that
        // width instead of treating the earlier guess as an eight-byte load.
        if typed
            || existing_read_access_width(memory, pointer, *kind).is_some()
            || recorded_load_access_width(descriptor.memory(), descriptor.pointer()).is_none()
        {
            read_observations::produced(identity.as_legacy_read(), bits);
            return identity.into_legacy_read();
        }
    }
    let (identity, observed_bytes) = scalar_reads::select_comparison_identity(descriptor);
    scalar_reads::record_comparison_observation(&identity, descriptor.memory(), observed_bytes);
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

pub(crate) fn latest_scalar_read_observation(read: &MachineTerm) -> Option<MachineTerm> {
    read_observations::latest(read)
}

/// Returns the load variable for a load term's provenance-stable form.
/// The term is first canonicalized without assumptions, resolving cached
/// cells and state representation differences. The same cell loaded at
/// different symbolic states therefore shares one load variable whenever
/// the difference is representational. The second return value is the form
/// retained in the producer binding, exactly as registered under the name.
pub(crate) fn load_variable_for_term(bits: &MachineTerm) -> Option<(Variable, MachineTerm)> {
    let MachineTerm::MemoryLoad(..) = bits else {
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

fn load_variable_for_term_uncached(bits: &MachineTerm) -> Option<(Variable, MachineTerm)> {
    let canonical = crate::kernel::memory_provenance::canonicalize_atomic_loads(bits);
    if let MachineTerm::MemoryLoad(memory, pointer, kind) = &canonical {
        let MachineTerm::MemoryLoad(origin, _, _) = bits else {
            unreachable!("the pattern above matched a memory load");
        };
        // A cell of the canonical state holding this cell's own read (a
        // materialization) names that read: the load is that read. The raw
        // state can lack the cell while its unchanged-bytes source, which
        // the canonical state is projected from, holds it, so the cell is
        // asked of the canonical state. Only a read of the same address
        // and kind qualifies, so no stored value replaces a read.
        if let Some(MachineTerm::Variable(held)) = memory
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
                memory,
                pointer,
                *kind,
                // Either state's recorded entry is this same load's own
                // width, so the first one found is the answer. Taking the
                // larger would let a miss on one side widen a width the
                // other side knows exactly.
                recorded_load_access_width(origin, pointer)
                    .or_else(|| recorded_load_access_width(memory, pointer))
                    .or_else(|| {
                        existing_read_access_width(origin, pointer, *kind)
                            .max(existing_read_access_width(memory, pointer, *kind))
                    })
                    .unwrap_or_else(|| kind.unrecorded_access_byte_width()),
                origin,
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
    if let MachineTerm::Variable(variable) = &canonical
        && let MachineTerm::MemoryLoad(_, _, kind) = bits
        && registered_load_kind_for_variable(variable) == Some(*kind)
    {
        return Some((*variable, bits.clone()));
    }
    let MachineTerm::MemoryLoad(memory, pointer, kind) = bits else {
        unreachable!("the pattern above matched a memory load");
    };
    Some((load_variable_for_cell(memory, pointer, *kind), bits.clone()))
}

/// Binds a load term to its load variable and records the defining
/// equation in the path's fact stream. The defining equation is
/// kernel-certified by construction: the load variable represents this
/// load. It must not demand a checkable assumption derivation
/// downstream.
#[cfg(test)]
fn mint_load_variable(
    bits: &MachineTerm,
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
pub(crate) fn record_load_variable_defining_fact(
    variable: Variable,
    load: MachineTerm,
    facts: &mut ExecutionFacts,
) {
    record_load_variable_defining_fact_with_source(variable, load, facts, None);
}

pub(crate) fn record_load_variable_defining_fact_with_source(
    variable: Variable,
    load: MachineTerm,
    facts: &mut ExecutionFacts,
    source: Option<&LoadSourceId>,
) {
    record_load_variable_defining_fact_with_source_and_pointer(variable, load, facts, source, None);
}

fn record_load_variable_defining_fact_with_source_and_pointer(
    variable: Variable,
    load: MachineTerm,
    facts: &mut ExecutionFacts,
    source: Option<&LoadSourceId>,
    typed_pointer_value: Option<&Pointer>,
) {
    let MachineTerm::MemoryLoad(memory, pointer, kind) = &load else {
        // `load_variable_for_term` currently returns a memory load's
        // canonical operand.  Keep this guard explicit so future changes
        // cannot attach producer metadata to an unrelated term.
        return;
    };
    let defining_load = load.clone();
    let defining_proposition = Proposition::ConditionIs(
        ConditionTerm::Compare {
            // The raw-load form historically used a 32-bit equality with
            // a width-check exception. Registered read terms use the actual
            // carrier width: a narrow read is a value of its own format.
            format: match kind {
                LoadKind::Int8 => MachineIntegerType::Int8,
                LoadKind::UInt8 => MachineIntegerType::UInt8,
                LoadKind::Int16 => MachineIntegerType::Int16,
                LoadKind::UInt16 => MachineIntegerType::UInt16,
                LoadKind::Bits64 | LoadKind::Float64 => MachineIntegerType::Int64,
                LoadKind::Int128 => MachineIntegerType::Int128,
                LoadKind::UInt128 => MachineIntegerType::UInt128,
                LoadKind::Int32 | LoadKind::UInt32 | LoadKind::Float32 => MachineIntegerType::Int32,
            },
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(variable)),
            // The registered variable is the structural read term used by
            // logical lowering. Keep the raw descriptor in the producer
            // binding below, not as a second term form in a citable fact.
            right: Box::new(canonical_form_of_load(
                memory.clone(),
                pointer.as_ref().clone(),
                *kind,
            )),
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
        .position(|fact| fact.proposition == defining_proposition);
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

pub(in crate::kernel) fn symbolic_load_value(
    memory: &Memory,
    pointer: &Pointer,
    value_type: ProgramType,
) -> Option<ProgramValue> {
    // Every C load reaches the kernel through here with its type. The
    // `MemoryLoad` term built below carries the read's kind; the address's
    // recorded width, which every read there shares, is kept beside it.
    // Recording it here is what lets an `int32` load keep being separated
    // from a store one element away.
    record_load_access_width(memory, pointer, value_type.byte_width());
    symbolic_load_value_unrecorded(memory, pointer, value_type)
}

/// [`symbolic_load_value`] without recording the access width, for a caller
/// that has already said how wide the access is.
pub(in crate::kernel) fn symbolic_load_value_unrecorded(
    memory: &Memory,
    pointer: &Pointer,
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
            pointer.clone(),
            parameter,
        )),
        ProgramType::Void | ProgramType::VoidPointer => None,
        ProgramType::Bool => {
            let load = MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(memory.clone()),
                Box::new(pointer.clone()),
                LoadKind::UInt8,
            );
            // The byte rule (Stage 5): the read of a `bool` cell whose byte
            // is `b` is the `Bool` `b != 0`. Every write of such a cell
            // stores `v as uint8`, 1 or 0 (rule C1), and no write of another
            // kind or byte view reaches it, so the byte is 0 or 1 and this is
            // the value the cell holds.
            Some(crate::kernel::bool_value(load))
        }
        ProgramType::Int8 => Some(memory.symbolic_int8_load(pointer)),
        ProgramType::Int16 => Some(memory.symbolic_int16_load(pointer)),
        ProgramType::Int32 => Some(memory.symbolic_int32_load(pointer)),
        ProgramType::UInt8 => Some(memory.symbolic_uint8_load(pointer)),
        ProgramType::UInt16 => Some(memory.symbolic_uint16_load(pointer)),
        ProgramType::UInt32 => Some(memory.symbolic_uint32_load(pointer)),
        ProgramType::Int64 => Some(memory.symbolic_int64_load(pointer)),
        ProgramType::UInt64 => Some(memory.symbolic_uint64_load(pointer)),
        ProgramType::Float32 => Some(memory.symbolic_float32_load(pointer)),
        ProgramType::Float64 => Some(memory.symbolic_float64_load(pointer)),
        ProgramType::Int8Pointer | ProgramType::Int8PointerPointer => {
            Some(memory.symbolic_pointer_load(pointer, value_type))
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
            Some(memory.symbolic_pointer_load(pointer, value_type))
        }
        ProgramType::Float32Pointer
        | ProgramType::Float64Pointer
        | ProgramType::Float32PointerPointer
        | ProgramType::Float64PointerPointer => {
            Some(memory.symbolic_pointer_load(pointer, value_type))
        }
        ProgramType::FunctionPointer(_) => Some(memory.symbolic_pointer_load(pointer, value_type)),
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
    memory: &Memory,
    pointer: &Pointer,
    program_type: ProgramType,
) -> Option<ProgramValue> {
    let (kind, wrap): (LoadKind, fn(MachineTerm) -> ProgramValue) = match program_type {
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
            let load = MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(memory.clone()),
                Box::new(pointer.clone()),
                LoadKind::Int32,
            );
            return SCALAR_READ_IDENTITY_CACHE.with(|cache| {
                let read = cache.borrow().get(&load)?.0.as_legacy_read().clone();
                Some(ProgramValue::Pointer(PointerValue::from_read(
                    Pointer::loaded(&read).expect("cached pointer read descriptor"),
                    program_type,
                    &crate::kernel::intern_memory_ref(memory),
                    pointer,
                )))
            });
        }
        _ => return None,
    };
    let load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(memory.clone()),
        Box::new(pointer.clone()),
        kind,
    );
    crate::instrumentation::record_deterministic_work(1);
    SCALAR_READ_IDENTITY_CACHE
        .with(|cache| cache.borrow().get(&load).cloned())
        .map(|(identity, _)| wrap(identity.into_legacy_read()))
}

pub(in crate::kernel) fn symbolic_storage_cell_value(
    memory: &Memory,
    pointer: &Pointer,
    program_type: ProgramType,
    record_width: bool,
) -> Option<ProgramValue> {
    if program_type.is_object_pointer() {
        if record_width && pointer.block.is_local_block() {
            record_load_access_width(memory, pointer, program_type.byte_width());
        }
        let load = MachineTerm::MemoryLoad(
            crate::kernel::intern_memory(memory.clone()),
            Box::new(pointer.clone()),
            LoadKind::Int32,
        );
        let value = Pointer::loaded(&load).expect("symbolic pointer cell read");
        return Some(ProgramValue::Pointer(PointerValue::from_read(
            value,
            program_type,
            &crate::kernel::intern_memory(memory.clone()),
            pointer,
        )));
    }
    // Entry cells and contract reads select the same structural descriptor.
    let value = if record_width {
        symbolic_load_value(memory, pointer, program_type)
    } else {
        symbolic_load_value_unrecorded(memory, pointer, program_type)
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

#[cfg(test)]
mod tests {
    #[test]
    fn exact_read_descriptors_and_comparison_identities_keep_distinct_roles() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer {
            block: "read-api-target".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let other = Pointer {
            block: "read-api-other".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = Memory::new()
            .with_block("read-api-target", 4)
            .with_block("read-api-other", 4)
            .store(pointer.clone(), int32(7));
        let before = intern_memory_ref(&memory);
        let after = crate::kernel::intern_memory(memory.store(other, int32(9)));
        record_load_access_width(before.memory(), &pointer, 4);
        record_load_access_width(after.memory(), &pointer, 4);
        let first = MachineTerm::memory_read(before.clone(), pointer.clone(), LoadKind::Int32);
        let second = MachineTerm::memory_read(after.clone(), pointer.clone(), LoadKind::Int32);
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
            scalar_read_observation(crate::kernel::MachineOperandView::Legacy(&legacy)).unwrap();
        assert_eq!(observation.origin, Some(after));
        assert_eq!(observation.bytes, 4);
        assert_eq!(
            canonical_scalar_read(&second),
            legacy,
            "warm compatibility path"
        );
    }

    #[test]
    fn scalar_read_comparison_identities_distinguish_writes_and_kinds() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer {
            block: "read-api-written".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = Memory::new()
            .with_block("read-api-written", 4)
            .store(pointer.clone(), int32(7));
        let before = intern_memory_ref(&memory);
        let after = crate::kernel::intern_memory(memory.store(pointer.clone(), int32(9)));
        let identity = |memory: SharedMemory, kind| {
            let read = MachineTerm::memory_read(memory, pointer.clone(), kind);
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
        let memory = Memory::new();
        let address = Pointer::symbolic(Variable(93_001));
        let before = load_variable_registry_len();
        for ty in [
            ProgramType::Int32Pointer,
            ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
        ] {
            let ordinary = symbolic_load_value(&memory, &address, ty).unwrap();
            let logical = memory.symbolic_pointer_version_load(&address, ty);
            let entry = symbolic_storage_cell_value(&memory, &address, ty, true)
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
                    .pointer()
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
    fn querying_a_registered_read_preserves_its_access_width() {
        for bytes in [4, 8] {
            let _session = crate::kernel::VerificationSession::enter();
            let memory = crate::kernel::intern_memory(Memory::new());
            let pointer = Pointer::symbolic(Variable(993149));
            let name = load_variable_for_exact_cell(&memory, &pointer, LoadKind::Int32, bytes);
            let raw =
                MachineTerm::MemoryLoad(memory.clone(), Box::new(pointer.clone()), LoadKind::Int32);
            assert_eq!(
                load_term_access_width(&memory, &pointer, LoadKind::Int32),
                bytes
            );
            let canonical = canonical_term(&raw);
            assert!(matches!(canonical, MachineTerm::MemoryLoad(..)));
            assert_eq!(registered_load_bytes_for_variable(&name), Some(bytes));
            assert_eq!(
                scalar_read_observation(crate::kernel::MachineOperandView::Legacy(&canonical))
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
        let memory = crate::kernel::intern_memory(Memory::new());
        let pointer = Pointer::symbolic(Variable(993150));
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
        assert_eq!(observe(&other).origin, Some(memory.clone()));
        begin_load_origin_epoch();
        assert!(
            observe(&term).origin.is_none(),
            "a query must not renew an origin"
        );
        assert!(observe(&other).origin.is_none());
        load_variable_for_exact_cell(&memory, &pointer, LoadKind::Int32, 8);
        assert_eq!(observe(&term).bytes, 8, "width updates are live");
        assert_eq!(observe(&other).origin, Some(memory));
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
            (ProgramType::Int32Pointer, Pointer::null()),
            (
                ProgramType::Int32Pointer,
                Pointer::symbolic(Variable(989_850)),
            ),
            (
                ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
                Pointer::null(),
            ),
            (
                ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
                Pointer::function("callback"),
            ),
        ] {
            let _session = crate::kernel::VerificationSession::enter();
            let address = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            };
            let value = ProgramValue::typed_pointer(stored.clone(), ty);
            let memory = Memory::new().store(address.clone(), value.clone());
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
            // The structural read keeps its own designation. The complete
            // stored value is related through the graph, not folded into it.
            let ProgramValue::Pointer(stored_value) = &value else {
                unreachable!()
            };
            assert!(
                matches!(&ordinary[0].outcome, ExpressionOutcome::Value(ProgramValue::Pointer(actual))
                if actual.pointer() != &stored
                    && context.equality_graph.knows_condition(
                        &ConditionTerm::PointerValueEqual(
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
                read.pointer(),
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
            assert!(known.pointers_known_equal(read.pointer(), &stored));
        }
    }

    #[test]
    fn logical_read_of_copied_pointer_retains_its_complete_value() {
        let complete_equalities = [false, true].map(|declare_after_store| {
            let _session = crate::kernel::VerificationSession::enter();
            let field = Memory::frame_local_pointer(0, "copied_pointer");
            let stored = PointerValue::new(
                Pointer::symbolic(Variable(210_399)),
                ProgramType::Int32Pointer,
            );
            let mut memory =
                Memory::new().store(field.clone(), ProgramValue::Pointer(stored.clone()));
            // Aggregate parameter binding writes its fields, then declares
            // the private destination block. Compare the immediate store.
            if declare_after_store {
                memory = memory.with_block(field.block.clone(), 8);
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
            assert!(known.pointers_known_equal(read.pointer(), stored.pointer()));
            // Check entailment, not exact premise spelling: the producer's
            // equation may name the endpoints in the opposite order.
            known.contains_known(&Proposition::ConditionIs(
                ConditionTerm::pointer_value_equal(read.clone(), stored),
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
        let address = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let context = PureFactContext::new()
            .allow_symbolic_contract_loads()
            .force_symbolic_external_loads();
        let memory = Memory::new();
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
        assert_eq!(actual.pointer(), expected.pointer());
    }

    #[test]
    fn program_pointer_facts_retain_their_scoped_read_producer() {
        let _session = crate::kernel::VerificationSession::enter();
        let empty = PureFactContext::new();
        let registry_before = capture_load_variable_registry();
        let memory = Memory::new();
        let address = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(8),
        };
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
        let defining_address = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(8),
        };
        let definition = pointer
            .pointer()
            .as_loaded_value()
            .expect("a program pointer read names its read");
        assert_eq!(definition.defining_address, defining_address);
        assert_eq!(definition.displacement, PointerOffsetTerm::Constant(0));
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_term(pointer.pointer()).is_some()
        );
        assert!(
            crate::kernel::memory_provenance::checked_pointer_read_endpoint(
                pointer.pointer(),
                &context
            )
            .is_some()
        );
        assert!(
            ResourceContext::new()
                .memory_write_range(pointer.pointer(), 4, &context)
                .is_none()
        );
        restore_load_variable_registry(&registry_before);
        // A restore returns the registry to its capture, as it does the
        // memory arena whose ids name the read's state: a name minted
        // after the capture names nothing afterwards, exactly as a load
        // variable minted then does.
        assert!(pointer.pointer().as_loaded_value().is_none());
        assert!(
            crate::kernel::memory_provenance::checked_pointer_read_endpoint(
                pointer.pointer(),
                &context
            )
            .is_none()
        );
    }

    #[test]
    fn logical_read_equations_are_not_conditions_or_quantifier_guards() {
        let value = Pointer::symbolic(Variable(959_001));
        let read = Pointer::loaded_value(&intern_memory(Memory::new()), &value);
        let fact = ExecutionPureFact::logical_read_equation(
            PointerValue::new(value, ProgramType::Int32Pointer),
            read,
        );
        let facts: ExecutionFacts = vec![fact.clone()].into();
        assert!(!facts.has_path_conditions());
        let goal = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
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
        let address = Pointer::symbolic(Variable(959_101));
        let base = Memory::new();
        let mut facts = ExecutionFacts::new();
        let value = canonicalized_symbolic_load_value_with_identity(
            &base,
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
        let base = Memory::new();
        let source = Pointer::symbolic(Variable(955_001));
        let cached = logical_pointer_read(&base, &source, &empty);
        assert_eq!(
            cached
                .as_loaded_value()
                .expect("typed cached load")
                .defining_address,
            source
        );
        let address = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(955_002)), 4),
        };
        let alias = Pointer::symbolic(Variable(955_003));
        let current = base.clone().materialize_named_cell(
            address.clone(),
            ProgramValue::Pointer(PointerValue::from_read(
                cached.clone(),
                ProgramType::Int64Pointer,
                &intern_memory_ref(&base),
                &source,
            )),
        );
        let logical = logical_pointer_read(&current, &alias, &empty);
        let model = Pointer::symbolic(Variable(955_004));
        let base_context = empty
            .clone()
            .assume_condition(
                ConditionTerm::pointer_equal(alias.clone(), address.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::PointerValueEqual(
                    Box::new(PointerValue::new(model.clone(), ProgramType::Int64Pointer)),
                    Box::new(PointerValue::from_read(
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
        assert!(context.pointers_known_equal(&model, value.pointer()));
        let mut checkpoint = context.equality_graph.input_root();
        assert!(checkpoint.append_inputs_from(&context.equality_graph));
        assert!(checkpoint.are_equal(&model, value.pointer()));
        let restricted = context.restricted_to_facts(&[], &[]);
        assert!(!restricted.pointers_known_equal(&model, value.pointer()));
        let missing_alias = empty.clone().assume_condition(
            ConditionTerm::PointerValueEqual(
                Box::new(PointerValue::new(model.clone(), ProgramType::Int64Pointer)),
                Box::new(PointerValue::from_read(
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
    fn a_loaded_pointer_cannot_reach_storage_created_after_the_read() {
        let storage = PointerBlock::Heap(8710);
        let early: PointerBlock = "local:early_object".into();
        let later: PointerBlock = "local:later_object".into();
        let cell = Pointer {
            block: storage.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = Memory::new()
            .with_block(storage.clone(), 16)
            .with_block(early.clone(), 4);
        let value_type = ProgramType::Int32Pointer;
        let assumptions = PureFactContext::new()
            .assume_proposition(Proposition::MemoryReadDefined {
                memory: memory.clone(),
                pointer: cell.clone(),
                value_type,
            })
            .assume_proposition(Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: cell.clone(),
                bytes: MachineTerm::constant(8),
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
        let loaded = &value.pointer().block;
        assert!(loaded.proven_distinct(&later));
        assert!(later.proven_distinct(loaded));
        assert!(!loaded.proven_distinct(&early));
        // The same holds for a heap identity the read's state never
        // handed out, and not for one it already holds.
        assert!(loaded.proven_distinct(&PointerBlock::Heap(8711)));
        assert!(PointerBlock::Heap(8711).proven_distinct(loaded));
        assert!(!loaded.proven_distinct(&storage));
    }

    #[test]
    fn unknown_pointer_in_fresh_storage_does_not_inherit_storage_provenance() {
        for block in [PointerBlock::Heap(8700), PointerBlock::Temporary(8701)] {
            for offset in [0, 8] {
                let cell = Pointer {
                    block: block.clone(),
                    offset: PointerOffsetTerm::Constant(offset),
                };
                // Another allocation live at the read, which the value may
                // point into as well as anything else that existed then.
                let memory = Memory::new()
                    .with_block(block.clone(), 16)
                    .with_block(PointerBlock::Heap(8702), 16);
                let value_type = ProgramType::Int32Pointer;
                let assumptions = PureFactContext::new()
                    .assume_proposition(Proposition::MemoryReadDefined {
                        memory: memory.clone(),
                        pointer: cell.clone(),
                        value_type,
                    })
                    .assume_proposition(Proposition::MemoryLoadable {
                        memory: memory.clone(),
                        base: cell.clone(),
                        bytes: MachineTerm::constant(8),
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
                    assert!(matches!(
                        value.pointer().block,
                        PointerBlock::LoadedPointer(_)
                    ));
                    assert_eq!(
                        value.pointer().as_loaded_value().unwrap().defining_address,
                        cell
                    );
                    assert!(
                        !value
                            .pointer()
                            .block
                            .proven_distinct(&PointerBlock::Heap(8702))
                    );
                    assert_eq!(value.program_type(), value_type);
                }
                let bits = MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory_ref(&memory),
                    Box::new(cell.clone()),
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
                )
                .unwrap();
                let ProgramValue::Pointer(cached) = cached else {
                    panic!("cached pointer expected");
                };
                assert!(matches!(
                    cached.pointer().block,
                    PointerBlock::LoadedPointer(_)
                ));
                let target = Pointer {
                    block: PointerBlock::Heap(8702),
                    offset: PointerOffsetTerm::Constant(0),
                };
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
                    if pointer_read_over_write_value(value.pointer()).as_ref() == Some(&target)
                        && assumptions.equality_graph.knows_condition(
                            &ConditionTerm::PointerValueEqual(
                                Box::new(value.clone()),
                                Box::new(PointerValue::new(target.clone(), value_type)),
                            ), true,
                        ))
                );
            }
        }
    }

    #[test]
    fn logical_scalar_read_preserves_cached_offset_spelling() {
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::scaled_int32_node(
                    MachineTerm::Variable(Variable(944_021)),
                    4,
                )),
                Box::new(PointerOffsetTerm::Constant(16)),
            ),
        };
        let expected = ProgramValue::Int32(MachineTerm::constant(7));
        let memory = Memory::new().store(pointer.clone(), expected.clone());
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
            let cell = Pointer {
                block: "local:pointer-holder".into(),
                offset: PointerOffsetTerm::Constant(offset),
            };
            let target = Pointer {
                block: "local:other-object".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let value_type = ProgramType::Int32Pointer;
            let before = Memory::new()
                .with_block(target.block.clone(), 4)
                .with_block(cell.block.clone(), 16)
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
                before.with_loop_memory_havoc_preserving_loans(
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
                assert!(matches!(
                    value.pointer().block,
                    PointerBlock::LoadedPointer(_)
                ));
                assert_eq!(
                    value.pointer().as_loaded_value().unwrap().defining_address,
                    cell
                );
                assert!(!value.pointer().block.proven_distinct(&target.block));
            }
            let bits = MachineTerm::MemoryLoad(
                crate::kernel::intern_memory_ref(&memory),
                Box::new(cell.clone()),
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
            )
            .unwrap();
            let ProgramValue::Pointer(cached) = cached else {
                panic!("cached pointer expected");
            };
            assert!(matches!(
                cached.pointer().block,
                PointerBlock::LoadedPointer(_)
            ));
            assert!(!cached.pointer().block.proven_distinct(&target.block));
        }
    }

    #[test]
    fn indexed_local_load_uses_proven_alias_without_inventing_initialization() {
        let index = MachineTerm::Variable(Variable(839));
        let base = Pointer {
            block: "local:indexed".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let pointer = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::add(
                PointerOffsetTerm::Constant(4),
                PointerOffsetTerm::scale_int32(index.clone(), 4),
            ),
        };
        let assumptions = PureFactContext::new()
            .assume_condition(ConditionTerm::equal(index, MachineTerm::constant(1)), true);
        let memory = Memory::new()
            .with_block(base.block.clone(), 12)
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
        let left = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(810)),
        };
        let right = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(811)),
        };
        let mut cache = MemoryLoadAliasCache::default();
        let empty = PureFactContext::new();
        assert!(!cache.resolution_equal(&left, &right, &empty));

        let equal = empty.assume_condition(
            ConditionTerm::pointer_offset_equal(left.offset.clone(), right.offset.clone()),
            true,
        );
        assert!(cache.resolution_equal(&left, &right, &equal));
    }

    #[test]
    fn ancestor_named_load_does_not_cross_into_an_aliasing_fact_context() {
        let retained_index = MachineTerm::Variable(Variable(812));
        let written_index = MachineTerm::Variable(Variable(813));
        let read_index = MachineTerm::Variable(Variable(814));
        let at = |index| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(index, 4),
        };
        let retained = at(retained_index);
        let written = at(written_index.clone());
        let read = at(read_index.clone());

        // Keep one unresolved cell so the reduced load is still symbolic.
        // Dropping only the later, proven-distinct write then makes the
        // reduced memory structurally equal to this already-interned ancestor.
        let ancestor_memory = Memory::new().store(retained, int32(1));
        let ancestor = intern_memory_ref(&ancestor_memory);
        let current = ancestor_memory.store(written.clone(), int32(2));
        let distinct = PureFactContext::new().assume_condition(
            ConditionTerm::equal(read_index.clone(), written_index.clone()),
            false,
        );
        let aliasing = PureFactContext::new()
            .assume_condition(ConditionTerm::equal(read_index, written_index), true);
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
        let ExpressionOutcome::Value(ProgramValue::Int32(MachineTerm::MemoryLoad(
            named_memory,
            named_pointer,
            LoadKind::Int32,
        ))) = &distinct_path.outcome
        else {
            panic!("the unresolved distinct load should have a symbolic identity");
        };
        assert_eq!(*named_memory, ancestor);
        assert_eq!(**named_pointer, read);

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
    fn minted_load_fact_carries_exact_producer_binding() {
        let memory = crate::kernel::intern_memory(Memory::new());
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(12),
        };
        let load = MachineTerm::MemoryLoad(
            memory.clone(),
            Box::new(pointer.clone()),
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
        let memory = intern_memory(Memory::new());
        let pointer = Pointer::symbolic(Variable(299_301));
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
            let raw = MachineTerm::MemoryLoad(memory.clone(), Box::new(pointer.clone()), kind);
            let (variable, descriptor) = load_variable_for_term(&raw).unwrap();
            let mut facts = ExecutionFacts::new();
            record_load_variable_defining_fact(variable, descriptor.clone(), &mut facts);
            let expected = Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format,
                    relation: CompareRelation::Equal,
                    left: Box::new(MachineTerm::Variable(variable)),
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
        let memory = intern_memory(Memory::new());
        let address = Pointer::symbolic(Variable(299_201));
        let raw = |pointer, kind| MachineTerm::MemoryLoad(memory.clone(), Box::new(pointer), kind);
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
            let changed = Proposition::ConditionIs(
                ConditionTerm::equal(
                    MachineTerm::Variable(variable),
                    MachineTerm::Variable(other),
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
        let replacement = Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::Variable(variable),
                MachineTerm::MemoryLoad(
                    intern_memory(Memory::new()),
                    Box::new(Pointer::symbolic(Variable(299_201))),
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
        let memory = crate::kernel::intern_memory(Memory::new());
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(12),
        };
        let load =
            MachineTerm::MemoryLoad(memory, Box::new(pointer), crate::kernel::LoadKind::Int32);
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
    fn transported_equal_equation_from_a_new_epoch_drops_producer_provenance() {
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(20),
        };
        let first_memory = crate::kernel::intern_memory(Memory::new());
        let first_load = MachineTerm::MemoryLoad(
            first_memory.clone(),
            Box::new(pointer.clone()),
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
        // Exercise the raw descriptor form too: structural state equality
        // can hold across epochs, but it must not carry producer authority.
        let fact = ExecutionPureFact::certified(Proposition::ConditionIs(
            ConditionTerm::equal(MachineTerm::Variable(variable), first_load),
            true,
        ))
        .with_generated_load_binding(produced.generated_load_binding().unwrap().clone())
        .with_generated_load_source_event(produced.generated_load_source_events()[0].clone());

        // A fresh arena represents a new epoch. Its empty Memory is
        // structurally equal to the first one, but its embedded state
        // identity is intentionally different.
        crate::kernel::primitives::start_fresh_memory_arena();
        let second_memory = crate::kernel::intern_memory(Memory::new());
        let second_load = MachineTerm::MemoryLoad(
            second_memory.clone(),
            Box::new(pointer),
            crate::kernel::LoadKind::Int32,
        );
        let replacement = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(variable)),
                right: Box::new(second_load),
            },
            true,
        );
        assert_eq!(fact.proposition(), &replacement);
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
    #[ignore = "nightly: 0.6s in the parallel gate"]
    fn a_symbolic_load_over_many_undecided_cells_splits_without_recursing() {
        const CELLS: u32 = 400;
        let paths = std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(|| {
                let block = PointerBlock::from("global:split_table");
                let mut memory = Memory::new().with_block(block.clone(), CELLS * 4);
                for index in 0..CELLS {
                    memory = memory.store(
                        Pointer {
                            block: block.clone(),
                            offset: PointerOffsetTerm::Constant(i64::from(index) * 4),
                        },
                        int32(index),
                    );
                }
                let pointer = Pointer {
                    block,
                    offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(841)), 4),
                };
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
        memory: &Memory,
        address: &Pointer,
        context: &PureFactContext,
    ) -> Pointer {
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
        value.pointer().clone()
    }

    #[test]
    fn logical_pointer_field_alias_keeps_loaded_supplier_base_after_call() {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = Pointer::symbolic(Variable(955_920))
            .offset_by_elements(MachineTerm::Variable(Variable(955_921)), 4);
        let alias = Pointer::symbolic(Variable(955_922));
        let target = Pointer::symbolic(Variable(955_923));
        let right = owner.offset_by_bytes(8);
        let before = Memory::new().store(
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
            ConditionTerm::pointer_equal(owner.clone(), alias.clone()),
            true,
        );
        let read = |memory: &Memory, address: Pointer, context: &PureFactContext| {
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
            ExpressionOutcome::Value(ProgramValue::Pointer(value)) => value.pointer().clone(),
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
                Pointer::symbolic(Variable(955_925)),
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
        let slot = Pointer::symbolic(Variable(989_960));
        let alias = Pointer::symbolic(Variable(989_961));
        let memory = Memory::new().store(
            slot.clone(),
            ProgramValue::UInt64(MachineTerm::uint64_constant(7)),
        );
        let empty = PureFactContext::new()
            .allow_symbolic_contract_loads()
            .prefer_symbolic_external_loads()
            .keep_spec_loads_symbolic();
        let facts = empty
            .clone()
            .assume_condition(ConditionTerm::pointer_equal(slot, alias.clone()), true);
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
    fn program_and_logical_reads_through_an_opaque_alias_are_equal_in_the_graph() {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(95_000)), 4),
        };
        let alias = Pointer::symbolic(Variable(95_001));
        let memory = Memory::new();
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
                memory: memory.clone(),
                pointer: alias.clone(),
                value_type: ProgramType::UInt64,
            })
            .assume_proposition(Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: alias.clone(),
                bytes: 8u32.into(),
                wide: false,
            });
        let context = without_alias.clone().assume_condition(
            ConditionTerm::pointer_equal(owner.clone(), alias.clone()),
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
        let memory = Memory::new();
        let a = Pointer::symbolic(Variable(92_200));
        let b = Pointer::symbolic(Variable(92_201));
        let before = PureFactContext::new();
        let sibling = before.clone();
        let x = logical_pointer_read(&memory, &a, &before);
        let y = logical_pointer_read(&memory, &b, &before);
        assert!(before.pure_facts().is_empty());
        assert!(!before.pointers_known_equal(&x, &y));
        let branch = before
            .clone()
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
        assert!(branch.pointers_known_equal(&x, &y));
        assert!(!sibling.pointers_known_equal(&x, &y));
        assert!(!before.pointers_known_equal(&x, &y));
        assert!(!ResourceContext::new().permits_memory_read(&b, 8, &branch));
        let changed = memory.store(
            a.clone(),
            ProgramValue::typed_pointer(
                Pointer::symbolic(Variable(92_202)),
                ProgramType::Int64Pointer,
            ),
        );
        let z = logical_pointer_read(&changed, &a, &branch);
        assert!(!branch.pointers_known_equal(&x, &z));
        assert!(!branch.pointers_known_equal(&x, &x.offset_by_bytes(8)));
        // Definitions survive reconstruction, but the required address fact
        // must still be supplied by the new context itself.
        let reconstructed = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
        assert!(reconstructed.pointers_known_equal(&x, &y));
        assert_eq!(reconstructed.pure_facts().len(), 1);
    }

    #[test]
    fn typed_read_validity_accepts_its_certified_pointer_equation() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: "global:defined-complete-pointer".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let stored = ProgramValue::typed_pointer(
            Pointer::symbolic(Variable(210_290)),
            ProgramType::Int32Pointer,
        );
        // Forget the materialized cell without changing its stored value.
        // The typed read recovers the complete pointer, while the separately
        // recorded initialized bytes supply authority to read it.
        let memory = Memory::new()
            .with_initialized_object(&field, 8)
            .store(field.clone(), stored.clone())
            .without_possible_aliasing_cells(
                &Pointer::symbolic(Variable(210_291)),
                8,
                &PureFactContext::new(),
            );
        assert!(memory.known_value(&field).is_none());
        let view = |bytes| {
            PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: field.clone(),
                bytes: MachineTerm::constant(bytes),
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
        assert!(context.proves_memory_read_defined(&memory, &field, ProgramType::Int32Pointer));
        assert_eq!(context.fact_counts(), before);
        // Recovering a value and its equation grants no missing read extent.
        assert!(!PureFactContext::new().proves_memory_read_defined(
            &memory,
            &field,
            ProgramType::Int32Pointer,
        ));
        assert!(!view(4).proves_memory_read_defined(&memory, &field, ProgramType::Int32Pointer));
    }

    #[test]
    fn a_symbolic_pointer_read_recovers_the_complete_stored_value() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: "global:symbolic-complete-pointer".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let target = Pointer::symbolic(Variable(210_190));
        let class = crate::kernel::effective_type::CAccessClass::Scalar(
            crate::kernel::effective_type::CScalarClass::Int,
        );
        let stored = PointerValue::new(target.clone(), ProgramType::Int32Pointer)
            .with_extent(Some(SubobjectExtent {
                start: target,
                width: 4u32.into(),
            }))
            .with_object_class(Some(class.clone()));
        let context = PureFactContext::new();
        let memory = Memory::new()
            .store(field.clone(), ProgramValue::Pointer(stored.clone()))
            .without_possible_aliasing_cells(&Pointer::symbolic(Variable(210_191)), 8, &context);
        assert!(memory.known_value(&field).is_none());
        let read = |memory: &Memory| {
            let mut facts = ExecutionFacts::new();
            let ProgramValue::Pointer(value) = canonicalized_symbolic_load_value_with_identity(
                memory,
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
        // pointer, including the designation, bounds, and access class.
        assert_ne!(value.pointer(), stored.pointer());
        assert_eq!(value.designation(), value.pointer());
        assert!(context.equality_graph.knows_condition(
            &ConditionTerm::PointerValueEqual(Box::new(value.clone()), Box::new(stored.clone())),
            true,
        ));
        assert_eq!(
            pointer_read_over_write_value(value.pointer()),
            Some(stored.pointer().clone())
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
        let current = PointerValue::new(
            Pointer::loaded_value(&crate::kernel::intern_memory_ref(&memory), &field),
            ProgramType::Int32Pointer,
        );
        assert!(context.pointer_designations_match(&current, &stored));
        assert!(context.pointers_known_equal(current.pointer(), stored.pointer()));
        assert!(context.pure_facts().is_empty());
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_term(stored.pointer()).is_none()
        );
        let partial = memory.store(field.offset_by_bytes(4), ProgramValue::UInt32(0u32.into()));
        assert!(!context.pointer_designations_match(&read(&partial).0, &stored));
    }

    #[test]
    fn a_pointer_cast_restores_complete_word_reads_inside_a_numeric_observation() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: "global:scoped-word".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let target = Pointer::symbolic(Variable(210_199));
        let pointer = PointerValue::new(target.clone(), ProgramType::Int32Pointer)
            .with_extent(Some(SubobjectExtent::constant(target.clone(), 4)));
        let stored = ProgramValue::PointerInteger(PointerIntegerValue {
            numeric: Box::new(ProgramValue::UInt64(MachineTerm::pointer_address(target))),
            pointer: Box::new(pointer.clone()),
            kind: PointerIntegerKind::Exact,
        });
        let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new_with_element_width(field.clone(), 0u32.into(), 1u32.into(), 8),
        ));
        let state = ExecutionState::new()
            .with_memory(Memory::new().store(field.clone(), stored))
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
        let field = Pointer {
            block: "global:symbolic-word".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let target = Pointer::symbolic(Variable(210_192));
        let pointer = PointerValue::new(target.clone(), ProgramType::Int32Pointer).with_extent(
            Some(SubobjectExtent {
                start: target.clone(),
                width: 4u32.into(),
            }),
        );
        let context = PureFactContext::new();
        let read = |memory: &Memory| {
            canonicalized_symbolic_load_value_with_identity(
                memory,
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
            let bits = MachineTerm::pointer_address(target.clone());
            let bits = if kind == PointerIntegerKind::Tagged {
                MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::BitwiseOr,
                    left: Box::new(bits),
                    right: Box::new(MachineTerm::uint64_constant(1)),
                }
            } else {
                bits
            };
            let stored = ProgramValue::PointerInteger(PointerIntegerValue {
                numeric: Box::new(ProgramValue::UInt64(bits)),
                pointer: Box::new(pointer.clone()),
                kind,
            });
            let memory = Memory::new()
                .store(field.clone(), stored.clone())
                .without_possible_aliasing_cells(
                    &Pointer::symbolic(Variable(210_193)),
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
            let numeric = Memory::new().store(field.clone(), stored.numeric_value().clone());
            let ProgramValue::PointerInteger(fresh) = read(&numeric) else {
                panic!("word read")
            };
            assert!(matches!(
                fresh.kind,
                PointerIntegerKind::Word { changed_bits: 0 }
            ));
            assert!(fresh.pointer.extent().is_none());
        }
        assert!(context.pure_facts().is_empty());
    }

    #[test]
    fn explicit_numeric_word_frame_does_not_supply_pointer_origin() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer::symbolic(Variable(210_194));
        let target = Pointer::symbolic(Variable(210_195));
        let pointer = PointerValue::new(target.clone(), ProgramType::Int32Pointer).with_extent(
            Some(SubobjectExtent {
                start: target.clone(),
                width: 4u32.into(),
            }),
        );
        let stored = ProgramValue::PointerInteger(PointerIntegerValue {
            numeric: Box::new(ProgramValue::UInt64(MachineTerm::pointer_address(target))),
            pointer: Box::new(pointer.clone()),
            kind: PointerIntegerKind::Exact,
        });
        let before = Memory::new().store(field.clone(), stored);
        // Forgetting a cache is not a write to the program's memory.
        let after = before.clone().without_possible_aliasing_cells(
            &Pointer::symbolic(Variable(210_196)),
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
                after: after.clone(),
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
                !facts.pointer_designations_match(&recovered, &pointer),
                "numeric equality alone cannot supply the original pointer bounds"
            ),
            other => panic!("unexpected numeric cast result: {other:?}"),
        }
    }

    #[test]
    fn a_cached_scalar_prefix_recovers_only_the_complete_stored_pointer() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: "global:cached-pointer-a".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let other = Pointer {
            block: "global:cached-pointer-b".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let address = Pointer::symbolic(Variable(210_172));
        let stored = PointerValue::new(address.clone(), ProgramType::Int32Pointer).with_extent(
            Some(SubobjectExtent {
                start: address,
                width: 4u32.into(),
            }),
        );
        let memory = Memory::new()
            .store(field.clone(), ProgramValue::Pointer(stored.clone()))
            .store(other.clone(), ProgramValue::Pointer(stored.clone()));
        let memory = memory
            .without_possible_aliasing_cells(
                &Pointer::symbolic(Variable(210_173)),
                8,
                &PureFactContext::new(),
            )
            .materialize_symbolic_cell(field.clone(), ProgramType::Int32)
            .materialize_symbolic_cell(other.clone(), ProgramType::Int32);
        let context = PureFactContext::new();
        let read = |memory: &Memory, field: &Pointer| {
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
            )
            .unwrap() else {
                panic!("pointer read")
            };
            value
        };
        assert_eq!(read(&memory, &field), stored);
        assert_eq!(read(&memory, &other), stored);
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_term(stored.pointer()).is_none()
        );
        let overwritten = memory.store(
            field.clone().offset_by_bytes(4),
            ProgramValue::UInt32(0u32.into()),
        );
        let changed = read(&overwritten, &field);
        assert!(changed.extent().is_none());
        assert!(!context.pointer_designations_match(&changed, &stored));
    }

    #[test]
    fn checked_function_pointer_reads_reconcile_cached_aliases_without_leaking_evidence() {
        let _session = crate::kernel::VerificationSession::enter();
        let table = Pointer {
            block: "global:callback-table".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let argument = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scaled_int32_node(
                MachineTerm::Variable(Variable(210_510)),
                4,
            ),
        };
        let target = Pointer::function("callback");
        let replacement = Pointer::function("replacement");
        let program_type = ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED);
        let memory = Memory::new().store(
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
        let alias = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(argument.clone(), table.clone()),
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
            crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&alias));
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
                .pointers_known_equal(read.pointer(), &target)
        );
        assert!(
            !undecorated
                .assumptions()
                .pointers_known_equal(read.pointer(), &target)
        );
        assert!(!context.pointers_known_equal(read.pointer(), &target));
        for fact in &path.facts {
            fact.retain_pointer_read_definition(&context);
        }
        assert!(context.pointers_known_equal(read.pointer(), &target));
        assert!(!bare.pointers_known_equal(read.pointer(), &target));
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
        assert!(context.pointers_known_equal(changed_read.pointer(), &replacement));
        assert!(!context.pointers_known_equal(read.pointer(), changed_read.pointer()));
    }

    #[test]
    fn canonical_pointer_names_do_not_redefine_a_scalar_prefix_source() {
        // A cell caching a 4-byte scalar copied from `source` holds only a
        // prefix of a pointer: an 8-byte pointer read through it is not the
        // pointer read at `source`, whose name it must not take.
        let _session = crate::kernel::VerificationSession::enter();
        let base = Memory::new();
        let source = Pointer::symbolic(Variable(940_095));
        let destination = Pointer::symbolic(Variable(940_096));
        let ProgramValue::Pointer(original) =
            base.symbolic_pointer_load(&source, ProgramType::Int32Pointer)
        else {
            unreachable!()
        };
        let source_word = MachineTerm::MemoryLoad(
            crate::kernel::intern_memory(base.clone()),
            Box::new(source.clone()),
            crate::kernel::LoadKind::Int32,
        );
        let (variable, _) = load_variable_for_term(&source_word).unwrap();
        let cached = base.store(
            destination.clone(),
            ProgramValue::Int32(MachineTerm::Variable(variable)),
        );
        let ProgramValue::Pointer(prefix) =
            cached.symbolic_pointer_load(&destination, ProgramType::Int32Pointer)
        else {
            unreachable!()
        };
        assert_ne!(prefix.pointer(), original.pointer());
        assert!(
            prefix
                .pointer()
                .as_loaded_value()
                .is_none_or(|read| read.defining_address != source),
            "{:?}",
            prefix.pointer()
        );
    }

    #[test]
    fn specification_pointer_reads_do_not_adopt_fact_supplied_bounds() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = Memory::new();
        let address = Pointer::symbolic(Variable(989_920));
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
        let bounded = value.clone().with_extent(Some(SubobjectExtent {
            start: value.pointer().clone(),
            width: 4u32.into(),
        }));
        let facts = empty.clone().assume_condition(
            ConditionTerm::PointerValueEqual(Box::new(value.clone()), Box::new(bounded)),
            true,
        );
        let _scope = SpecificationReadScope::enter();
        assert_eq!(evaluate(&facts), evaluate(&empty));
    }

    #[test]
    fn specification_cached_pointer_value_does_not_follow_fact_supported_frames() {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = Pointer::symbolic(Variable(989_930));
        let write = Pointer::symbolic(Variable(989_931));
        let target = Pointer::symbolic(Variable(989_932));
        let stored = PointerValue::new(target.clone(), ProgramType::Int32Pointer)
            .with_extent(Some(SubobjectExtent::constant(target, 4)));
        let memory = Memory::new()
            .store(slot.clone(), ProgramValue::Pointer(stored.clone()))
            .without_possible_aliasing_cells(&write, 4, &PureFactContext::new())
            .store(write.clone(), ProgramValue::Int32(7u32.into()));
        assert!(memory.known_value(&slot).is_none());
        let variable =
            load_variable_for_exact_cell(&intern_memory_ref(&memory), &slot, LoadKind::Int32, 8);
        let cached = ProgramValue::Int32(MachineTerm::Variable(variable));
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
        let memory = Memory::new();
        let source = Pointer::symbolic(Variable(989_910));
        let destination = Pointer::symbolic(Variable(989_911));
        let read = MachineTerm::MemoryLoad(
            intern_memory_ref(&memory),
            Box::new(source.clone()),
            LoadKind::Int32,
        );
        let variable = load_variable_for_term(&read).unwrap().0;
        let value = ProgramValue::Int32(MachineTerm::Variable(variable));
        let empty = PureFactContext::new();
        let facts = empty.clone().assume_condition(
            ConditionTerm::pointer_equal(source, destination.clone()),
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
                )
                .unwrap()
            };
            assert_eq!(evaluate(&facts), evaluate(&empty), "{label}");
        }
    }

    #[test]
    fn specification_program_pointer_reads_retain_their_logical_names() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = Memory::new();
        let a = Pointer::symbolic(Variable(940_097));
        let b = Pointer::symbolic(Variable(940_098));
        let context = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
        let read = |address: &Pointer| {
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
            pointer.pointer().clone()
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
        let base = Memory::new();
        let origin = intern_memory_ref(&base);
        let a = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(940_091)), 4),
        };
        let b = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(940_092)), 4),
        };
        let field_a = a.clone().offset_by_bytes(8);
        let field_b = b.clone().offset_by_bytes(8);
        let first = base.symbolic_pointer_load(&field_a, ProgramType::Int32Pointer);
        let second = base.symbolic_pointer_load(&field_b, ProgramType::Int32Pointer);
        let slot_a = Pointer {
            block: "local:raw-a".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let slot_b = Pointer {
            block: "local:raw-b".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = base
            .store(slot_a.clone(), first)
            .store(slot_b.clone(), second);
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_value_equal(
                PointerValue::new(a, ProgramType::Int32Pointer),
                PointerValue::new(b, ProgramType::Int32Pointer),
            ),
            true,
        );
        let canonical = |field: &Pointer| {
            Pointer::loaded(&canonical_term(&MachineTerm::MemoryLoad(
                origin.clone(),
                Box::new(field.clone()),
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
                pointer_read_over_write_value(value.pointer()).as_ref(),
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
        let memory = Memory::new();
        let a = Pointer::symbolic(Variable(92_210));
        let b = Pointer::symbolic(Variable(92_211));
        let before = PureFactContext::new();
        let program_read = |address: &Pointer| {
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
            value.pointer().clone()
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
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
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
        let slot = Pointer::symbolic(Variable(92_330));
        let write = Pointer::symbolic(Variable(92_331));
        let before = intern_memory(Memory::new());
        let load = MachineTerm::MemoryLoad(before.clone(), Box::new(slot.clone()), LoadKind::Int32);
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
                ProgramValue::UInt64(MachineTerm::uint64_constant(0)),
            );
            let mut transitions = vec![(before.memory().clone(), memory.clone(), written)];
            // Separation across more than one write requires an explicit
            // chain; the cached prefix alone is not a complete-pointer proof.
            for n in 0..later_stores {
                let previous = memory.clone();
                let write = slot.offset_by_bytes(16 + 8 * n);
                memory = memory.store(
                    write.clone(),
                    ProgramValue::UInt64(MachineTerm::uint64_constant(1)),
                );
                transitions.push((previous, memory.clone(), write));
            }
            let old_read = Pointer::loaded_value(&before, &slot);
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
                &ProgramValue::Int32(MachineTerm::Variable(variable)),
                ProgramType::Int64Pointer,
                &mut facts,
                &context,
                None,
                LoadPurpose::Program,
            )
            .expect("typed cached read") else {
                panic!("pointer read")
            };
            let new_read = result.designation();
            let retained = facts.iter().fold(PureFactContext::new(), |context, fact| {
                context.assume_execution_pure_fact(fact)
            });
            assert_eq!(
                retained
                    .equality_graph
                    .designations_equal(&old_read, new_read),
                expected,
                "owned bytes={owned_bytes}, overlap={overlap}, later stores={later_stores}"
            );
            assert!(
                !PureFactContext::new()
                    .equality_graph
                    .designations_equal(&old_read, new_read)
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
                            after: exit.clone(),
                            writes: vec![(write, 8)],
                        }],
                        &explicit,
                    )
                    .expect("one explicitly supplied separated write");
                    explicit = explicit.assume_proposition(equality);
                }
                assert!(
                    explicit
                        .equality_graph
                        .designations_equal(&old_read, new_read),
                    "explicit complete-pointer frames recover the long case"
                );
            }
        }
    }

    #[test]
    fn cached_typed_read_retains_exact_definition_without_admitting_facts() {
        let context = PureFactContext::new();
        let address = Pointer::symbolic(Variable(92_310));
        let retained_state = intern_memory(Memory::new());
        let load = MachineTerm::MemoryLoad(
            retained_state.clone(),
            Box::new(address.clone()),
            crate::kernel::LoadKind::Int32,
        );
        let (variable, _) = load_variable_for_term(&load).expect("load identity");
        let mut facts = crate::kernel::ExecutionFacts::new();
        let source = test_load_source(0);
        let ProgramValue::Pointer(value) = canonicalized_pointer_value_from_int_cell(
            &retained_state,
            &address,
            &ProgramValue::Int32(MachineTerm::Variable(variable)),
            ProgramType::Int64Pointer,
            &mut facts,
            &context,
            Some(&source),
            LoadPurpose::Program,
        )
        .expect("cached typed pointer") else {
            panic!("expected pointer");
        };
        // The cached read is named by its exact definition, without any
        // producer fact being admitted first.
        let application = Pointer::loaded_value(&retained_state, &address);
        assert_eq!(value.pointer(), &application);
        assert!(
            facts.is_empty(),
            "the descriptor needs no defining equation"
        );
        assert!(context.pointers_known_equal(value.pointer(), &application));
        assert!(context.pure_facts().is_empty());
        assert!(
            ResourceContext::new()
                .memory_write_range(value.pointer(), 8, &context)
                .is_none()
        );
        let sibling = PureFactContext::new();
        assert!(sibling.pointers_known_equal(value.pointer(), &application));
        assert!(sibling.pure_facts().is_empty());
        let declared =
            intern_memory(Memory::new().with_block(PointerBlock::from("global:other"), 8));
        assert!(
            context
                .pointers_known_equal(value.pointer(), &Pointer::loaded_value(&declared, &address))
        );
        let later = intern_memory(
            declared
                .memory()
                .clone()
                .store(address.offset_by_bytes(4), crate::kernel::uint8(1u32)),
        );
        assert!(
            !context
                .pointers_known_equal(value.pointer(), &Pointer::loaded_value(&later, &address))
        );
    }

    #[test]
    fn cached_pointer_prefix_cannot_recover_bounds_after_an_upper_half_write() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer::symbolic(Variable(92_312));
        let before = Memory::new();
        let (variable, _) = load_variable_for_term(&MachineTerm::MemoryLoad(
            intern_memory_ref(&before),
            Box::new(address.clone()),
            LoadKind::Int32,
        ))
        .unwrap();
        let cached = ProgramValue::Int32(MachineTerm::Variable(variable));
        let read = |memory: &Memory, context: &PureFactContext| {
            let ProgramValue::Pointer(value) = canonicalized_pointer_value_from_int_cell(
                memory,
                &address,
                &cached,
                ProgramType::Int32Pointer,
                &mut ExecutionFacts::new(),
                context,
                None,
                LoadPurpose::Logical,
            )
            .unwrap() else {
                panic!("pointer read")
            };
            value
        };
        let original = read(&before, &PureFactContext::new());
        let base = Pointer {
            block: PointerBlock::Heap(92_312),
            offset: PointerOffsetTerm::Constant(0),
        };
        let bounded = PointerValue::new(base.clone(), ProgramType::Int32Pointer).with_extent(Some(
            SubobjectExtent {
                start: base,
                width: 4u32.into(),
            },
        ));
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_value_equal(original.clone(), bounded.clone()),
            true,
        );
        assert_eq!(
            context
                .pointer_value_at_entry(&original)
                .extent()
                .unwrap()
                .width,
            MachineTerm::constant(4)
        );
        let unchanged = before.clone().with_block("unrelated-pointer-cache", 4);
        assert_eq!(
            context
                .pointer_value_at_entry(&read(&unchanged, &context))
                .extent()
                .unwrap()
                .width,
            MachineTerm::constant(4)
        );
        let observed = before
            .clone()
            .materialize_symbolic_cell(address.clone(), ProgramType::Int32)
            .materialize_symbolic_cell(address.clone().offset_by_bytes(4), ProgramType::Int32);
        let observed_read = read(&observed, &context);
        assert_eq!(observed_read.pointer(), original.pointer());
        assert!(context.pointer_designations_match(&observed_read, &bounded));
        assert_eq!(
            context
                .pointer_value_at_entry(&observed_read)
                .extent()
                .unwrap()
                .width,
            MachineTerm::constant(4)
        );
        let overwritten = observed.store(
            address.clone().offset_by_bytes(4),
            ProgramValue::UInt32(0u32.into()),
        );
        let changed = read(&overwritten, &context);
        assert_eq!(
            changed.pointer(),
            original.pointer(),
            "the cached numeric prefix is unchanged; it cannot supply bounds"
        );
        assert!(!context.pointer_designations_match(&changed, &bounded));
        assert!(context.pointer_value_at_entry(&changed).extent().is_none());
    }

    #[test]
    fn cached_volatile_pointer_read_has_no_retainable_definition() {
        let context = PureFactContext::new();
        let address = Pointer::symbolic(Variable(92_311));
        let retained_state = intern_memory(Memory::new());
        let load = MachineTerm::MemoryLoad(
            retained_state.clone(),
            Box::new(address.clone()),
            crate::kernel::LoadKind::Int32,
        );
        let (variable, _) = load_variable_for_term(&load).expect("load identity");
        let mut facts = crate::kernel::ExecutionFacts::new();
        let ProgramValue::Pointer(value) = canonicalized_pointer_value_from_int_cell(
            &retained_state,
            &address,
            &ProgramValue::Int32(MachineTerm::Variable(variable)),
            ProgramType::Int64Pointer,
            &mut facts,
            &context,
            None,
            LoadPurpose::VolatileProgram,
        )
        .expect("cached volatile pointer") else {
            panic!("expected pointer");
        };
        for fact in &facts {
            fact.retain_pointer_read_definition(&context);
        }
        assert!(!context.pointers_known_equal(
            value.pointer(),
            &Pointer::loaded_value(&retained_state, &address)
        ));
    }

    #[test]
    fn completed_pointer_reads_join_through_later_graph_address_equality() {
        let memory = Memory::new();
        let retained_state = intern_memory(memory.clone());
        let a = Pointer::symbolic(Variable(92_100));
        let b = Pointer::symbolic(Variable(92_101));
        let read = |address: &Pointer, volatile| {
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
            (value.pointer().clone(), paths[0].facts.clone())
        };
        let (x, x_facts) = read(&a, false);
        let (y, y_facts) = read(&b, false);
        let empty = PureFactContext::new();
        // A completed program read is named by its own read.
        assert_eq!(x, Pointer::loaded_value(&retained_state, &a));
        assert_eq!(y, Pointer::loaded_value(&retained_state, &b));
        let available = x_facts
            .iter()
            .chain(&y_facts)
            .fold(empty.clone(), |context, fact| {
                context.assume_execution_pure_fact(fact)
            });
        assert!(available.pointers_known_equal(&x, &Pointer::loaded_value(&retained_state, &a)));
        assert!(!empty.pointers_known_equal(&x, &y));
        let branch = available
            .clone()
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
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
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
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
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b), true);
        assert!(address_only.pointers_known_equal(&x, &y));
        assert!(owner.permits_memory_read(&y, 4, &address_only));
        assert!(!ResourceContext::new().permits_memory_read(&y, 4, &address_only));
        assert!(!address_only.pointers_known_equal(&x, &y.offset_by_bytes(8)));
        let declared = intern_memory(
            memory
                .clone()
                .with_block(PointerBlock::from("global:later"), 8),
        );
        assert!(available.pointers_known_equal(&x, &Pointer::loaded_value(&declared, &a)));
        let later = intern_memory(
            declared
                .memory()
                .clone()
                .store(a.offset_by_bytes(4), crate::kernel::uint8(1u32)),
        );
        assert!(!available.pointers_known_equal(&x, &Pointer::loaded_value(&later, &a)));
        let volatile_address = Pointer::symbolic(Variable(92_102));
        let (volatile_value, volatile_facts) = read(&volatile_address, true);
        let volatile_context = volatile_facts.iter().fold(empty, |context, fact| {
            context.assume_execution_pure_fact(fact)
        });
        assert!(!volatile_context.pointers_known_equal(
            &volatile_value,
            &Pointer::loaded_value(&retained_state, &volatile_address),
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
                .pointers_known_equal(&volatile_same, &Pointer::loaded_value(&retained_state, &a),)
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
        use crate::kernel::proof::ProofFacts;
        use crate::kernel::proof::fact_reasoning::normalize_using_conditions;
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer::symbolic(Variable(99_100));
        let stored = Pointer::symbolic(Variable(99_101));
        let wrong = Pointer::symbolic(Variable(99_102));
        let empty = PureFactContext::new();
        let equality = |left: &Pointer, right: &Pointer| {
            Proposition::ConditionIs(
                ConditionTerm::pointer_equal(left.clone(), right.clone()),
                true,
            )
        };
        let memory = Memory::new().store(
            address.clone(),
            ProgramValue::typed_pointer(stored.clone(), ProgramType::Int32Pointer),
        );
        let read = |memory: Memory, address: &Pointer, variable, width| {
            record_load_access_width(&memory, address, width);
            let value = Pointer::symbolic(Variable(variable));
            empty.register_pointer_read(&value, &intern_memory(memory), address);
            value
        };
        let value = read(memory.clone(), &address, 99_103, 8);
        let premise = equality(&stored, &Pointer::null());
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&premise));
        for goal in [
            equality(&value, &Pointer::null()),
            equality(&Pointer::null(), &value),
        ] {
            assert!(
                normalize_using_conditions(&goal, std::slice::from_ref(&premise), &facts).is_ok()
            );
            assert!(
                normalize_using_conditions(&goal, &[], &ProofFacts::from_ordered(&[])).is_err()
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
                &equality(&value.offset_by_bytes(4), &Pointer::null()),
                std::slice::from_ref(&premise),
                &facts
            )
            .is_err()
        );
        let changed = memory
            .without_possible_aliasing_cells(&address.offset_by_bytes(4), 4, &empty)
            .store(
                address.offset_by_bytes(4),
                ProgramValue::Int32(MachineTerm::constant(0)),
            );
        let changed = read(changed, &address, 99_104, 8);
        assert!(
            normalize_using_conditions(
                &equality(&changed, &Pointer::null()),
                std::slice::from_ref(&premise),
                &facts
            )
            .is_err()
        );
        let narrow_address = Pointer::symbolic(Variable(99_105));
        let narrow = read(
            Memory::new().store(
                narrow_address.clone(),
                ProgramValue::typed_pointer(stored, ProgramType::Int32Pointer),
            ),
            &narrow_address,
            99_106,
            4,
        );
        assert!(
            normalize_using_conditions(
                &equality(&narrow, &Pointer::null()),
                std::slice::from_ref(&premise),
                &facts
            )
            .is_err()
        );
        let scalar_address = Pointer::symbolic(Variable(99_107));
        let scalar = read(
            Memory::new().store(
                scalar_address.clone(),
                ProgramValue::UInt64(MachineTerm::uint64_constant(0)),
            ),
            &scalar_address,
            99_108,
            8,
        );
        assert!(
            normalize_using_conditions(
                &equality(&scalar, &Pointer::null()),
                &[],
                &ProofFacts::from_ordered(&[])
            )
            .is_err()
        );
    }

    /// Same-block pointer equality is lowered to offset equality. It still
    /// needs an exact typed read, including its stride and unambiguous origin.
    #[test]
    fn normalize_recorded_pointer_reads_checks_definition() {
        use crate::kernel::proof::ProofFacts;
        use crate::kernel::proof::fact_reasoning::normalize_using_conditions;
        let _session = crate::kernel::VerificationSession::enter();
        let context = PureFactContext::new();
        let facts = ProofFacts::from_ordered(&[]);
        let address = Pointer::symbolic(Variable(103_001));
        let stored = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(103_002)), 4),
        };
        let memory = Memory::new().store(
            address.clone(),
            ProgramValue::typed_pointer(stored.clone(), ProgramType::Int32Pointer),
        );
        record_load_access_width(&memory, &address, 8);
        let read = Pointer::loaded_value(&intern_memory(memory.clone()), &address);
        let equality = |left: &Pointer, right: &Pointer| {
            Proposition::ConditionIs(
                ConditionTerm::PointerEqual(Box::new(left.clone()), Box::new(right.clone())),
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
        let wrong_value = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(103_004)), 4),
        };
        assert!(normalize_using_conditions(&equality(&read, &wrong_value), &[], &facts).is_err());
        let partial = memory
            .without_possible_aliasing_cells(&address.offset_by_bytes(4), 4, &context)
            .store(
                address.offset_by_bytes(4),
                ProgramValue::Int32(MachineTerm::constant(0)),
            );
        record_load_access_width(&partial, &address, 8);
        let changed = Pointer::loaded_value(&intern_memory(partial), &address);
        assert!(normalize_using_conditions(&equality(&changed, &stored), &[], &facts).is_err());
    }
    /// Canonical read states retain an exact projection edge back to the
    /// execution source. The selected alias is still required to find its store.
    #[test]
    fn normalize_recorded_pointer_value_follows_exact_projection_source() {
        use crate::kernel::proof::ProofFacts;
        use crate::kernel::proof::fact_reasoning::normalize_using_conditions;
        let _session = crate::kernel::VerificationSession::enter();
        let context = PureFactContext::new();
        let address = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(104_001)), 4),
        };
        let written = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(104_002)), 4),
        };
        let stored = Pointer::symbolic(Variable(104_003));
        let source = Memory::new()
            .with_block_without_derivation("local:projection", 4)
            .store(
                written.clone(),
                ProgramValue::typed_pointer(stored.clone(), ProgramType::Int32Pointer),
            );
        record_load_access_width(&source, &address, 8);
        let source = intern_memory(source);
        let original =
            MachineTerm::MemoryLoad(source.clone(), Box::new(address.clone()), LoadKind::Int32);
        let projected = crate::kernel::memory_provenance::canonicalize_atomic_loads_deep(&original);
        let MachineTerm::MemoryLoad(projected, _, _) = projected else {
            panic!("an unresolved aliased read must remain a load");
        };
        assert_ne!(source, projected);
        record_load_access_width(&projected, &address, 8);
        let read = Pointer::symbolic(Variable(104_004));
        context.register_pointer_read(&read, &projected, &address);
        let alias = Proposition::ConditionIs(ConditionTerm::pointer_equal(address, written), true);
        let goal = Proposition::ConditionIs(ConditionTerm::pointer_equal(read, stored), true);
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&alias));
        assert!(normalize_using_conditions(&goal, std::slice::from_ref(&alias), &facts).is_ok());
        assert!(normalize_using_conditions(&goal, &[], &ProofFacts::from_ordered(&[])).is_err());
    }
    #[test]
    fn symbolic_storage_pointer_cells_share_logical_read_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer::symbolic(Variable(190_101));
        let memory = Memory::new();
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
                symbolic_storage_cell_value(&memory, &address, program_type, false).unwrap();
            let logical = memory.symbolic_pointer_load(&address, program_type);
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
        let old = symbolic_storage_cell_value(&memory, &address, ProgramType::Int32Pointer, false)
            .unwrap();
        let new = symbolic_storage_cell_value(&changed, &address, ProgramType::Int32Pointer, false)
            .unwrap();
        assert!(old != new);
    }

    #[test]
    fn symbolic_pointer_load_factory_retains_exact_read_definition() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer::symbolic(Variable(190_001));
        let memory = Memory::new();
        let ProgramValue::Pointer(value) =
            memory.symbolic_pointer_load(&address, ProgramType::Int32Pointer)
        else {
            panic!("typed pointer read")
        };
        assert_eq!(
            crate::kernel::equality_graph::logical_pointer_read_term(value.pointer()),
            Some(MachineTerm::MemoryLoad(
                intern_memory(memory.clone()),
                Box::new(address.clone()),
                LoadKind::Int32,
            )),
        );
        // Recording a definition does not settle a value or grant a cell.
        let assumptions = PureFactContext::new();
        assert_eq!(
            assumptions.decide(&ConditionTerm::pointer_equal(
                value.pointer().clone(),
                Pointer::symbolic(Variable(190_002)),
            )),
            None
        );
        assert!(!memory.is_loadable_concretely(&address, 8));
        let cell_bits = MachineTerm::MemoryLoad(
            intern_memory(memory),
            Box::new(address.clone()),
            LoadKind::Int32,
        );
        // The pointee width does not enter the read's identity.
        assert_eq!(
            &Pointer::loaded(&cell_bits.clone()).unwrap(),
            value.pointer()
        );
        // A displaced read, or an address indexed by the cell's scalar, has
        // no read definition of its own.
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_term(
                &value.pointer().offset_by_bytes(8)
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
    fn pointer_read_comparison_preserves_the_complete_stored_extent() {
        let _session = VerificationSession::enter();
        let slot = Pointer::symbolic(Variable(989_001));
        let target = Pointer::symbolic(Variable(989_002));
        let stored = PointerValue::new(target.clone(), ProgramType::Int32Pointer).with_extent(
            Some(SubobjectExtent {
                start: target.clone(),
                width: 4u32.into(),
            }),
        );
        let memory =
            intern_memory(Memory::new().store(slot.clone(), ProgramValue::Pointer(stored.clone())));
        let read = PointerValue::new(
            Pointer::loaded_value(&memory, &slot),
            ProgramType::Int32Pointer,
        );
        let equal = Proposition::ConditionIs(
            ConditionTerm::PointerValueEqual(Box::new(read.clone()), Box::new(stored)),
            true,
        );
        assert!(holds_by_read_over_write(&equal));
        let larger = PointerValue::new(target.clone(), ProgramType::Int32Pointer).with_extent(
            Some(SubobjectExtent {
                start: target,
                width: 8u32.into(),
            }),
        );
        let unequal = Proposition::ConditionIs(
            ConditionTerm::PointerValueEqual(Box::new(read), Box::new(larger)),
            true,
        );
        assert!(!holds_by_read_over_write(&unequal));
    }

    #[test]
    fn pointer_read_comparison_keeps_explicit_bounds_on_the_read() {
        let _session = VerificationSession::enter();
        let slot = Pointer::symbolic(Variable(989_020));
        let target = Pointer::symbolic(Variable(989_021));
        let stored = PointerValue::new(target.clone(), ProgramType::Int32Pointer).with_extent(
            Some(SubobjectExtent {
                start: target.clone(),
                width: 4u32.into(),
            }),
        );
        let memory =
            intern_memory(Memory::new().store(slot.clone(), ProgramValue::Pointer(stored.clone())));
        let read = PointerValue::new(
            Pointer::loaded_value(&memory, &slot),
            ProgramType::Int32Pointer,
        )
        .with_extent(Some(SubobjectExtent {
            start: target,
            width: 8u32.into(),
        }));
        let unequal = Proposition::ConditionIs(
            ConditionTerm::PointerValueEqual(Box::new(read), Box::new(stored)),
            true,
        );
        assert!(!holds_by_read_over_write(&unequal));
    }

    #[test]
    fn integer_read_over_write_follows_a_stored_pointer_address() {
        let _session = VerificationSession::enter();
        let slot = Pointer {
            block: PointerBlock::Heap(989_003),
            offset: PointerOffsetTerm::Constant(0),
        };
        let target = Pointer {
            block: PointerBlock::Heap(989_004),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = intern_memory(
            Memory::new()
                .store(
                    slot.clone(),
                    ProgramValue::typed_pointer(target.clone(), ProgramType::Int32Pointer),
                )
                .store(target.offset_by_bytes(4), ProgramValue::Int32(37u32.into())),
        );
        let address = Pointer::loaded_value(&memory, &slot).offset_by_bytes(4);
        let raw = MachineTerm::MemoryLoad(memory, Box::new(address), LoadKind::Int32);
        let (name, _) = load_variable_for_term(&raw).expect("the integer read has a version name");
        assert_eq!(
            read_over_write_value(&MachineTerm::Variable(name)),
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
        let cell = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let unrelated = Pointer {
            block: PointerBlock::Heap(985_003),
            offset: PointerOffsetTerm::Constant(0),
        };
        let first = crate::kernel::intern_memory(
            Memory::new().store(unrelated.clone(), ProgramValue::UInt32(1u32.into())),
        );
        let named = Pointer::version_read(&first, &cell);
        let context = PureFactContext::new();
        assert!(context.pointers_known_equal(&named, &Pointer::loaded_value(&first, &cell)));
        let later = crate::kernel::intern_memory(
            first
                .memory()
                .clone()
                .store(unrelated, ProgramValue::UInt32(2u32.into())),
        );
        let later_read = Pointer::loaded_value(&later, &cell);
        assert_eq!(named, Pointer::version_read(&later, &cell));
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
                .pointers_known_equal(&named, &Pointer::loaded_value(&first, &cell))
        );
    }

    #[test]
    fn named_pointer_reads_retain_the_original_state_definition() {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let source = crate::kernel::intern_memory(Memory::new().store(
            Pointer {
                block: PointerBlock::Heap(985_001),
                offset: PointerOffsetTerm::Constant(0),
            },
            ProgramValue::UInt32(1u32.into()),
        ));
        let named = PointerValue::new(
            Pointer::version_read(&source, &cell),
            ProgramType::Int32Pointer,
        );
        let original = PointerValue::new(
            Pointer::loaded_value(&source, &cell),
            ProgramType::Int32Pointer,
        );
        assert_ne!(named.pointer(), original.pointer());
        let context = PureFactContext::new();
        assert!(context.equality_graph.knows_condition(
            &ConditionTerm::PointerValueEqual(Box::new(named.clone()), Box::new(original)),
            true,
        ));
        let changed = crate::kernel::intern_memory(
            source
                .memory()
                .clone()
                .store(cell.offset_by_bytes(4), ProgramValue::UInt32(9u32.into())),
        );
        let changed = PointerValue::new(
            Pointer::loaded_value(&changed, &cell),
            ProgramType::Int32Pointer,
        );
        assert!(!context.equality_graph.knows_condition(
            &ConditionTerm::PointerValueEqual(Box::new(named), Box::new(changed)),
            true,
        ));
    }

    #[test]
    fn named_pointer_reads_retain_complete_stored_values_in_the_graph() {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = Pointer::symbolic(Variable(981_301));
        let target = Pointer::symbolic(Variable(981_302));
        let stored = PointerValue::new(target.clone(), ProgramType::Int32Pointer).with_extent(
            Some(SubobjectExtent {
                start: target.clone(),
                width: 4u32.into(),
            }),
        );
        let memory = crate::kernel::intern_memory(
            Memory::new().store(slot.clone(), ProgramValue::Pointer(stored.clone())),
        );
        let named = PointerValue::new(
            Pointer::version_read(&memory, &slot),
            ProgramType::Int32Pointer,
        );
        assert_ne!(named.pointer(), stored.pointer());
        assert_ne!(named.designation(), stored.designation());
        let context = PureFactContext::new();
        assert!(context.equality_graph.knows_condition(
            &ConditionTerm::PointerValueEqual(Box::new(named.clone()), Box::new(stored.clone())),
            true,
        ));
        let other_extent = stored.clone().with_extent(Some(SubobjectExtent {
            start: target,
            width: 8u32.into(),
        }));
        assert!(!context.equality_graph.knows_condition(
            &ConditionTerm::PointerValueEqual(Box::new(named), Box::new(other_extent)),
            true,
        ));
    }
}

#[test]
fn arithmetic_comparison_normalizes_selected_read_addresses_without_changing_terms() {
    use crate::kernel::{MachineBinaryOp, MachineIntegerType};
    let _session = crate::kernel::VerificationSession::enter();
    let index = MachineTerm::Variable(Variable(989_784));
    let written = MachineTerm::logical_machine_binary(
        MachineIntegerType::UInt64,
        MachineBinaryOp::Add,
        MachineTerm::uint64_constant(0),
        index.clone(),
    );
    let pointer = |value| Pointer {
        block: Pointer::symbolic(Variable(989_785)).block,
        offset: PointerOffsetTerm::scaled_int64_node(value, 4, true),
    };
    let memory = crate::kernel::intern_memory(Memory::new());
    let read = |memory, value| {
        crate::kernel::canonical_form_of_load(memory, pointer(value), LoadKind::Int32)
    };
    let original = read(memory.clone(), written.clone());
    let simple = read(memory.clone(), index.clone());
    let equality = |left, right| Proposition::ConditionIs(ConditionTerm::equal(left, right), true);
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
        MachineTerm::Binary {
            op: MachineBinaryOp::Add,
            ..
        }
    ));
    let changed = Memory::new().store(
        pointer(index.clone()),
        ProgramValue::Int32(MachineTerm::constant(17)),
    );
    let different_state = equality(original, read(crate::kernel::intern_memory(changed), index));
    assert!(!crate::kernel::proposition_holds_without_facts(
        &comparison_form(&different_state).unwrap_or(different_state)
    ));
}

#[test]
fn scalar_read_presence_survives_shared_admission_and_registry_reset() {
    use crate::kernel::{IntegerTerm, SharedMachineIntegerTerm, Term};
    let _session = crate::kernel::VerificationSession::enter();
    let memory = crate::kernel::intern_memory(Memory::new());
    let pointer = Pointer::symbolic(Variable(997171));
    let name = load_variable_for_exact_cell(&memory, &pointer, LoadKind::Int32, 4);
    let observed = |term| {
        Proposition::Equal(
            Term::Integer(IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                term,
            ))),
            Term::Integer(IntegerTerm::constant_i64(0)),
        )
    };
    let shared = observed(MachineTerm::Variable(name));
    assert!(proposition_mentions_scalar_read(&shared));
    assert!(proposition_mentions_load_variable(&shared));
    clear_load_variable_registry();
    assert!(proposition_mentions_scalar_read(&shared));
    assert!(proposition_mentions_load_variable(&shared));
    assert!(!proposition_mentions_scalar_read(&observed(
        MachineTerm::Variable(Variable(997172))
    )));
}

#[cfg(test)]
mod structural_read_connective_tests {
    use super::*;
    use crate::kernel::VerificationSession;

    #[test]
    fn exact_read_occurrences_match_names_before_stored_value_folding() {
        let _session = VerificationSession::enter();
        let address = Pointer::symbolic(Variable(989_032));
        let memory =
            intern_memory(Memory::new().store(address.clone(), ProgramValue::Int32(37u32.into())));
        let name = load_variable_for_cell(&memory, &address, LoadKind::Int32);
        let read = registered_load_term_for_variable(&name).unwrap();
        let named = MachineTerm::Variable(name);
        assert!(terms_have_same_canonical_form(&read, &named));
        assert!(terms_have_same_canonical_form(&named, &read));
        let other = MachineTerm::MemoryLoad(
            memory,
            Box::new(address.offset_by_bytes(4)),
            LoadKind::Int32,
        );
        assert!(!terms_have_same_canonical_form(&other, &named));
    }

    #[test]
    fn stored_structural_reads_compare_inside_logical_connectives() {
        let _session = VerificationSession::enter();
        let address = Pointer::symbolic(Variable(989_031));
        let memory =
            intern_memory(Memory::new().store(address.clone(), ProgramValue::Int32(37u32.into())));
        let read = MachineTerm::MemoryLoad(memory, Box::new(address), LoadKind::Int32);
        let observed = IntegerTerm::from_machine(MachineIntegerType::Int32, read).unwrap();
        let leaf = Proposition::ConditionIs(
            ConditionTerm::integer_equal(observed, IntegerTerm::constant_i64(37)),
            true,
        );
        let expected = comparison_form(&leaf).expect("stored value comparison");
        let guard = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
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
