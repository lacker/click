use super::*;

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
pub(in crate::kernel) fn evaluate_c_memory_load_paths(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    has_external_read_resource: bool,
    volatile: bool,
    source: Option<&LoadSourceId>,
    byte_order: Option<ByteOrder>,
) -> Vec<CExpressionPath> {
    let _assumptions_id_scope = assumptions.enter_id_scope();
    if has_pending_reallocation_for_pointer(memory, &pointer) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::UnresolvedAllocationOutcome),
            facts,
            obligations,
        }];
    }
    let mut alias_cache = MemoryLoadAliasCache::default();
    let observed = (!volatile && assumptions.should_require_owned_expression_loads())
        .then(|| (crate::kernel::intern_c_memory_ref(memory), pointer.clone()));
    let mut paths = evaluate_c_memory_load_paths_with_alias_cache(
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
    if let Some(observed) = observed {
        for path in &mut paths {
            let CExpressionOutcome::Value(CValue::Pointer(value)) = &path.outcome else {
                continue;
            };
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
/// A specification load denotes the value one named snapshot holds at one
/// pointer. It is not a step of the program, so it has no branch to take: an
/// alias it cannot resolve leaves the load term unresolved rather than
/// splitting into the cases a C execution would have to choose between. The
/// one-term spec load rule already governs the non-symbolic spec path in
/// `crate::kernel::spec`; this is the same rule on the symbolic one.
#[allow(clippy::too_many_arguments)]
pub(in crate::kernel) fn evaluate_spec_memory_load_paths(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let _assumptions_id_scope = assumptions.enter_id_scope();
    if has_pending_reallocation_for_pointer(memory, &pointer) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::UnresolvedAllocationOutcome),
            facts,
            obligations,
        }];
    }
    let mut alias_cache = MemoryLoadAliasCache::default();
    evaluate_c_memory_load_paths_with_alias_cache(
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
        // A specification load denotes a snapshot's cell, not a C access;
        // it has no byte view of a wider cell.
        None,
    )
}

/// Construct the value of a logical read using the shared typed load model.
/// No C access occurs and no validity evidence is introduced.
pub(in crate::kernel) fn evaluate_logical_memory_load_paths(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let pointer = logical_memory_load_address(memory, pointer, value_type, assumptions);
    if let Some(value) = super::uint32_representation::observe_value(
        memory,
        &pointer,
        value_type,
        assumptions.should_keep_spec_loads_symbolic(),
    ) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }
    if assumptions.should_keep_spec_loads_symbolic() {
        let _assumptions_id_scope = assumptions.enter_id_scope();
        let mut paths = evaluate_c_memory_load_paths_with_alias_cache(
            memory,
            pointer.clone(),
            value_type,
            facts,
            obligations,
            assumptions,
            false,
            LoadPurpose::Logical,
            &mut MemoryLoadAliasCache::default(),
            None,
            None,
        );
        for path in &mut paths {
            // An invalid typed read still denotes a logical value. The C
            // evaluator's refusal is retained only by checked evaluation.
            if matches!(path.outcome, CExpressionOutcome::RuntimeError(_))
                && let Some(value) = canonicalized_symbolic_load_value_with_identity(
                    memory,
                    &pointer,
                    value_type,
                    &mut path.facts,
                    assumptions,
                    should_use_symbolic_pointer_identity(memory, &pointer, value_type),
                    None,
                    LoadPurpose::Logical,
                )
            {
                path.outcome = CExpressionOutcome::Value(value);
            }
            path.facts
                .retain(|fact| !is_load_variable_defining_fact(fact.proposition()));
        }
        return paths;
    }
    let mut facts = facts;
    let value = memory
        .known_union_value(&pointer, value_type)
        .filter(|value| value_type.accepts(value))
        .or_else(|| {
            memory.known_value(&pointer).and_then(|stored| {
                let complete_pointer = matches!(&stored, CValue::Pointer(_))
                    || matches!(&stored, CValue::Int32(Bitvector32Term::Variable(variable))
                        if registered_load_kind_for_variable(variable) == Some(LoadKind::Bits32)
                            && registered_load_bytes_for_variable(variable)
                                == Some(crate::kernel::C_POINTER_BYTE_WIDTH));
                canonicalized_pointer_value_from_int_cell(
                    &pointer,
                    &stored,
                    value_type,
                    &mut facts,
                    assumptions,
                    None,
                    LoadPurpose::Logical,
                )
                .or_else(|| value_type.accepts(&stored).then_some(stored))
                .inspect(|value| {
                    if let CValue::Pointer(value) = value {
                        record_pointer_read_observation(value.pointer(), memory, &pointer);
                        let current = Pointer::loaded_value(
                            &crate::kernel::intern_c_memory_ref(memory),
                            &pointer,
                        );
                        if complete_pointer
                            && !assumptions.pointers_known_equal(value.pointer(), &current)
                        {
                            // The cached value was selected under this path's
                            // premises. Carry its current-cell equation with
                            // the result, rather than treating a global read
                            // observation as evidence in another context.
                            facts.push(ExecutionPureFact::logical_read_equation(
                                value.pointer().clone(),
                                current,
                            ));
                        }
                    }
                })
            })
        })
        .or_else(|| {
            // The cell may be stored under another spelling of this address:
            // a C store through `p` after the path proved `p == id`, read
            // here through `id`. The equality holds on this path, so the
            // stored value is this snapshot's value at the address. Only a
            // block the pointer classes put with others is retried.
            assumptions
                .equality_graph
                .pointer_spellings(&pointer)
                .into_iter()
                .find_map(|spelling| {
                    let stored = memory.known_value(&spelling)?;
                    value_type.accepts(&stored).then_some(stored)
                })
        })
        .or_else(|| {
            canonicalized_symbolic_load_value_with_identity(
                memory,
                &pointer,
                value_type,
                &mut facts,
                assumptions,
                should_use_symbolic_pointer_identity(memory, &pointer, value_type),
                None,
                LoadPurpose::Logical,
            )
        });
    facts.retain(|fact| !is_load_variable_defining_fact(fact.proposition()));
    value
        .into_iter()
        .map(|value| CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts: facts.clone(),
            obligations: obligations.clone(),
        })
        .collect()
}

/// Use a published footprint only to select coordinates for this logical
/// address. Equality of the address grants no access or snapshot transport.
fn logical_memory_load_address(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    assumptions: &PureFactContext,
) -> Pointer {
    // Only opaque model pointers and external pointers with an admitted
    // cross-block alias can need another spelling. Wide scalar loads need
    // the cached coordinate because their equalities do not use int32 load
    // congruence. Keep ordinary and loaded-pointer reads on their fast path.
    let model_pointer = match &pointer.block {
        PointerBlock::Symbolic(variable) if !crate::kernel::is_load_variable(variable) => true,
        PointerBlock::ExternalArgument
            if matches!(value_type, CType::Int64 | CType::UInt64)
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

fn has_pending_reallocation_for_pointer(memory: &CMemory, pointer: &Pointer) -> bool {
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
/// specification read is not a step: it denotes the value the named snapshot
/// holds, and the load term over that snapshot already *is* that value.
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
fn evaluate_c_memory_load_paths_with_alias_cache(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    has_external_read_resource: bool,
    purpose: LoadPurpose,
    alias_cache: &mut MemoryLoadAliasCache,
    source: Option<&LoadSourceId>,
    byte_order: Option<ByteOrder>,
) -> Vec<CExpressionPath> {
    let mut distinct_case = None;
    let mut paths = evaluate_c_memory_load_case(
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
            assumptions: transported,
        } = case;
        if transported.is_some() {
            case_assumptions = transported;
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
        paths.extend(evaluate_c_memory_load_case(
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
    memory: CMemory,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: Option<PureFactContext>,
}

/// One turn of [`evaluate_c_memory_load_paths_with_alias_cache`]: the paths
/// this memory decides, with the distinct case of an undecided cell left in
/// `distinct_case` for the caller. `written` is the memory the load was read
/// at, which every uninitialized-read check asks: `memory` may be a distinct
/// case's, without cells the program wrote.
#[allow(clippy::too_many_arguments)]
fn evaluate_c_memory_load_case(
    memory: &CMemory,
    written: &CMemory,
    pointer: Pointer,
    value_type: CType,
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
) -> Vec<CExpressionPath> {
    let branches_on_unresolved_aliases =
        splits && matches!(purpose, LoadPurpose::Program | LoadPurpose::VolatileProgram);
    let use_symbolic_pointer_identity =
        should_use_symbolic_pointer_identity(memory, &pointer, value_type);
    let mut facts = facts;
    if purpose != LoadPurpose::Logical && memory.is_ended_local_address(&pointer) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
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
        let Some(theorem) = prove_c_condition_fact_transport(&source, memory, assumptions) else {
            continue;
        };
        let Some(target) =
            c_condition_fact_transport_target_in_context(&theorem, &source, assumptions)
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
        && (!memory.may_read_uninitialized_object_under(
            &pointer,
            value_type.byte_width(),
            assumptions,
        ) || purpose == LoadPurpose::Logical
            || written.has_initialized_bytes_under(&pointer, value_type.byte_width(), assumptions)
            || assumptions.has_memory_read_defined_evidence(memory, &pointer, value_type));
    // A typed union overlay is the authoritative view for an exact typed
    // load, including in provenance-sensitive symbolic-load mode. Selecting
    // the raw load first would reinterpret a copied pointer member as an
    // integer and discard its provenance.
    if let Some(value) = memory.known_union_value(&pointer, value_type) {
        if value_type.accepts(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                pointer: pointer.clone(),
                value_type,
                stored: None,
            }),
            facts,
            obligations,
        }];
    }

    if let Some(value) = super::uint32_representation::observe_value(
        memory,
        &pointer,
        value_type,
        allow_symbolic_external_load && assumptions.should_force_symbolic_external_loads(),
    ) {
        super::uint32_representation::record_observation_definition(&value, &mut facts);
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    // Provenance-sensitive lowering asks for the load identity even when this
    // snapshot has already materialized the cell's concrete value. Checking
    // `known_value` first would collapse `at(mark, field == 11)` to `true` and
    // erase the address needed for later frame transport.
    if allow_symbolic_external_load && assumptions.should_force_symbolic_external_loads() {
        let Some(value) = canonicalized_symbolic_load_value_with_identity(
            memory,
            &pointer,
            value_type,
            &mut facts,
            assumptions,
            use_symbolic_pointer_identity,
            source,
            purpose,
        ) else {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                }),
                facts,
                obligations,
            }];
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    // A pointer-typed load of a materialized int32 cell that is not a bare
    // load term (for example a call-havoc variable standing for the framed
    // field) cannot be reinterpreted as a stable pointer form. When the
    // caller permits symbolic external loads, fall through to the symbolic
    // load below — its load-term form relates across snapshots — instead
    // of failing the load.
    let pointer_cell_defers_to_symbolic = |value: &CValue| {
        (matches!(value, CValue::Int32(_))
            || (matches!(value_type, CType::FunctionPointer(_))
                && matches!(
                    value,
                    CValue::Int8(_)
                        | CValue::Int16(_)
                        | CValue::UInt8(_)
                        | CValue::UInt16(_)
                        | CValue::UInt32(_)
                        | CValue::Int64(_)
                        | CValue::UInt64(_)
                )))
            && value_type.is_pointer()
            && has_external_read_resource
            && (assumptions.should_prefer_symbolic_external_loads()
                || matches!(value_type, CType::FunctionPointer(_))
                || (allow_symbolic_external_load
                    && matches!(value, CValue::Int32(Bitvector32Term::Variable(variable))
                        if registered_load_kind_for_variable(variable) == Some(LoadKind::Bits32)
                            && registered_load_bytes_for_variable(variable)
                                .is_some_and(|bytes| bytes < crate::kernel::C_POINTER_BYTE_WIDTH))))
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
            Some(value) => CExpressionOutcome::Value(value),
            None => CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                pointer: pointer.clone(),
                value_type,
                stored: None,
            }),
        };
        return vec![CExpressionPath {
            outcome,
            facts,
            obligations,
        }];
    }
    // An exact materialized cell is already the authoritative value for this
    // non-union pointer. Avoid proving every other symbolic cell distinct
    // before the direct map lookup.
    if let Some(value) = memory.known_value(&pointer) {
        if let Some(value) = canonicalized_pointer_value_from_int_cell(
            &pointer,
            &value,
            value_type,
            &mut facts,
            assumptions,
            source,
            purpose,
        ) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        if value_type.accepts(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        if !pointer_cell_defers_to_symbolic(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
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
            let (found, visited) = memory.cells.find_candidate_by(
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
            &pointer,
            &value,
            value_type,
            &mut facts,
            assumptions,
            source,
            purpose,
        ) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        if value_type.accepts(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        if !pointer_cell_defers_to_symbolic(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
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
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead),
            facts,
            obligations,
        }];
    }

    if purpose != LoadPurpose::Logical && memory.is_deallocated_heap_address(&pointer, assumptions)
    {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
            facts,
            obligations,
        }];
    }

    if allow_symbolic_external_load && assumptions.should_prefer_symbolic_external_loads() {
        let Some(value) = canonicalized_symbolic_load_value_with_identity(
            memory,
            &pointer,
            value_type,
            &mut facts,
            assumptions,
            use_symbolic_pointer_identity,
            source,
            purpose,
        ) else {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                }),
                facts,
                obligations,
            }];
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    let mut memory = memory.clone();
    // The access width belongs to the snapshot the load is read at, not only
    // to the projection of it that the term ends up carrying. Recording it
    // here as well as inside `symbolic_load_value` is what lets a later
    // caller holding the unreduced snapshot ask how many bytes this load
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
                    // Dropping a cell names this load at a snapshot that no longer
                    // records it, so the question is the same byte question
                    // `1a3b2701` put in front of the three snapshot comparisons:
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
    // The returned symbolic load carries the reduced memory snapshot, so
    // other queries must relate it back to its source. Dropping cells
    // provably distinct from the loaded pointer is a no-op for this load,
    // which is exactly the `CellsForgotten` edge; without it the derivation
    // walk dead-ends at this variant.
    //
    // The reduction choice may depend on `assumptions`, and the reduced map
    // may therefore re-intern as a snapshot older than `reduction_base`.
    // That spelling is sound but deliberately gains no fact-free derivation
    // edge: `record_c_memory_derivation` refuses the backwards edge below.
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
        record_c_memory_derivation(&mut memory, CMemoryDerivation::CellsForgotten { base });
    }

    if pointer.has_symbolic_block() && allow_symbolic_external_load {
        let Some(value) = canonicalized_symbolic_load_value_with_identity(
            &memory,
            &pointer,
            value_type,
            &mut facts,
            assumptions,
            use_symbolic_pointer_identity,
            source,
            purpose,
        ) else {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                }),
                facts,
                obligations,
            }];
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
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
        use_symbolic_pointer_identity,
        source,
        purpose,
    ) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }
    // A run the load indexes symbolically is never split slot by slot. Its
    // slots are one family of cells the facts did not place the index on; a
    // case per slot would only enumerate the array, and the load term over
    // this snapshot is already the value every such case agrees on.
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
                        .iter()
                        .find_map(|(stored_pointer, stored_value)| {
                            (stored_pointer != &pointer
                                && !in_symbolically_indexed_run(stored_pointer)
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
        let stored_bytes = cell_access_byte_width(&stored_value);
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
                &pointer,
                &stored_value,
                value_type,
                &mut facts,
                assumptions,
                source,
                purpose,
            ) {
                CExpressionOutcome::Value(value)
            } else if value_type.accepts(&stored_value) {
                CExpressionOutcome::Value(stored_value)
            } else {
                CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                })
            };
            paths.push(CExpressionPath {
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
                    assumptions: load_assumptions.clone(),
                });
            } else {
                // The cell may still hold some of the loaded bytes, so the
                // load's value is its load over this snapshot, which keeps
                // the cell, and no further case is split from it.
                let outcome = match canonicalized_symbolic_load_value_with_identity(
                    &memory,
                    &pointer,
                    value_type,
                    &mut distinct_facts,
                    assumptions,
                    use_symbolic_pointer_identity,
                    source,
                    purpose,
                ) {
                    Some(value) => CExpressionOutcome::Value(value),
                    None => CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                        pointer: pointer.clone(),
                        value_type,
                        stored: None,
                    }),
                };
                paths.push(CExpressionPath {
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
            CType::Int8 => int8(Bitvector32Term::Constant(0)),
            CType::Int16 => int16(Bitvector32Term::Constant(0)),
            CType::Int32 => int32(Bitvector32Term::Constant(0)),
            CType::UInt8 => uint8(Bitvector32Term::Constant(0)),
            CType::UInt16 => uint16(Bitvector32Term::Constant(0)),
            CType::UInt32 => CValue::UInt32(Bitvector32Term::Constant(0)),
            CType::Int64 => CValue::Int64(Bitvector32Term::Int64Constant(0)),
            CType::UInt64 => CValue::UInt64(Bitvector32Term::UInt64Constant(0)),
            CType::Int128 => match crate::kernel::c_int128_literal(0) {
                CExpression::Value(value) => value,
                _ => unreachable!("wide literal is a value"),
            },
            CType::UInt128 => match crate::kernel::c_uint128_literal(0) {
                CExpression::Value(value) => value,
                _ => unreachable!("wide literal is a value"),
            },
            CType::Float32 => CValue::Float32(Bitvector32Term::Constant(0)),
            CType::Float64 => CValue::Float64(Bitvector32Term::UInt64Constant(0)),
            _ if value_type.is_pointer() => CValue::typed_pointer(Pointer::null(), value_type),
            _ => {
                return vec![CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                        pointer: pointer.clone(),
                        value_type,
                        stored: None,
                    }),
                    facts,
                    obligations,
                }];
            }
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    if memory.is_loadable_concretely(&pointer, value_type.byte_width()) {
        if let Some(value) = cell_value_recorded_on_path(
            &memory,
            &pointer,
            value_type,
            &mut facts,
            assumptions,
            source,
            purpose,
        ) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        let Some(value) = canonicalized_symbolic_load_value_with_identity(
            &memory,
            &pointer,
            value_type,
            &mut facts,
            assumptions,
            use_symbolic_pointer_identity,
            source,
            purpose,
        ) else {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                }),
                facts,
                obligations,
            }];
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    if purpose != LoadPurpose::Logical && !has_external_read_resource {
        let proposition = Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: pointer.clone(),
            bytes: Bitvector32Term::Constant(value_type.byte_width()),
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
                &Bitvector32Term::Constant(value_type.byte_width()),
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
        && ((pointer.block.starts_with("local:") && memory.has_block(&pointer.block))
            || memory.may_read_uninitialized_object_under(
                &pointer,
                value_type.byte_width(),
                assumptions,
            ))
        && !written.has_initialized_bytes_under(&pointer, value_type.byte_width(), assumptions)
        && !assumptions.has_memory_read_defined_evidence(&memory, &pointer, value_type)
    {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead),
            facts,
            obligations,
        }];
    }

    if let Some(value) = cell_value_recorded_on_path(
        &memory,
        &pointer,
        value_type,
        &mut facts,
        assumptions,
        source,
        purpose,
    ) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    let Some(value) = canonicalized_symbolic_load_value_with_identity(
        &memory,
        &pointer,
        value_type,
        &mut facts,
        assumptions,
        use_symbolic_pointer_identity,
        source,
        purpose,
    ) else {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                pointer: pointer.clone(),
                value_type,
                stored: None,
            }),
            facts,
            obligations,
        }];
    };

    vec![CExpressionPath {
        outcome: CExpressionOutcome::Value(value),
        facts,
        obligations,
    }]
}

/// The value a C read finds for its cell in the recorded history on this
/// path, when no cached cell of `memory` answers it.
///
/// This is the cached-cell read above, asked one snapshot further back: a
/// store at an address the facts could not place when it ran drops the cells
/// it may write, and a path that later learns the store missed this cell
/// (`u != 0` for `buf[u] = 7` and a read of `buf[0]`) reads the value the
/// cell held before it. The answer depends on the path's facts exactly as the
/// distinct-cell reduction above does, and like it is spent only on this
/// path's value; nothing is named by it. Only a program read asks: a
/// specification read denotes the named snapshot's value, and a volatile one
/// may observe a write no recorded step made.
#[allow(clippy::too_many_arguments)]
fn cell_value_recorded_on_path(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
) -> Option<CValue> {
    if purpose != LoadPurpose::Program {
        return None;
    }
    let value = crate::kernel::resource_tracker::cell_value_on_path(
        &crate::kernel::intern_c_memory_ref(memory),
        pointer,
        value_type.byte_width(),
        assumptions,
    )?;
    if let Some(value) = canonicalized_pointer_value_from_int_cell(
        pointer,
        &value,
        value_type,
        facts,
        assumptions,
        source,
        purpose,
    ) {
        return Some(value);
    }
    value_type.accepts(&value).then_some(value)
}

/// Preserve a complete designated pointer stored at this exact cell.
/// Unknown legacy reads remain absent until checked symbolic carrier
/// input/output effects can supply their designation together with the address.
fn pointer_value_with_load_designation(
    value: CPointerValue,
    load: &Bitvector32Term,
) -> CPointerValue {
    if value.designation().is_none()
        && value.c_type().is_object_pointer()
        && let Bitvector32Term::MemoryLoad(memory, address, kind) = load
        && let Some(CValue::Pointer(stored)) = memory.known_value(address)
        && stored.designation().is_some()
        && kind.reads_value(&CValue::Pointer(stored.clone()))
    {
        stored.with_type(value.c_type())
    } else {
        value
    }
}

/// Keep a rewritten producer pair together. Only its exact defining read can
/// update a raw load name; an unrelated address equation never qualifies.
pub(crate) fn transport_pointer_load_pair(
    before: &CPointerValue,
    after: CPointerValue,
) -> CPointerValue {
    let (Some(PointerDesignation::Loaded(old)), Some(PointerDesignation::Loaded(new))) =
        (before.designation(), after.designation())
    else {
        return after;
    };
    if old == new {
        return after;
    }
    let registered_here = |variable: Variable| {
        matches!(registered_load_term_for_variable(&variable),
            Some(Bitvector32Term::MemoryLoad(memory, address, LoadKind::Bits32))
                if memory.arena_id() == old.memory().arena_id() && address.as_ref() == old.address())
    };
    enum Spelling {
        Symbolic,
        Application,
        Legacy(Variable),
    }
    let spelling = match &before.pointer().block {
        PointerBlock::Symbolic(variable)
            if registered_here(*variable) && after.pointer().block == before.pointer().block =>
        {
            Spelling::Symbolic
        }
        PointerBlock::LoadedPointer(identity)
            if *identity == old.id() && after.pointer().block == before.pointer().block =>
        {
            Spelling::Application
        }
        block if *block == old.address().block => {
            let mut pending = vec![&before.pointer().offset];
            let mut found = None;
            while let Some(offset) = pending.pop() {
                match offset {
                    PointerOffsetTerm::Add(left, right) => {
                        pending.push(left);
                        pending.push(right);
                    }
                    PointerOffsetTerm::Int32Scaled { value, .. } => {
                        if let Bitvector32Term::Variable(variable) = value.as_ref()
                            && registered_here(*variable)
                        {
                            found = Some(*variable);
                            break;
                        }
                    }
                    _ => {}
                }
            }
            let Some(variable) = found else {
                return after;
            };
            Spelling::Legacy(variable)
        }
        _ => return after,
    };
    let load = Bitvector32Term::MemoryLoad(
        new.memory().clone(),
        Box::new(new.address().clone()),
        LoadKind::Bits32,
    );
    let (variable, _) = load_variable_for_term(&load).expect("a paired read remains a memory load");
    let definition = registered_load_term_for_variable(&variable)
        .expect("a load name retains its defining read");
    let mut pointer = after.pointer().clone();
    match spelling {
        Spelling::Symbolic => pointer.block = PointerBlock::Symbolic(variable),
        Spelling::Application => {
            let Bitvector32Term::MemoryLoad(memory, address, _) = &definition else {
                unreachable!()
            };
            pointer.block = PointerBlock::LoadedPointer(pointer_load_identity(memory, address));
        }
        Spelling::Legacy(old_variable) => {
            let from = Bitvector32Term::Variable(old_variable);
            let to = Bitvector32Term::Variable(variable);
            let term = Term::PointerOffset(pointer.offset);
            let Term::PointerOffset(offset) =
                crate::kernel::proof::term_rewrite::TermRewrite::for_bits(&from, &to).term(&term)
            else {
                unreachable!()
            };
            pointer.offset = offset;
            let Bitvector32Term::MemoryLoad(_, address, _) = &definition else {
                unreachable!()
            };
            pointer.block = address.block.clone();
        }
    }
    let Bitvector32Term::MemoryLoad(memory, address, _) = definition else {
        unreachable!()
    };
    after
        .with_pointer(pointer)
        .with_designation(PointerDesignation::Loaded(PointerLoadIdentity::new(
            memory, *address,
        )))
}

/// Reinterprets an int cell's loaded value as a pointer without letting the
/// load enter the offset. The address name retains its immutable defining
/// read. Only an exact complete designated stored pointer supplies a carrier;
/// unknown legacy reads keep their designation absent.
fn canonicalized_pointer_value_from_int_cell(
    pointer: &Pointer,
    value: &CValue,
    value_type: CType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
) -> Option<CValue> {
    let pointee_byte_width = value_type.pointee_type()?.byte_width();
    let fresh = match value {
        CValue::Int8(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::Int8(Bitvector32Term::Variable(fresh)));
        }
        CValue::Int16(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::Int16(Bitvector32Term::Variable(fresh)));
        }
        CValue::Int32(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            load_variable_for_term(bits)?.0
        }
        // A cell materialized with its load variable (canonicalizing at
        // creation) already carries the variable; record its defining fact
        // in this path's stream, as minting would have.
        CValue::Int32(Bitvector32Term::Variable(variable)) if is_load_variable(variable) => {
            *variable
        }
        _ => return None,
    };
    // Bits32 is also the model's proxy for a complete pointer read. Its
    // scalar container alone does not establish that the defining read
    // covered all pointer bytes.
    if registered_load_kind_for_variable(&fresh) != Some(LoadKind::Bits32)
        || registered_load_bytes_for_variable(&fresh) != Some(crate::kernel::C_POINTER_BYTE_WIDTH)
    {
        return None;
    }
    // The selected cached value already names its defining read. An address
    // alias may spell that cell with a different symbolic storage block; it
    // must not rebase the same pointer value onto that caller spelling.
    let defining_load = registered_load_term_for_variable(&fresh);
    let defining_block = match &defining_load {
        Some(Bitvector32Term::MemoryLoad(_, address, _)) => &address.block,
        _ => &pointer.block,
    };
    // A load variable names the pointer value, not an offset in the
    // storage object containing it. Fresh storage provenance must not
    // manufacture disjointness from the actual pointee.
    let loaded = if matches!(
        defining_block,
        PointerBlock::Heap(_) | PointerBlock::Temporary(_)
    ) || defining_block.starts_with("local:")
    {
        Pointer::symbolic(fresh)
    } else {
        Pointer::loaded(
            defining_block.clone(),
            Bitvector32Term::Variable(fresh),
            i64::from(pointee_byte_width),
        )
    };
    let mut value = CPointerValue::new(loaded.clone(), value_type);
    if let Some(load) = defining_load {
        value = pointer_value_with_load_designation(value, &load);
        if matches!(purpose, LoadPurpose::Logical | LoadPurpose::Validity)
            && let Bitvector32Term::MemoryLoad(memory, address, _) = &load
        {
            assumptions.register_pointer_read(&loaded, memory, address);
        }
        // The cached scalar spelling still comes from this exact typed read.
        // Preserve the same producer evidence as the symbolic load route,
        // recording each source observation once.
        record_load_variable_defining_fact_with_source_and_pointer(
            fresh,
            load,
            facts,
            source,
            (purpose == LoadPurpose::Program).then_some(&loaded),
        );
    }
    Some(CValue::Pointer(value))
}

fn should_use_symbolic_pointer_identity(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
) -> bool {
    // A pointer in heap, temporary, or local storage may target any object.
    // Its storage block supplies no provenance for the loaded value, including
    // after loop havoc (which need not be a call-memory havoc).
    // After a call-havoc edge, an unknown pointer-sized cell may contain the
    // address of any live object, including an automatic local. Give that
    // value an opaque identity instead of deriving a fresh offset in the
    // cell's storage block; equality facts can then resolve a dereference to
    // the object it actually aliases.
    let pointer_sized_load = matches!(
        &pointer.offset,
        PointerOffsetTerm::Int32Scaled { byte_width: 8, .. }
            | PointerOffsetTerm::Int64Scaled { byte_width: 8, .. }
    );
    (matches!(
        pointer.block,
        PointerBlock::Heap(_) | PointerBlock::Temporary(_)
    ) || pointer.block.starts_with("local:")
        || (memory.has_call_memory_havoc() && pointer_sized_load))
        && value_type.is_pointer()
        && memory.known_union_value(pointer, value_type).is_none()
        && memory.known_value(pointer).is_none()
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
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    use_symbolic_identity: bool,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
) -> Option<CValue> {
    use crate::kernel::reasoning::memory_resolution::{RunAccess, run_access};
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
                            && assumptions.decide(&ConditionTerm::uint64_less_than(
                                index.clone(),
                                Bitvector32Term::UInt64Constant(u64::from(*live_high - first)),
                            )) == Some(true)
                    });
            }
            let Some((low, high)) = assumptions.signed_interval_past_exclusions(&index) else {
                return false;
            };
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
        })?
        .clone();
    // A constant run's slots are not loads of its source, which is empty:
    // every live slot holds the run's one value, so the load reads it.
    if let crate::kernel::primitives::RunValueMode::Constant(value) = run.value_mode() {
        return value_type.accepts(value).then(|| value.clone());
    }
    canonicalized_symbolic_load_value_with_identity(
        run.source().memory(),
        pointer,
        value_type,
        facts,
        assumptions,
        use_symbolic_identity,
        source,
        purpose,
    )
}

fn canonicalized_symbolic_load_value_with_identity(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    use_symbolic_identity: bool,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
) -> Option<CValue> {
    // C and logical reads must name the same typed value through a checked
    // opaque address alias. Only the symbolic value's coordinates change:
    // C access validity still checks the original pointer and its provenance.
    let address = logical_memory_load_address(memory, pointer.clone(), value_type, assumptions);
    let value = symbolic_load_value(memory, &address, value_type)?;
    // Terms are canonical at creation: an int or byte load evaluates to its
    // load variable, with the defining fact beside it, so every fact,
    // offset, and range built from the value is canonical.
    match &value {
        CValue::Int8(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::Int8(Bitvector32Term::Variable(fresh)));
        }
        CValue::Int16(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::Int16(Bitvector32Term::Variable(fresh)));
        }
        CValue::Int32(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::Int32(Bitvector32Term::Variable(fresh)));
        }
        CValue::UInt8(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::UInt8(Bitvector32Term::Variable(fresh)));
        }
        CValue::UInt16(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::UInt16(Bitvector32Term::Variable(fresh)));
        }
        // The wider integer scalars name their loads for the same reason.
        // Adoption is atomic across producers: contract lowering already
        // materializes a `uint32`, `int64`, or `uint64` cell with
        // `canonical_form_of_load`, so leaving execution's load of the same
        // cell unnamed would split one value into two terms that only
        // the snapshot could reconnect — and a snapshot the execution has
        // since written cannot. A resource body fact about a `uint64` cell
        // (the rbtree's packed parent word) then survives a write to a
        // sibling cell of the same node, which the fold after that write
        // needs.
        CValue::UInt32(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::UInt32(Bitvector32Term::Variable(fresh)));
        }
        CValue::Int64(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::Int64(Bitvector32Term::Variable(fresh)));
        }
        CValue::UInt64(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::UInt64(Bitvector32Term::Variable(fresh)));
        }
        CValue::Int128(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::Int128(Bitvector32Term::Variable(fresh)));
        }
        CValue::UInt128(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::UInt128(Bitvector32Term::Variable(fresh)));
        }
        _ => {}
    }
    let CValue::Pointer(pointer_value) = &value else {
        return Some(value);
    };
    let Some((block, bits, byte_width)) = pointer_value.pointer().as_loaded() else {
        return Some(value);
    };
    if !matches!(bits, Bitvector32Term::MemoryLoad(_, _, _)) {
        return Some(value);
    }
    let (fresh, load) = load_variable_for_term(bits)?;
    let pointer = if use_symbolic_identity {
        Pointer::symbolic(fresh)
    } else {
        Pointer::loaded(block.clone(), Bitvector32Term::Variable(fresh), byte_width)
    };
    if matches!(purpose, LoadPurpose::Logical | LoadPurpose::Validity) {
        record_pointer_read_observation(&pointer, memory, &address);
        // The logical evaluator constructs a term, not a C access. Retain
        // its exact typed definition in the trusted graph's term metadata;
        // logical evaluation still exports no defining proposition premise.
        // A retained/materialized load can return the same value at a later
        // snapshot. That observation does not replace its immutable producer.
        if let Some(Bitvector32Term::MemoryLoad(memory, address, _)) =
            registered_load_term_for_variable(&fresh)
        {
            assumptions.register_pointer_read(&pointer, &memory, &address);
        }
    }
    let value = pointer_value_with_load_designation(
        pointer_value.clone().with_pointer(pointer.clone()),
        &registered_load_term_for_variable(&fresh).expect("a load retains its defining term"),
    );
    record_load_variable_defining_fact_with_source_and_pointer(
        fresh,
        load,
        facts,
        source,
        (purpose == LoadPurpose::Program).then_some(&pointer),
    );
    Some(CValue::Pointer(value))
}

const LOAD_VARIABLE_BASE: u64 = 1 << 40;
const LOAD_VARIABLE_RANGE: u64 = 1 << 40;
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
        (PointerBlock::Symbolic(variable), PointerOffsetTerm::Constant(0)) => *variable,
        (_, PointerOffsetTerm::Int32Scaled { value, .. }) => {
            let Bitvector32Term::Variable(variable) = value.as_ref() else {
                return None;
            };
            *variable
        }
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
    LOAD_VARIABLE_RANGE
}

/// Runs `body` with only the first `range` load-variable ids available, so
/// distinct loads collide at the hash and a test can watch the probe.
#[cfg(test)]
pub(crate) fn with_load_variable_range<T>(range: u64, body: impl FnOnce() -> T) -> T {
    assert!(range > 0 && range <= LOAD_VARIABLE_RANGE);
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
    (LOAD_VARIABLE_BASE..LOAD_VARIABLE_BASE + LOAD_VARIABLE_RANGE).contains(&variable.0)
}

/// Whether a proposition is a load-variable defining equation
/// (`v == load(snapshot, ptr)` for a reserved load variable). Such
/// equations are true by construction, so path wrapping treats them as
/// ambient truths rather than premises.
pub(crate) fn is_load_variable_defining_fact(proposition: &Proposition) -> bool {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = proposition
    else {
        return false;
    };
    matches!(
        (left.as_ref(), right.as_ref()),
        (
            Bitvector32Term::Variable(variable),
            Bitvector32Term::MemoryLoad(_, _, _)
        ) if is_load_variable(variable)
    )
}

/// One load variable's registry entry: the load it names, and what the
/// session has learned about it since.
#[derive(Clone)]
struct RegisteredLoad {
    /// The canonical snapshot, address and kind: the load itself.
    memory: SharedCMemory,
    pointer: Pointer,
    kind: LoadKind,
    /// The first-seen live origin, and the origin epoch it was recorded in.
    origin: SharedCMemory,
    epoch: u64,
    /// The widest access width any mint of this name asked for.
    bytes: u32,
}

thread_local! {
    // Latest complete pointer and wide-word reads, indexed by value and
    // function epoch. Observations never change the defining name.
    // Persistent roots keep session capture/restore from copying the table.
    static POINTER_READ_OBSERVATIONS: std::cell::RefCell<
        imbl::HashMap<(u64, Pointer), (SharedCMemory, Pointer)>,
    > = std::cell::RefCell::new(imbl::HashMap::new());
    static WIDE_LOAD_OBSERVATIONS: std::cell::RefCell<
        imbl::HashMap<(u64, Variable), (SharedCMemory, Pointer)>,
    > = std::cell::RefCell::new(imbl::HashMap::new());
    /// Separate pointer-valued load names. The defining key is one canonical
    /// snapshot and address at the fixed eight-byte pointer interpretation;
    /// neither a scalar load variable nor its mutable maximum access width
    /// decides membership in this registry.
    static POINTER_LOAD_REGISTRY: std::cell::RefCell<
        std::collections::HashMap<PointerLoadId, (SharedCMemory, Pointer)>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    /// Load variable -> the load it names (canonical memory, pointer, kind),
    /// its first-seen live origin and the origin epoch that origin was
    /// recorded in, and an access width in bytes.
    ///
    /// The kind is part of the name: two reads of one address in one snapshot
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
    /// whole session, but the live snapshot transport resolves through is
    /// first-seen within one verified function: the surface begins a new
    /// epoch per function, and the next mint in a new epoch replaces an
    /// origin recorded under an older one, which belongs to a DAG the
    /// current function's effect snapshots never connect to.
    static LOAD_ORIGIN_EPOCH: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static LOAD_VARIABLE_CACHE: std::cell::RefCell<
        std::collections::HashMap<Bitvector32Term, (Variable, Bitvector32Term)>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    static TERM_CACHE: std::cell::RefCell<
        std::collections::HashMap<Bitvector32Term, Bitvector32Term>,
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
    LOAD_VARIABLE_CACHE.with(|cache| cache.borrow_mut().clear());
    TERM_CACHE.with(|cache| cache.borrow_mut().clear());
}

/// Everything `clear_load_variable_registry` clears, as one value: the load
/// names, their origins, observations and widths, the pointer-load names, and the logical
/// pointer reads. A reusable session captures it once and restores it before
/// each check.
#[derive(Clone)]
pub(crate) struct LoadRegistryState {
    pointer_observations: imbl::HashMap<(u64, Pointer), (SharedCMemory, Pointer)>,
    wide_observations: imbl::HashMap<(u64, Variable), (SharedCMemory, Pointer)>,
    variables: std::collections::HashMap<Variable, RegisteredLoad>,
    pointers: std::collections::HashMap<PointerLoadId, (SharedCMemory, Pointer)>,
    widths: std::collections::HashMap<(SharedCMemory, Pointer), u32>,
    widths_at_address: std::collections::HashMap<Pointer, u32>,
    array_widths: std::collections::BTreeMap<(PointerBlock, i64), SymbolicArrayAccessWidths>,
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
        pointers: POINTER_LOAD_REGISTRY.with(|registry| registry.borrow().clone()),
        widths: LOAD_ACCESS_WIDTH.with(|widths| widths.borrow().clone()),
        widths_at_address: LOAD_ACCESS_WIDTH_AT_ADDRESS.with(|widths| widths.borrow().clone()),
        array_widths: SYMBOLIC_ARRAY_ACCESS_WIDTHS.with(|arrays| arrays.borrow().clone()),
        origin_epoch: LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get),
        logical_pointer_reads: crate::kernel::equality_graph::capture_logical_pointer_reads(),
    }
}

pub(crate) fn restore_load_variable_registry(state: &LoadRegistryState) {
    // A cached name is meaningful only beside the registry that defines it.
    // Derived term/name caches are not part of the captured registry state.
    clear_load_canonicalization_caches();
    POINTER_READ_OBSERVATIONS
        .with(|registry| *registry.borrow_mut() = state.pointer_observations.clone());
    WIDE_LOAD_OBSERVATIONS
        .with(|registry| *registry.borrow_mut() = state.wide_observations.clone());
    crate::kernel::equality_graph::restore_logical_pointer_reads(&state.logical_pointer_reads);
    LOAD_VARIABLE_REGISTRY.with(|registry| *registry.borrow_mut() = state.variables.clone());
    POINTER_LOAD_REGISTRY.with(|registry| *registry.borrow_mut() = state.pointers.clone());
    LOAD_ACCESS_WIDTH.with(|widths| *widths.borrow_mut() = state.widths.clone());
    LOAD_ACCESS_WIDTH_AT_ADDRESS
        .with(|widths| *widths.borrow_mut() = state.widths_at_address.clone());
    SYMBOLIC_ARRAY_ACCESS_WIDTHS.with(|arrays| *arrays.borrow_mut() = state.array_widths.clone());
    LOAD_ORIGIN_EPOCH.with(|epoch| epoch.set(state.origin_epoch));
}

pub(crate) fn clear_load_variable_registry() {
    clear_load_canonicalization_caches();
    POINTER_READ_OBSERVATIONS.with(|registry| registry.borrow_mut().clear());
    WIDE_LOAD_OBSERVATIONS.with(|registry| registry.borrow_mut().clear());
    crate::kernel::equality_graph::clear_logical_pointer_reads();
    LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow_mut().clear());
    POINTER_LOAD_REGISTRY.with(|registry| registry.borrow_mut().clear());
    // Access widths are scoped to the verification that observed them. A
    // `local:` address is spelled the same in the next function, so a width
    // left behind would answer for an unrelated cell there.
    LOAD_ACCESS_WIDTH.with(|widths| widths.borrow_mut().clear());
    LOAD_ACCESS_WIDTH_AT_ADDRESS.with(|widths| widths.borrow_mut().clear());
    SYMBOLIC_ARRAY_ACCESS_WIDTHS.with(|arrays| arrays.borrow_mut().clear());
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

/// The load represented by a load variable minted on this thread.
/// Reasoning uses this to consult the snapshot lazily: a load variable in
/// an equality query is viewed as its load exactly where a load term would
/// have triggered provenance evidence.
pub(crate) fn registered_load_for_variable(
    variable: &Variable,
) -> Option<(SharedCMemory, Pointer)> {
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        registry
            .borrow()
            .get(variable)
            .map(|load| (load.memory.clone(), load.pointer.clone()))
    })
}

/// The load term a load variable names, kind included: the right-hand side
/// of its defining equation.
pub(crate) fn registered_load_term_for_variable(variable: &Variable) -> Option<Bitvector32Term> {
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        registry.borrow().get(variable).map(|load| {
            Bitvector32Term::MemoryLoad(
                load.memory.clone(),
                Box::new(load.pointer.clone()),
                load.kind,
            )
        })
    })
}

/// The kind of read a load variable names.
pub(crate) fn registered_load_kind_for_variable(variable: &Variable) -> Option<LoadKind> {
    LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow().get(variable).map(|load| load.kind))
}

/// Intern an eight-byte pointer load by its assumption-free defining
/// snapshot and address. Hashing only chooses a candidate slot: a collision
/// probes until the full key matches or an unused slot is found.
pub(crate) fn pointer_load_identity(memory: &SharedCMemory, address: &Pointer) -> PointerLoadId {
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

/// Decode a pointer-load name without consulting scalar-load metadata.
pub(crate) fn registered_pointer_load(identity: PointerLoadId) -> Option<(SharedCMemory, Pointer)> {
    POINTER_LOAD_REGISTRY.with(|registry| registry.borrow().get(&identity).cloned())
}

thread_local! {
    /// `(snapshot, address)` -> how many bytes the C load there reads.
    ///
    /// A `MemoryLoad` term carries its own read's kind, but one address may
    /// be read at several widths, and a framing walk about the address has to
    /// cover all of them; without this a caller has to assume the widest
    /// scalar, and an `int32` load stops being separable from a store four
    /// bytes away. The entry is written by [`symbolic_load_value`], the one
    /// typed entry point every C load passes through, before any naming can
    /// happen.
    static LOAD_ACCESS_WIDTH: std::cell::RefCell<
        std::collections::HashMap<(SharedCMemory, Pointer), u32>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());

    /// `address` -> the widest C load seen at it, in any snapshot.
    ///
    /// How wide the access at an address is comes from the C type being
    /// loaded, which does not vary with the snapshot. The exact key above is
    /// still preferred, because it answers for one particular load; this one
    /// answers for a walk that reached the address through a snapshot no
    /// typed load was ever performed at, which is every framing walk that
    /// starts at a later snapshot than the load it is carrying.
    ///
    /// Widening on conflict, so a `char` view and a `long` view of one
    /// address answer with the `long`: over-stating a width can only shrink
    /// the separated set.
    static LOAD_ACCESS_WIDTH_AT_ADDRESS: std::cell::RefCell<
        std::collections::HashMap<Pointer, u32>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// The element widths a symbolic static array declared for all of its
/// elements at once, in place of one [`record_load_access_width`] per
/// element: see [`declare_symbolic_array_access_widths`].
#[derive(Clone)]
struct SymbolicArrayAccessWidths {
    /// The snapshot every element's load reads.
    source: SharedCMemory,
    /// The byte distance between elements.
    stride: i64,
    count: u32,
    /// The loads of one element: each one's byte offset within the element,
    /// ascending and below `stride`, and its width. A scalar array's element
    /// is one load at offset 0; an array of structs has one per field.
    loads: std::sync::Arc<[(i64, u32)]>,
}

impl SymbolicArrayAccessWidths {
    /// The byte just past the last element's last load's first byte, for an
    /// array based at `base`.
    fn end(&self, base: i64) -> i64 {
        base.saturating_add(
            i64::from(self.count)
                .saturating_sub(1)
                .saturating_mul(self.stride),
        )
        .saturating_add(self.loads.last().map_or(0, |(offset, _)| *offset))
        .saturating_add(1)
    }

    /// The width of the load at `offset` bytes past the array's base, when
    /// one of its elements' loads is there.
    fn width_at(&self, base: i64, offset: i64) -> Option<u32> {
        if offset < base || offset >= self.end(base) {
            return None;
        }
        let within = (offset - base) % self.stride;
        self.loads
            .binary_search_by_key(&within, |(offset, _)| *offset)
            .ok()
            .map(|position| self.loads[position].1)
    }
}

thread_local! {
    /// The symbolic static arrays whose element widths are declared rather
    /// than recorded one element at a time, by block and constant base
    /// offset. No two overlap, so a constant pointer is an element of at most
    /// the one based nearest below it. Every reader of the two width tables
    /// reads a declared element as the entry the per-element record would
    /// have made, so the answers are that record's. Cleared with the tables.
    static SYMBOLIC_ARRAY_ACCESS_WIDTHS: std::cell::RefCell<
        std::collections::BTreeMap<(PointerBlock, i64), SymbolicArrayAccessWidths>,
    > = const { std::cell::RefCell::new(std::collections::BTreeMap::new()) };
}

/// The declared array element spelled exactly `pointer` (a constant offset in
/// the array's block, as the element's own load spells it): the snapshot its
/// load reads, and its width.
fn declared_array_access_width(pointer: &Pointer) -> Option<(SharedCMemory, u32)> {
    let PointerOffsetTerm::Constant(offset) = pointer.offset else {
        return None;
    };
    SYMBOLIC_ARRAY_ACCESS_WIDTHS.with(|arrays| {
        let arrays = arrays.borrow();
        if arrays.is_empty() {
            return None;
        }
        let ((block, base), array) = arrays
            .range(..=(pointer.block.clone(), offset))
            .next_back()?;
        if *block != pointer.block {
            return None;
        }
        array
            .width_at(*base, offset)
            .map(|bytes| (array.source.clone(), bytes))
    })
}

/// The width the snapshot-keyed record at `(memory, pointer)` would hold for
/// a declared array element.
fn declared_exact_access_width(memory: &SharedCMemory, pointer: &Pointer) -> Option<u32> {
    declared_array_access_width(pointer)
        .filter(|(source, _)| source == memory)
        .map(|(_, bytes)| bytes)
}

/// Says that a load of `bytes` bytes happens at every element `base`,
/// `base + stride`, … of a `count`-element array in `source`, exactly as
/// [`symbolic_load_value`] of each element would have recorded it, in work
/// that does not depend on `count`. Only a constant base is declared, and
/// only where no other declared array overlaps the elements; `false`
/// declares nothing, and the caller records the elements one by one.
///
/// Declaring before any element is named keeps every name what it was: the
/// naming reads the width back through [`recorded_load_access_width`], which
/// answers with the declaration.
pub(in crate::kernel) fn declare_symbolic_array_access_widths(
    source: &SharedCMemory,
    base: &Pointer,
    stride: u32,
    count: u32,
    bytes: u32,
) -> bool {
    declare_symbolic_element_access_widths(source, base, stride, count, &[(0, bytes)])
}

/// [`declare_symbolic_array_access_widths`] for an array whose every
/// element is read by several loads, one per `(offset, bytes)` of `loads`
/// (ascending offsets within the element, each below `stride`): an array of
/// structs, whose fields are its elements' loads. `false` declares nothing,
/// as there.
pub(in crate::kernel) fn declare_symbolic_element_access_widths(
    source: &SharedCMemory,
    base: &Pointer,
    stride: u32,
    count: u32,
    loads: &[(u32, u32)],
) -> bool {
    let PointerOffsetTerm::Constant(offset) = base.offset else {
        return false;
    };
    if count == 0
        || stride == 0
        || loads.is_empty()
        || !loads.windows(2).all(|pair| pair[0].0 < pair[1].0)
        || loads.last().is_some_and(|(within, _)| *within >= stride)
    {
        return false;
    }
    let declared = SymbolicArrayAccessWidths {
        source: source.clone(),
        stride: i64::from(stride),
        count,
        loads: loads
            .iter()
            .map(|(within, bytes)| (i64::from(*within), *bytes))
            .collect(),
    };
    let end = declared.end(offset);
    SYMBOLIC_ARRAY_ACCESS_WIDTHS.with(|arrays| {
        let mut arrays = arrays.borrow_mut();
        let key = (base.block.clone(), offset);
        if let Some(held) = arrays.get(&key) {
            // The same array declared again, as every function entry does.
            return held.source == declared.source
                && held.stride == declared.stride
                && held.count == declared.count
                && held.loads == declared.loads;
        }
        let below = arrays
            .range(..&key)
            .next_back()
            .filter(|((block, _), _)| *block == base.block)
            .is_some_and(|((_, held_base), held)| held.end(*held_base) > offset);
        let above = arrays
            .range(&key..)
            .next()
            .filter(|((block, _), _)| *block == base.block)
            .is_some_and(|((_, held_base), _)| *held_base < end);
        if below || above {
            return false;
        }
        arrays.insert(key, declared);
        true
    })
}

/// Remembers that a load of `bytes` bytes happens at this address in this
/// snapshot. Widening on conflict: the entry has to cover every access that
/// resolves through it. A declared array element counts as already recorded
/// at its declared width.
fn record_load_access_width(memory: &CMemory, pointer: &Pointer, bytes: u32) {
    let key = (
        crate::kernel::intern_c_memory(memory.clone()),
        pointer.clone(),
    );
    let declared = declared_array_access_width(pointer);
    let declared_exact = declared
        .as_ref()
        .filter(|(source, _)| *source == key.0)
        .map(|(_, bytes)| *bytes);
    let declared_at_address = declared.map(|(_, bytes)| bytes);
    // A recorded width can only ever widen, and a name computed under the
    // narrower one is stale: the epoch walk a narrow access takes crosses
    // stores the wider one stops at, so it names the load at an older
    // snapshot. `LOAD_VARIABLE_CACHE` is keyed by the term alone — a term
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
                let mut known = declared_exact.unwrap_or(bytes);
                widen(&mut known);
                widths.insert(key, known);
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
                let mut known = declared_at_address.unwrap_or(bytes);
                widen(&mut known);
                widths.insert(pointer.clone(), known);
            }
        }
    });
    if widened {
        LOAD_VARIABLE_CACHE.with(|cache| cache.borrow_mut().clear());
    }
}

/// Preserve an existing typed observation when substitution changes its
/// snapshot or address. A kind alone supplies no width here: Bits32 also
/// encodes pointer words. Destination observations can only widen.
pub(crate) fn transport_load_access_width(
    source: &SharedCMemory,
    source_pointer: &Pointer,
    destination: &SharedCMemory,
    destination_pointer: &Pointer,
) {
    if source == destination && source_pointer == destination_pointer {
        return;
    }
    if let Some(bytes) = recorded_load_access_width(source, source_pointer) {
        let bytes = rewritten_address_access_width(destination, destination_pointer)
            .map_or(bytes, |known| bytes.max(known));
        record_load_access_width(destination, destination_pointer, bytes);
    }
}

/// Rewriters may retain `128 + 3 * 4` where a typed address producer folded
/// the same exact offset to `140`. Inspect that one checked constant spelling
/// too; symbolic equality never enters this lookup.
fn rewritten_address_access_width(memory: &SharedCMemory, pointer: &Pointer) -> Option<u32> {
    let known = |pointer: &Pointer| {
        recorded_load_access_width(memory, pointer)
            .into_iter()
            .chain(recorded_load_access_width_at_address(pointer))
            .max()
    };
    let original = known(pointer);
    if matches!(pointer.offset, PointerOffsetTerm::Constant(_)) {
        return original;
    }
    let constant = pointer.offset.as_const().and_then(|offset| {
        known(&Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Constant(offset),
        })
    });
    original.into_iter().chain(constant).max()
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
            .or_insert_with(|| {
                declared_array_access_width(pointer)
                    .map_or(bytes, |(_, declared)| declared.max(bytes))
            });
    });
}

/// The width of the C load recorded at this address in this snapshot, when
/// one was. `None` means no typed load was seen here, and the caller stands
/// in [`resource_tracker::widest_scalar_access_bytes`].
pub(crate) fn recorded_load_access_width(memory: &SharedCMemory, pointer: &Pointer) -> Option<u32> {
    LOAD_ACCESS_WIDTH
        .with(|widths| {
            widths
                .borrow()
                .get(&(memory.clone(), pointer.clone()))
                .copied()
        })
        .or_else(|| declared_exact_access_width(memory, pointer))
        .or_else(|| {
            // This snapshot saw no typed load here, but the address still has
            // a width if any snapshot did: the C type at an address does not
            // change with the snapshot a framing walk happens to start from.
            recorded_load_access_width_at_address(pointer)
        })
}

/// The widest C load recorded at this address in any snapshot, a declared
/// array element's included.
fn recorded_load_access_width_at_address(pointer: &Pointer) -> Option<u32> {
    LOAD_ACCESS_WIDTH_AT_ADDRESS
        .with(|widths| widths.borrow().get(pointer).copied())
        .or_else(|| declared_array_access_width(pointer).map(|(_, bytes)| bytes))
}

/// The access width to use for a load named only by a term.
pub(crate) fn load_access_width_or_widest(memory: &SharedCMemory, pointer: &Pointer) -> u32 {
    recorded_load_access_width(memory, pointer)
        .unwrap_or_else(crate::kernel::resource_tracker::widest_scalar_access_bytes)
}

/// The access width a framing walk uses for a `kind` read at this address:
/// the width recorded there, never narrower than the read itself.
pub(crate) fn load_term_access_width(
    memory: &SharedCMemory,
    pointer: &Pointer,
    kind: LoadKind,
) -> u32 {
    let observed = recorded_load_access_width(memory, pointer);
    observed
        .unwrap_or_else(|| kind.unrecorded_access_byte_width())
        .max(kind.byte_width())
}

/// The widest C load recorded at this address in any snapshot, or the widest
/// scalar when none was seen.
///
/// The snapshot-keyed form above is the precise one and is what a caller
/// holding an interned snapshot asks. This one is for a caller holding a bare
/// `CMemory` it would have to intern only to ask the question, where the C
/// type at the address is the whole answer anyway: every framing comparison
/// runs at a snapshot later than the load it is carrying, so the exact key
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
/// [`resource_tracker::widest_scalar_access_bytes`].
pub(crate) fn registered_load_bytes_for_variable(variable: &Variable) -> Option<u32> {
    LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow().get(variable).map(|load| load.bytes))
}

/// The first-seen live snapshot a load variable was minted from in the
/// current origin epoch. The canonical form is a jumped placeholder unsuited
/// to frame checks; transport resolves through this origin, which is
/// DAG-connected and cell-comparable to later effect snapshots of the
/// function that minted it. First-seen is deterministic because mint order
/// is execution order; per-epoch because two functions in one session can
/// mint the same variable from unconnected snapshots.
pub(crate) fn registered_load_origin_for_variable(
    variable: &Variable,
) -> Option<(SharedCMemory, Pointer)> {
    let current_epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        registry
            .borrow()
            .get(variable)
            // An origin recorded under an earlier epoch belongs to another
            // function's DAG; it can relate nothing this function executes.
            .filter(|load| load.epoch == current_epoch)
            .map(|load| (load.origin.clone(), load.pointer.clone()))
    })
}

/// [`registered_load_origin_for_variable`] as the load term it names there:
/// the same read, kind included, at the live origin.
pub(crate) fn registered_load_origin_term_for_variable(
    variable: &Variable,
) -> Option<Bitvector32Term> {
    let (origin, pointer) = registered_load_origin_for_variable(variable)?;
    let kind = registered_load_kind_for_variable(variable)?;
    Some(Bitvector32Term::MemoryLoad(origin, Box::new(pointer), kind))
}

/// Whether the pointer a load variable names was obtained before `block`
/// existed, so cannot point into it: a pointer value read at a snapshot
/// cannot hold the address of an object that snapshot does not have.
///
/// The reference is the load's live origin, the state it was first read in,
/// never its canonical memory, which may be a projection that leaves
/// unrelated blocks out. Only local blocks are judged: a local exists from
/// the step that declares it into the snapshot, so a local the origin does
/// not hold, and has not ended, was declared after the read. Heap blocks
/// are not judged, because a heap identity can come from a contract's
/// allocation claim rather than from a snapshot's own blocks.
pub(crate) fn loaded_pointer_predates_block(variable: &Variable, block: &PointerBlock) -> bool {
    if !block.starts_with("local:") {
        return false;
    }
    let Some((origin, _)) = registered_load_origin_for_variable(variable) else {
        return false;
    };
    !origin.has_block(block) && !origin.forgotten.ended_local_blocks.contains(block)
}

/// Views a term as a memory load for equality reasoning: load terms pass
/// through, and registered load variables resolve to the loads they
/// represent. Other terms are not loads.
pub(crate) fn viewed_as_memory_load(term: &Bitvector32Term) -> Option<Bitvector32Term> {
    match term {
        Bitvector32Term::MemoryLoad(_, _, _) => Some(term.clone()),
        Bitvector32Term::Variable(variable) => registered_load_term_for_variable(variable),
        _ => None,
    }
}

/// Whether a proposition mentions any registered load variable.
/// Cross-effect fact transport uses this to include facts written with load
/// variables in rewriting, exactly as load-term facts are included by
/// mentioning their snapshots.
pub(crate) fn proposition_mentions_registered_load_variable(proposition: &Proposition) -> bool {
    let mut variables = std::collections::BTreeSet::new();
    crate::kernel::reasoning::variable_collection::collect_proposition_bitvector_variables(
        proposition,
        &mut variables,
    );
    variables.iter().any(|variable| {
        is_load_variable(variable) && registered_load_for_variable(variable).is_some()
    })
}

/// The single canonical form for a term: the deep, assumption-free
/// structural canonicalization ([`canonicalize_atomic_loads`]) followed by
/// load-variable substitution, so every remaining load becomes its load
/// variable. The load variable is the canonical form of its load — a
/// consumer never expands a load variable back into its snapshot-bearing
/// load; the registered defining fact is the only bridge. Equality of
/// canonical forms holds by definition: it needs no proof evidence.
/// Deterministic and idempotent. The traversal is linear and uses explicit
/// worklists. Shallow terms are memoized; deep terms bypass the recursive
/// structural key and take the same complete path directly.
///
/// [`canonicalize_atomic_loads`]: crate::kernel::memory_provenance::canonicalize_atomic_loads
pub(crate) fn canonical_term(term: &Bitvector32Term) -> Bitvector32Term {
    let cacheable = crate::kernel::memory_provenance::term_is_shallow_structural_cache_key(term);
    if cacheable && let Some(hit) = TERM_CACHE.with(|cache| cache.borrow().get(term).cloned()) {
        return hit;
    }
    let structural = crate::kernel::memory_provenance::canonicalize_atomic_loads(term);
    // Register the live observation before its projected form can claim the
    // load's origin. Keep the established projected canonical identity.
    if matches!(term, Bitvector32Term::MemoryLoad(..))
        && matches!(structural, Bitvector32Term::MemoryLoad(..))
    {
        load_variable_for_term(term);
    }
    let result = substitute_load_variables(&structural, &mut None);
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

/// The canonical form for a pointer offset: every scaled index takes its
/// [`canonical_term`] form. The offset analogue of [`canonical_term`].
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
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    results.push(PointerOffsetTerm::scale_int32(
                        canonical_term(value),
                        *byte_width,
                    ));
                }
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => results.push(PointerOffsetTerm::scale_int64(
                    canonical_term(value),
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

/// Gives an index or endpoint term the model's stable representation before
/// it enters pointer-offset or range arithmetic: every load atom is replaced
/// by its load variable and each variable's defining equation joins
/// the fact stream. Every producer that scales an integer term into an
/// offset or evaluates a range endpoint must route the term through this,
/// so a loaded index never enters a `PointerOffsetTerm` or a range bound as
/// a raw `MemoryLoad`. Adoption is atomic across producers: naming one
/// birth site while another emits load terms splits one load identity into
/// two terms that only a proved equality could reconnect.
pub(crate) fn canonicalized_offset_index_term(
    bits: Bitvector32Term,
    facts: &mut ExecutionFacts,
) -> Bitvector32Term {
    if !term_mentions_a_memory_load(&bits) {
        return bits;
    }
    substitute_load_variables(&bits, &mut Some(facts))
}

/// The term for reading `pointer` from `memory` at a creation point with no
/// fact stream (resource materialization, contract evaluation): the load
/// variable. Load variables are content-addressed, so this agrees with
/// every other creation point; the defining fact is available through the
/// registry.
pub(crate) fn canonical_form_of_load(
    memory: SharedCMemory,
    pointer: Pointer,
    kind: LoadKind,
) -> Bitvector32Term {
    let load = Bitvector32Term::MemoryLoad(memory, Box::new(pointer), kind);
    match load_variable_for_term(&load) {
        Some((variable, _)) => Bitvector32Term::Variable(variable),
        None => load,
    }
}

/// Name a typed cell's own source read at its complete storage width.
/// In particular, a pointer cell's Bits32 proxy is an eight-byte read;
/// recording that fact precedes minting its immutable defining name.
pub(crate) fn canonical_form_of_typed_load(
    memory: SharedCMemory,
    pointer: Pointer,
    value_type: CType,
) -> Option<Bitvector32Term> {
    let kind = LoadKind::of_type(value_type)?;
    record_load_access_width(&memory, &pointer, value_type.byte_width());
    Some(canonical_form_of_load(memory, pointer, kind))
}

/// Name the four-byte word selected by checked uint32 representation metadata.
/// The caller validates that declaration before this helper records its width;
/// a bare Bits32 load retains its conservative pointer-compatible footprint.
pub(in crate::kernel) fn canonical_declared_uint32_word(
    memory: &CMemory,
    object: &Pointer,
) -> Bitvector32Term {
    record_load_access_width(memory, object, 4);
    canonical_form_of_load(
        crate::kernel::intern_c_memory_ref(memory),
        object.clone(),
        LoadKind::Bits32,
    )
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
fn is_store_fact(condition: &ConditionTerm, value: bool) -> bool {
    if !value {
        return false;
    }
    let ConditionTerm::Bitvector32Equal(left, right) = condition else {
        return false;
    };
    let (load, stored) = match (left.as_ref(), right.as_ref()) {
        (Bitvector32Term::MemoryLoad(memory, pointer, kind), stored)
        | (stored, Bitvector32Term::MemoryLoad(memory, pointer, kind)) => {
            ((memory, pointer, kind), stored)
        }
        _ => return false,
    };
    let Some(value) = load.0.known_value(load.1) else {
        return false;
    };
    load.2.reads_value(&value)
        && matches!(
            value,
            crate::kernel::integer32_c_value!(recorded)
                if &recorded == stored
        )
}

/// The canonical form for a condition: every operand takes its
/// [`canonical_term`] form, so terms that are equal by definition compare
/// identically. The comparison direction of the canonical model for
/// whole facts.
pub(crate) fn canonical_condition(condition: &ConditionTerm) -> ConditionTerm {
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        (
            Box::new(canonical_term(left)),
            Box::new(canonical_term(right)),
        )
    };
    match condition {
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => condition.clone(),
        ConditionTerm::AlgebraicEqual(_, _) => condition.clone(),
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedLessThan(left, right)
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedLessEqual(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        }
        ConditionTerm::Bitvector32Equal(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32Equal(left, right)
        }
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        }
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        }
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        }
        ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
        }
        ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right)
        }
        ConditionTerm::Bitvector64SignedLessThan(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector64SignedLessThan(left, right)
        }
        ConditionTerm::Bitvector64SignedLessEqual(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector64SignedLessEqual(left, right)
        }
        ConditionTerm::Bitvector64SignedGreaterThan(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector64SignedGreaterThan(left, right)
        }
        ConditionTerm::Bitvector64SignedGreaterEqual(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
        }
        ConditionTerm::Bitvector64UnsignedLessThan(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector64UnsignedLessThan(left, right)
        }
        ConditionTerm::Bitvector64UnsignedLessEqual(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector64UnsignedLessEqual(left, right)
        }
        ConditionTerm::Bitvector64UnsignedGreaterThan(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector64UnsignedGreaterThan(left, right)
        }
        ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right)
        }
        ConditionTerm::Bitvector64Equal(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector64Equal(left, right)
        }
        ConditionTerm::Bitvector64SignedAddOverflows(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector64SignedAddOverflows(left, right)
        }
        ConditionTerm::Bitvector64SignedSubtractOverflows(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector64SignedSubtractOverflows(left, right)
        }
        ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right)
        }
        ConditionTerm::Bitvector64SignedDivideOverflows(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector64SignedDivideOverflows(left, right)
        }
        ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right)
        }
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

/// Replaces every load atom in a term with its load variable.
/// When `facts` carries a stream, this is the production mode: each
/// substituted load variable's defining fact joins the stream,
/// deduplicated, so the variable always travels with its defining fact. Binder scopes
/// (`RangeFold` bodies) are left untouched: a load under a fold can mention
/// bound variables, which name no load identity.
fn substitute_load_variables(
    term: &Bitvector32Term,
    facts: &mut Option<&mut ExecutionFacts>,
) -> Bitvector32Term {
    type BinaryConstructor = fn(Box<Bitvector32Term>, Box<Bitvector32Term>) -> Bitvector32Term;
    type UnaryConstructor = fn(Box<Bitvector32Term>) -> Bitvector32Term;
    type ConditionConstructor = fn(Box<Bitvector32Term>, Box<Bitvector32Term>) -> ConditionTerm;

    enum Task<'a> {
        VisitTerm(&'a Bitvector32Term),
        VisitCondition(&'a ConditionTerm),
        VisitOffset(&'a PointerOffsetTerm),
        RebuildBinary(BinaryConstructor),
        RebuildUnary(UnaryConstructor),
        RebuildMachineCast(MachineIntegerType, MachineIntegerType),
        RebuildFloatUnary(bool),
        RebuildFloatBinary {
            is_float64: bool,
            operator: CFloatBinaryOperator,
        },
        RebuildIf,
        RebuildPureFunction {
            name: String,
            argument_count: usize,
        },
        RebuildConditionBinary(ConditionConstructor),
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
    }

    macro_rules! visit_binary {
        ($constructor:path, $left:expr, $right:expr, $tasks:expr) => {{
            $tasks.push(Task::RebuildBinary($constructor));
            $tasks.push(Task::VisitTerm($right));
            $tasks.push(Task::VisitTerm($left));
        }};
    }
    macro_rules! visit_unary {
        ($constructor:path, $value:expr, $tasks:expr) => {{
            $tasks.push(Task::RebuildUnary($constructor));
            $tasks.push(Task::VisitTerm($value));
        }};
    }
    macro_rules! visit_condition_binary {
        ($constructor:path, $left:expr, $right:expr, $tasks:expr) => {{
            $tasks.push(Task::RebuildConditionBinary($constructor));
            $tasks.push(Task::VisitTerm($right));
            $tasks.push(Task::VisitTerm($left));
        }};
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
                    Bitvector32Term::MachineIntegerCast {
                        value,
                        source,
                        destination,
                    } => {
                        tasks.push(Task::RebuildMachineCast(*source, *destination));
                        tasks.push(Task::VisitTerm(value));
                    }

                    Bitvector32Term::Constant(_)
                    | Bitvector32Term::Variable(_)
                    | Bitvector32Term::Int64Constant(_)
                    | Bitvector32Term::UInt64Constant(_)
                    | Bitvector32Term::MachineIntegerConstant(_) => term_results.push(term.clone()),
                    Bitvector32Term::MemoryLoad(_, _, _) => match load_variable_for_term(term) {
                        Some((variable, load)) => {
                            if let Some(facts) = facts.as_deref_mut() {
                                record_load_variable_defining_fact(variable, load, facts);
                            }
                            term_results.push(Bitvector32Term::Variable(variable));
                        }
                        None => term_results.push(term.clone()),
                    },
                    Bitvector32Term::PointerAddress(_)
                    | Bitvector32Term::IntegerToMachine { .. } => term_results.push(term.clone()),
                    Bitvector32Term::ClickFunctionApplication { .. }
                    | Bitvector32Term::AlgebraicMatch { .. } => term_results.push(term.clone()),
                    Bitvector32Term::Add(left, right) => {
                        visit_binary!(Bitvector32Term::Add, left, right, tasks)
                    }
                    Bitvector32Term::Subtract(left, right) => {
                        visit_binary!(Bitvector32Term::Subtract, left, right, tasks)
                    }
                    Bitvector32Term::Multiply(left, right) => {
                        visit_binary!(Bitvector32Term::Multiply, left, right, tasks)
                    }
                    Bitvector32Term::Divide(left, right) => {
                        visit_binary!(Bitvector32Term::Divide, left, right, tasks)
                    }
                    Bitvector32Term::UnsignedDivide(left, right) => {
                        visit_binary!(Bitvector32Term::UnsignedDivide, left, right, tasks)
                    }
                    Bitvector32Term::Remainder(left, right) => {
                        visit_binary!(Bitvector32Term::Remainder, left, right, tasks)
                    }
                    Bitvector32Term::UnsignedRemainder(left, right) => {
                        visit_binary!(Bitvector32Term::UnsignedRemainder, left, right, tasks)
                    }
                    Bitvector32Term::ShiftLeft(left, right) => {
                        visit_binary!(Bitvector32Term::ShiftLeft, left, right, tasks)
                    }
                    Bitvector32Term::ArithmeticShiftRight(left, right) => {
                        visit_binary!(Bitvector32Term::ArithmeticShiftRight, left, right, tasks)
                    }
                    Bitvector32Term::LogicalShiftRight(left, right) => {
                        visit_binary!(Bitvector32Term::LogicalShiftRight, left, right, tasks)
                    }
                    Bitvector32Term::BitwiseAnd(left, right) => {
                        visit_binary!(Bitvector32Term::BitwiseAnd, left, right, tasks)
                    }
                    Bitvector32Term::BitwiseOr(left, right) => {
                        visit_binary!(Bitvector32Term::BitwiseOr, left, right, tasks)
                    }
                    Bitvector32Term::BitwiseXor(left, right) => {
                        visit_binary!(Bitvector32Term::BitwiseXor, left, right, tasks)
                    }
                    Bitvector32Term::BitwiseNot(value) => {
                        visit_unary!(Bitvector32Term::BitwiseNot, value, tasks)
                    }
                    Bitvector32Term::Float32Negate(value) => {
                        tasks.push(Task::RebuildFloatUnary(false));
                        tasks.push(Task::VisitTerm(value));
                    }
                    Bitvector32Term::Float64Negate(value) => {
                        tasks.push(Task::RebuildFloatUnary(true));
                        tasks.push(Task::VisitTerm(value));
                    }
                    Bitvector32Term::Float32Binary {
                        operator,
                        left,
                        right,
                    } => {
                        tasks.push(Task::RebuildFloatBinary {
                            is_float64: false,
                            operator: *operator,
                        });
                        tasks.push(Task::VisitTerm(right));
                        tasks.push(Task::VisitTerm(left));
                    }
                    Bitvector32Term::Float64Binary {
                        operator,
                        left,
                        right,
                    } => {
                        tasks.push(Task::RebuildFloatBinary {
                            is_float64: true,
                            operator: *operator,
                        });
                        tasks.push(Task::VisitTerm(right));
                        tasks.push(Task::VisitTerm(left));
                    }
                    Bitvector32Term::Int64From32(value) => {
                        visit_unary!(Bitvector32Term::Int64From32, value, tasks)
                    }
                    Bitvector32Term::Int64FromUInt32(value) => {
                        visit_unary!(Bitvector32Term::Int64FromUInt32, value, tasks)
                    }
                    Bitvector32Term::UInt64From32(value) => {
                        visit_unary!(Bitvector32Term::UInt64From32, value, tasks)
                    }
                    Bitvector32Term::UInt32From64(value) => {
                        visit_unary!(Bitvector32Term::UInt32From64, value, tasks)
                    }
                    Bitvector32Term::UInt64FromInt32(value) => {
                        visit_unary!(Bitvector32Term::UInt64FromInt32, value, tasks)
                    }
                    Bitvector32Term::UInt64FromInt64(value) => {
                        visit_unary!(Bitvector32Term::UInt64FromInt64, value, tasks)
                    }
                    Bitvector32Term::Int64BitwiseNot(value) => {
                        visit_unary!(Bitvector32Term::Int64BitwiseNot, value, tasks)
                    }
                    Bitvector32Term::UInt64BitwiseNot(value) => {
                        visit_unary!(Bitvector32Term::UInt64BitwiseNot, value, tasks)
                    }
                    Bitvector32Term::Int64Add(left, right) => {
                        visit_binary!(Bitvector32Term::Int64Add, left, right, tasks)
                    }
                    Bitvector32Term::Int64Subtract(left, right) => {
                        visit_binary!(Bitvector32Term::Int64Subtract, left, right, tasks)
                    }
                    Bitvector32Term::Int64Multiply(left, right) => {
                        visit_binary!(Bitvector32Term::Int64Multiply, left, right, tasks)
                    }
                    Bitvector32Term::Int64Divide(left, right) => {
                        visit_binary!(Bitvector32Term::Int64Divide, left, right, tasks)
                    }
                    Bitvector32Term::Int64Remainder(left, right) => {
                        visit_binary!(Bitvector32Term::Int64Remainder, left, right, tasks)
                    }
                    Bitvector32Term::Int64ShiftLeft(left, right) => {
                        visit_binary!(Bitvector32Term::Int64ShiftLeft, left, right, tasks)
                    }
                    Bitvector32Term::Int64ArithmeticShiftRight(left, right) => visit_binary!(
                        Bitvector32Term::Int64ArithmeticShiftRight,
                        left,
                        right,
                        tasks
                    ),
                    Bitvector32Term::Int64BitwiseAnd(left, right) => {
                        visit_binary!(Bitvector32Term::Int64BitwiseAnd, left, right, tasks)
                    }
                    Bitvector32Term::Int64BitwiseOr(left, right) => {
                        visit_binary!(Bitvector32Term::Int64BitwiseOr, left, right, tasks)
                    }
                    Bitvector32Term::Int64BitwiseXor(left, right) => {
                        visit_binary!(Bitvector32Term::Int64BitwiseXor, left, right, tasks)
                    }
                    Bitvector32Term::UInt64Add(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64Add, left, right, tasks)
                    }
                    Bitvector32Term::UInt64Subtract(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64Subtract, left, right, tasks)
                    }
                    Bitvector32Term::UInt64Multiply(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64Multiply, left, right, tasks)
                    }
                    Bitvector32Term::UInt64Divide(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64Divide, left, right, tasks)
                    }
                    Bitvector32Term::UInt64Remainder(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64Remainder, left, right, tasks)
                    }
                    Bitvector32Term::UInt64ShiftLeft(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64ShiftLeft, left, right, tasks)
                    }
                    Bitvector32Term::UInt64LogicalShiftRight(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64LogicalShiftRight, left, right, tasks)
                    }
                    Bitvector32Term::UInt64BitwiseAnd(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64BitwiseAnd, left, right, tasks)
                    }
                    Bitvector32Term::UInt64BitwiseOr(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64BitwiseOr, left, right, tasks)
                    }
                    Bitvector32Term::UInt64BitwiseXor(left, right) => {
                        visit_binary!(Bitvector32Term::UInt64BitwiseXor, left, right, tasks)
                    }
                    Bitvector32Term::If {
                        condition,
                        then_term,
                        else_term,
                    } => {
                        tasks.push(Task::RebuildIf);
                        tasks.push(Task::VisitTerm(else_term));
                        tasks.push(Task::VisitTerm(then_term));
                        tasks.push(Task::VisitCondition(condition));
                    }
                    // A fold is a binder boundary: loads in its body can mention
                    // bound variables and therefore do not have a global load
                    // identity. Preserve the whole scoped term verbatim.
                    Bitvector32Term::RangeFold { .. } => term_results.push(term.clone()),
                    Bitvector32Term::PureFunctionApplication { name, arguments } => {
                        tasks.push(Task::RebuildPureFunction {
                            name: name.clone(),
                            argument_count: arguments.len(),
                        });
                        for argument in arguments.iter().rev() {
                            tasks.push(Task::VisitTerm(argument));
                        }
                    }
                }
            }
            Task::VisitCondition(condition) => match condition {
                ConditionTerm::AlgebraicEqual(_, _) => condition_results.push(condition.clone()),
                crate::kernel::integer_comparison_condition!(_, _) => {
                    condition_results.push(condition.clone())
                }
                ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {
                    condition_results.push(condition.clone())
                }
                ConditionTerm::Bitvector32SignedLessThan(left, right) => visit_condition_binary!(
                    ConditionTerm::Bitvector32SignedLessThan,
                    left,
                    right,
                    tasks
                ),
                ConditionTerm::Bitvector32SignedLessEqual(left, right) => visit_condition_binary!(
                    ConditionTerm::Bitvector32SignedLessEqual,
                    left,
                    right,
                    tasks
                ),
                ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector32SignedGreaterThan,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector32SignedGreaterEqual,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector32Equal(left, right) => {
                    visit_condition_binary!(ConditionTerm::Bitvector32Equal, left, right, tasks)
                }
                ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector32SignedAddOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector32SignedSubtractOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector32SignedMultiplyOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector32SignedDivideOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector32SignedShiftLeftOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64SignedLessThan(left, right) => visit_condition_binary!(
                    ConditionTerm::Bitvector64SignedLessThan,
                    left,
                    right,
                    tasks
                ),
                ConditionTerm::Bitvector64SignedLessEqual(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedLessEqual,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64SignedGreaterThan(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedGreaterThan,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64SignedGreaterEqual(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedGreaterEqual,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64UnsignedLessThan(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64UnsignedLessThan,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64UnsignedLessEqual(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64UnsignedLessEqual,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64UnsignedGreaterThan(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64UnsignedGreaterThan,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64UnsignedGreaterEqual,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64Equal(left, right) => {
                    visit_condition_binary!(ConditionTerm::Bitvector64Equal, left, right, tasks)
                }
                ConditionTerm::Bitvector64SignedAddOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedAddOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64SignedSubtractOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedSubtractOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedMultiplyOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64SignedDivideOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedDivideOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
                    visit_condition_binary!(
                        ConditionTerm::Bitvector64SignedShiftLeftOverflows,
                        left,
                        right,
                        tasks
                    )
                }
                ConditionTerm::Float32(float_condition) => {
                    let term_count = match float_condition {
                        CFloatCondition::Comparison { .. } => 2,
                        CFloatCondition::Classification { .. } => 1,
                    };
                    tasks.push(Task::RebuildFloatCondition {
                        is_float64: false,
                        condition: float_condition.clone(),
                        term_count,
                    });
                    match float_condition {
                        CFloatCondition::Comparison { left, right, .. } => {
                            tasks.push(Task::VisitTerm(right));
                            tasks.push(Task::VisitTerm(left));
                        }
                        CFloatCondition::Classification { value, .. } => {
                            tasks.push(Task::VisitTerm(value));
                        }
                    }
                }
                ConditionTerm::Float64(float_condition) => {
                    let term_count = match float_condition {
                        CFloatCondition::Comparison { .. } => 2,
                        CFloatCondition::Classification { .. } => 1,
                    };
                    tasks.push(Task::RebuildFloatCondition {
                        is_float64: true,
                        condition: float_condition.clone(),
                        term_count,
                    });
                    match float_condition {
                        CFloatCondition::Comparison { left, right, .. } => {
                            tasks.push(Task::VisitTerm(right));
                            tasks.push(Task::VisitTerm(left));
                        }
                        CFloatCondition::Classification { value, .. } => {
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
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    tasks.push(Task::RebuildInt32Scaled(*byte_width));
                    tasks.push(Task::VisitTerm(value));
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
                    tasks.push(Task::VisitTerm(value));
                }
            },
            Task::RebuildBinary(constructor) => {
                let right = term_results.pop().expect("visited right term");
                let left = term_results.pop().expect("visited left term");
                term_results.push(constructor(Box::new(left), Box::new(right)));
            }
            Task::RebuildMachineCast(source, destination) => {
                let value = term_results.pop().expect("visited machine cast operand");
                term_results.push(Bitvector32Term::machine_integer_cast(
                    source,
                    destination,
                    value,
                ));
            }
            Task::RebuildUnary(constructor) => {
                let value = term_results.pop().expect("visited unary term");
                term_results.push(constructor(Box::new(value)));
            }
            Task::RebuildFloatUnary(is_float64) => {
                let value = term_results.pop().expect("visited float unary term");
                term_results.push(if is_float64 {
                    Bitvector32Term::float64_negate(value)
                } else {
                    Bitvector32Term::float32_negate(value)
                });
            }
            Task::RebuildFloatBinary {
                is_float64,
                operator,
            } => {
                let right = term_results.pop().expect("visited right float term");
                let left = term_results.pop().expect("visited left float term");
                term_results.push(if is_float64 {
                    Bitvector32Term::float64_binary(left, right, operator)
                } else {
                    Bitvector32Term::float32_binary(left, right, operator)
                });
            }
            Task::RebuildIf => {
                let else_term = term_results.pop().expect("visited else term");
                let then_term = term_results.pop().expect("visited then term");
                let condition = condition_results.pop().expect("visited condition");
                term_results.push(Bitvector32Term::If {
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
                term_results.push(Bitvector32Term::PureFunctionApplication { name, arguments });
            }
            Task::RebuildConditionBinary(constructor) => {
                let right = term_results.pop().expect("visited right condition operand");
                let left = term_results.pop().expect("visited left condition operand");
                condition_results.push(constructor(Box::new(left), Box::new(right)));
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
pub(crate) fn terms_have_same_canonical_form(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> bool {
    if left == right {
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
fn term_mentions_a_memory_load(term: &Bitvector32Term) -> bool {
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Variable(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_) => false,
        Bitvector32Term::MemoryLoad(_, _, _) => true,
        Bitvector32Term::PointerAddress(pointer) => pointer
            .offset
            .scaled_values()
            .into_iter()
            .any(term_mentions_a_memory_load),
        crate::kernel::binary_bitvector32_term!(left, right) => {
            term_mentions_a_memory_load(left) || term_mentions_a_memory_load(right)
        }
        Bitvector32Term::Float32Binary { left, right, .. }
        | Bitvector32Term::Float64Binary { left, right, .. } => {
            term_mentions_a_memory_load(left) || term_mentions_a_memory_load(right)
        }
        Bitvector32Term::Int64From32(value)
        | Bitvector32Term::MachineIntegerCast { value, .. }
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::UInt32From64(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value)
        | Bitvector32Term::Int64BitwiseNot(value)
        | Bitvector32Term::UInt64BitwiseNot(value) => term_mentions_a_memory_load(value),
        crate::kernel::binary_wide_term!(left, right) => {
            term_mentions_a_memory_load(left) || term_mentions_a_memory_load(right)
        }
        Bitvector32Term::BitwiseNot(value)
        | Bitvector32Term::Float32Negate(value)
        | Bitvector32Term::Float64Negate(value) => term_mentions_a_memory_load(value),
        Bitvector32Term::If {
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
        Bitvector32Term::RangeFold { .. } => true,
        Bitvector32Term::PureFunctionApplication { name: _, arguments } => {
            arguments.iter().any(term_mentions_a_memory_load)
        }
        Bitvector32Term::ClickFunctionApplication { .. } => true,
        Bitvector32Term::AlgebraicMatch { arms, .. } => arms
            .iter()
            .any(|arm| term_mentions_a_memory_load(&arm.body)),
        Bitvector32Term::IntegerToMachine { .. } => true,
    }
}

fn condition_mentions_a_memory_load(condition: &ConditionTerm) -> bool {
    match condition {
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
    }
}

fn offset_mentions_a_memory_load(offset: &PointerOffsetTerm) -> bool {
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => false,
        PointerOffsetTerm::Add(left, right) => {
            offset_mentions_a_memory_load(left) || offset_mentions_a_memory_load(right)
        }
        PointerOffsetTerm::Int32Scaled { value, .. }
        | PointerOffsetTerm::Int64Scaled { value, .. } => term_mentions_a_memory_load(value),
    }
}

/// The load variable representing one load identity: the pair of a memory
/// snapshot (by content) and a loaded pointer. Hashing that identity into a
/// reserved id space picks where the search for its id starts, and the
/// thread-local registry assigns the first slot that holds this identity or
/// nothing, so distinct identities get distinct ids by construction. Every
/// pass — contract-grant lowering, requirement evaluation, and body
/// execution — therefore writes the same load with the same variable, and
/// the id is the hash itself unless another load already took that slot in
/// this session. The registry is never cleared within a session, and
/// exhausting its capacity is a loud failure rather than a silent reset.
/// The variable naming a `kind` load of `pointer` in `memory`. The epoch
/// walk that picks the snapshot it is named at is as wide as the widest
/// access recorded at the address, and never narrower than the read.
pub(crate) fn load_variable_for_cell(
    memory: &SharedCMemory,
    pointer: &Pointer,
    kind: LoadKind,
) -> Variable {
    load_variable_for_cell_with_origin(
        memory,
        pointer,
        kind,
        recorded_load_access_width(memory, pointer)
            .unwrap_or_else(|| kind.unrecorded_access_byte_width())
            .max(kind.byte_width()),
        memory,
    )
}

/// Mint the load identity for exactly this snapshot and pointer.
///
/// Fold substitution uses this after rewriting a registered load's address.
/// The ordinary cell helper first projects a snapshot through memory
/// provenance, which is correct for a newly observed load but would change
/// the snapshot identity carried by an existing defining fact.  Keeping this
/// narrow helper separate makes the selected snapshot explicit and avoids
/// traversing or rewriting any of its contents.
/// The supplied width is an existing storage observation, even when the
/// value uses a wider bitvector container. Preserve it and widen only for an
/// authenticated destination observation.
pub(crate) fn load_variable_for_exact_cell(
    memory: &SharedCMemory,
    pointer: &Pointer,
    kind: LoadKind,
    bytes: u32,
) -> Variable {
    let bytes =
        rewritten_address_access_width(memory, pointer).map_or(bytes, |known| bytes.max(known));
    record_load_access_width(memory, pointer, bytes);
    mint_load_variable_identity(memory, pointer, kind, memory, bytes)
}

/// The variable naming a `kind` load of `pointer` in `memory`.
///
/// `bytes` is the access width the epoch walk uses, and it decides how far
/// back the walk may go: a store lands on this load exactly when it writes
/// one of these bytes. It is never narrower than the read itself.
pub(crate) fn load_variable_for_cell_with_origin(
    memory: &SharedCMemory,
    pointer: &Pointer,
    kind: LoadKind,
    bytes: u32,
    origin: &SharedCMemory,
) -> Variable {
    let bytes = bytes.max(kind.byte_width());
    // Derive the variable from the cell's DAG epoch when one is recorded:
    // snapshots that differ only by effects provably disjoint from this
    // cell then share the variable, so bookkeeping drift and unrelated
    // stores do not mint new identities for one load.
    let epoch = crate::kernel::resource_tracker::last_same_point(
        crate::kernel::resource_tracker::Resource::Cell { pointer, bytes },
        &crate::kernel::resource_tracker::ProgramPoint::at(memory),
    )
    .map(|point| point.snapshot().clone());
    let memory = epoch.as_ref().unwrap_or(memory);
    mint_load_variable_identity(memory, pointer, kind, origin, bytes)
}

/// The kind is part of the identity: two reads of one address in one
/// snapshot that differ in kind are two values. The hash leaves it out, so a
/// load keeps the slot it had when every load of its address agreed on one
/// kind, and a second kind probes past it like any other collision.
fn mint_load_variable_identity(
    memory: &SharedCMemory,
    pointer: &Pointer,
    kind: LoadKind,
    origin: &SharedCMemory,
    bytes: u32,
) -> Variable {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    memory.hash(&mut hasher);
    pointer.hash(&mut hasher);
    let hash = hasher.finish();
    let range = load_variable_range();
    let current_epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
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
                    origin: known_origin,
                    epoch: known_epoch,
                    bytes: known_bytes,
                }) if known_memory == memory && known_pointer == pointer && *known_kind == kind => {
                    // One entry stands for every access that resolved to this
                    // name, so its width has to cover all of them: a caller
                    // that reads the width back is asking how many bytes this
                    // name could depend on.
                    *known_bytes = (*known_bytes).max(bytes);
                    // An origin from an earlier epoch was minted by another
                    // function; this function's first mint is its origin.
                    if *known_epoch != current_epoch {
                        *known_origin = origin.clone();
                        *known_epoch = current_epoch;
                    }
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
                            memory: memory.clone(),
                            pointer: pointer.clone(),
                            kind,
                            origin: origin.clone(),
                            epoch: current_epoch,
                            bytes,
                        },
                    );
                    return variable;
                }
            }
        }
    })
}

/// Reuse an exact read name or a materialized pointer cell's retained name.
/// This lookup never canonicalizes a new read or walks its memory history.
/// A scalar read of fewer bytes cannot supply a whole pointer's identity.
pub(in crate::kernel) fn known_pointer_read_variable_for_term(
    bits: &Bitvector32Term,
) -> Option<Variable> {
    crate::instrumentation::record_deterministic_work(1);
    let Bitvector32Term::MemoryLoad(memory, address, LoadKind::Bits32) = bits else {
        return None;
    };
    let variable = LOAD_VARIABLE_CACHE
        .with(|cache| cache.borrow().get(bits).map(|(variable, _)| *variable))
        .or_else(|| match memory.known_value(address) {
            Some(CValue::Int32(Bitvector32Term::Variable(variable))) => Some(variable),
            _ => materialized_pointer_cell_load_variable(memory, address),
        })?;
    (registered_load_kind_for_variable(&variable) == Some(LoadKind::Bits32)
        && registered_load_bytes_for_variable(&variable)
            == Some(crate::kernel::C_POINTER_BYTE_WIDTH))
    .then_some(variable)
}

// Keep the actual producer expression, including its live snapshot and
// pointer. Load identities can recur in disconnected model arms; their first
// registered origin is not necessarily in the current arm's memory history.
fn record_wide_load_observation(term: &Bitvector32Term, variable: Variable) {
    let Bitvector32Term::MemoryLoad(memory, pointer, LoadKind::Bits64) = term else {
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
fn record_pointer_read_observation(value: &Pointer, memory: &CMemory, address: &Pointer) {
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    crate::instrumentation::record_deterministic_work(1);
    let memory = crate::kernel::intern_c_memory_ref(memory);
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

pub(crate) fn latest_pointer_read_observation(value: &Pointer) -> Option<(SharedCMemory, Pointer)> {
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    crate::instrumentation::record_deterministic_work(1);
    POINTER_READ_OBSERVATIONS
        .with(|registry| registry.borrow().get(&(epoch, value.clone())).cloned())
}

pub(crate) fn latest_wide_load_observation(variable: &Variable) -> Option<Bitvector32Term> {
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    crate::instrumentation::record_deterministic_work(1);
    WIDE_LOAD_OBSERVATIONS.with(|registry| {
        registry
            .borrow()
            .get(&(epoch, *variable))
            .map(|(memory, pointer)| {
                Bitvector32Term::MemoryLoad(
                    memory.clone(),
                    Box::new(pointer.clone()),
                    LoadKind::Bits64,
                )
            })
    })
}

/// Returns the load variable for a load term's provenance-stable form.
/// The term is first canonicalized without assumptions, resolving cached
/// cells and snapshot representation differences. The same cell loaded at
/// different symbolic states therefore shares one load variable whenever
/// the difference is representational. The second return value is the form
/// used by the variable's defining equation.
pub(crate) fn load_variable_for_term(
    bits: &Bitvector32Term,
) -> Option<(Variable, Bitvector32Term)> {
    let Bitvector32Term::MemoryLoad(_, _, _) = bits else {
        return None;
    };
    // Naming is deterministic per term, and callers ask per fact atom per
    // comparison; the epoch walk and canonicalization behind a cold call
    // are not free, so cache by term. Term hashing is cheap: embedded
    // snapshots hash by interned identity.
    if let Some(hit) = LOAD_VARIABLE_CACHE.with(|cache| cache.borrow().get(bits).cloned()) {
        if load_variable_covers_observed_access(bits, hit.0) {
            record_wide_load_observation(bits, hit.0);
            return Some(hit);
        }
    }
    crate::instrumentation::record_deterministic_work(1);
    let computed = load_variable_for_term_uncached(bits)?;
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

fn load_variable_covers_observed_access(bits: &Bitvector32Term, variable: Variable) -> bool {
    let Bitvector32Term::MemoryLoad(memory, pointer, kind) = bits else {
        return false;
    };
    registered_load_kind_for_variable(&variable) == Some(*kind)
        && registered_load_bytes_for_variable(&variable).is_some_and(|bytes| {
            bytes >= recorded_load_access_width(memory, pointer).unwrap_or(kind.byte_width())
        })
}

fn load_variable_for_term_uncached(bits: &Bitvector32Term) -> Option<(Variable, Bitvector32Term)> {
    // A pointer cell this snapshot holds materialized, whose value is the
    // pointer an earlier load of this same cell produced, already names this
    // load: the materialized value is `cell.block + v * width` and `v` is
    // registered as the load of this cell. The integer counterpart below
    // resolves through the canonical form; a pointer cell's value is not an
    // integer, so it is resolved here instead of falling through to the epoch
    // walk. That walk is assumption-free, so it stops at a loop head's havoc
    // even where the head copied the cell back as provably unwritten, and a
    // field such as `arena->occupied` read again inside the loop would get a
    // second name for the value its pointer already carries.
    if let Bitvector32Term::MemoryLoad(memory, pointer, LoadKind::Bits32) = bits
        && let Some(variable) = materialized_pointer_cell_load_variable(memory, pointer)
    {
        return Some((variable, bits.clone()));
    }
    let mut canonical = crate::kernel::memory_provenance::canonicalize_atomic_loads(bits);
    if let Bitvector32Term::Variable(variable) = &canonical
        && !load_variable_covers_observed_access(bits, *variable)
    {
        // An earlier narrower observation may have cached this scalar cell's
        // value. Recheck only the selected term at the actual wider width;
        // neither the old cache entry nor an address equation proves the
        // additional bytes unchanged.
        canonical = crate::kernel::memory_provenance::canonicalize_atomic_loads_deep(bits);
    }
    if let Bitvector32Term::MemoryLoad(memory, pointer, kind) = &canonical {
        let Bitvector32Term::MemoryLoad(origin, _, _) = bits else {
            unreachable!("the pattern above matched a memory load");
        };
        return Some((
            load_variable_for_cell_with_origin(
                memory,
                pointer,
                *kind,
                // Either snapshot's recorded entry is this same load's own
                // width, so the first one found is the answer. Taking the
                // larger would let a miss on one side widen a width the
                // other side knows exactly.
                recorded_load_access_width(origin, pointer)
                    .or_else(|| recorded_load_access_width(memory, pointer))
                    .unwrap_or_else(|| kind.unrecorded_access_byte_width()),
                origin,
            ),
            canonical.clone(),
        ));
    }
    // The canonical form resolved this load through the snapshot's own
    // materialized cell, and the cell holds a load variable: that variable
    // already names this value, so it is this load's name too. Falling
    // through would mint a second identity for one value whenever the cell's
    // snapshot cannot be reached by the assumption-free epoch walk — a cell
    // retained across a call havoc by a `separate` premise, for instance,
    // whose reload would otherwise lose every fact stated about it. The
    // resolution is structural and assumption-free, and the havoc's retention
    // decision is re-checked during certification, so this adds no alias
    // approximation of its own.
    if let Bitvector32Term::Variable(variable) = &canonical
        && let Bitvector32Term::MemoryLoad(_, _, kind) = bits
        && registered_load_kind_for_variable(variable) == Some(*kind)
        && load_variable_covers_observed_access(bits, *variable)
    {
        return Some((*variable, bits.clone()));
    }
    let Bitvector32Term::MemoryLoad(memory, pointer, kind) = bits else {
        unreachable!("the pattern above matched a memory load");
    };
    Some((load_variable_for_cell(memory, pointer, *kind), bits.clone()))
}

/// The registered load variable a materialized pointer cell's value carries,
/// when that value is exactly the pointer a typed load of this cell produces
/// (`symbolic_pointer_load`): the cell's own block, offset `v * width` at the
/// value's pointee width, with `v` registered as a load of this same address.
/// One map lookup and one registry lookup.
fn materialized_pointer_cell_load_variable(
    memory: &SharedCMemory,
    pointer: &Pointer,
) -> Option<Variable> {
    let CValue::Pointer(value) = memory.cells.get(pointer)? else {
        return None;
    };
    let (storage, index, byte_width) = value.pointer().as_loaded()?;
    if *storage != pointer.block {
        return None;
    }
    // The scale must be the one a typed load of this cell applies, or the
    // stored index would not be the loaded one.
    if value.c_type().pointee_type()?.byte_width() != u32::try_from(byte_width).ok()? {
        return None;
    }
    let Bitvector32Term::Variable(variable) = index else {
        return None;
    };
    let (_, registered) = registered_load_for_variable(variable)?;
    (registered == *pointer
        && registered_load_kind_for_variable(variable) == Some(LoadKind::Bits32)
        && registered_load_bytes_for_variable(variable)
            == Some(crate::kernel::C_POINTER_BYTE_WIDTH))
    .then_some(*variable)
}

/// Binds a load term to its load variable and records the defining
/// equation in the path's fact stream. The defining equation is
/// kernel-certified by construction: the load variable represents this
/// load. It must not demand a checkable assumption derivation
/// downstream.
fn mint_load_variable(
    bits: &Bitvector32Term,
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
    load: Bitvector32Term,
    facts: &mut ExecutionFacts,
) {
    record_load_variable_defining_fact_with_source(variable, load, facts, None);
}

pub(crate) fn record_load_variable_defining_fact_with_source(
    variable: Variable,
    load: Bitvector32Term,
    facts: &mut ExecutionFacts,
    source: Option<&LoadSourceId>,
) {
    record_load_variable_defining_fact_with_source_and_pointer(variable, load, facts, source, None);
}

fn record_load_variable_defining_fact_with_source_and_pointer(
    variable: Variable,
    load: Bitvector32Term,
    facts: &mut ExecutionFacts,
    source: Option<&LoadSourceId>,
    typed_pointer_value: Option<&Pointer>,
) {
    let Bitvector32Term::MemoryLoad(memory, pointer, _) = &load else {
        // `load_variable_for_term` currently returns a memory load's
        // canonical operand.  Keep this guard explicit so future changes
        // cannot attach producer metadata to an unrelated term.
        return;
    };
    let defining_load = load.clone();
    let defining_proposition = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(variable)),
            Box::new(load.clone()),
        ),
        true,
    );
    let binding = GeneratedLoadBinding::Exact {
        variable,
        snapshot: CMemorySnapshotIdentity::of(memory.memory()),
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
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
) -> Option<CValue> {
    // Every C load reaches the kernel through here with its type. The
    // `MemoryLoad` term built below carries the read's kind; the address's
    // recorded width, which every read there shares, is kept beside it.
    // Recording it here is what lets an `int32` load keep being separated
    // from a store one element away.
    record_load_access_width(memory, pointer, value_type.byte_width());
    symbolic_load_value_unrecorded(memory, pointer, value_type)
}

/// [`symbolic_load_value`] without recording the access width, for a caller
/// that has already said how wide the access is, as a symbolic static array
/// says it for every element at once
/// ([`declare_symbolic_array_access_widths`]).
pub(in crate::kernel) fn symbolic_load_value_unrecorded(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
) -> Option<CValue> {
    match value_type {
        CType::Int128 | CType::UInt128 => {
            memory.symbolic_wide_integer_load(pointer, MachineIntegerType::from_c_type(value_type)?)
        }
        CType::Void | CType::VoidPointer => None,
        CType::Bool => {
            let load = Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory.clone()),
                Box::new(pointer.clone()),
                LoadKind::UInt8,
            );
            Some(CValue::Bool(Bitvector32Term::if_then_else(
                ConditionTerm::equal(load, Bitvector32Term::Constant(0)),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )))
        }
        CType::Int8 => Some(memory.symbolic_int8_load(pointer)),
        CType::Int16 => Some(memory.symbolic_int16_load(pointer)),
        CType::Int32 => Some(memory.symbolic_int32_load(pointer)),
        CType::UInt8 => Some(memory.symbolic_uint8_load(pointer)),
        CType::UInt16 => Some(memory.symbolic_uint16_load(pointer)),
        CType::UInt32 => Some(memory.symbolic_uint32_load(pointer)),
        CType::Int64 => Some(memory.symbolic_int64_load(pointer)),
        CType::UInt64 => Some(memory.symbolic_uint64_load(pointer)),
        CType::Float32 => Some(memory.symbolic_float32_load(pointer)),
        CType::Float64 => Some(memory.symbolic_float64_load(pointer)),
        CType::Int8Pointer | CType::Int8PointerPointer => Some(memory.symbolic_pointer_load(
            pointer,
            value_type.pointee_type()?.byte_width(),
            value_type,
        )),
        CType::VoidPointerPointer
        | CType::Int16Pointer
        | CType::UInt16Pointer
        | CType::Int32Pointer
        | CType::UInt8Pointer
        | CType::UInt32Pointer
        | CType::Int128Pointer
        | CType::Int64Pointer
        | CType::UInt128Pointer
        | CType::UInt64Pointer
        | CType::Int16PointerPointer
        | CType::UInt16PointerPointer
        | CType::Int32PointerPointer
        | CType::UInt8PointerPointer
        | CType::UInt32PointerPointer
        | CType::Int128PointerPointer
        | CType::Int64PointerPointer
        | CType::UInt128PointerPointer
        | CType::UInt64PointerPointer => Some(memory.symbolic_pointer_load(
            pointer,
            value_type.pointee_type()?.byte_width(),
            value_type,
        )),
        CType::Float32Pointer
        | CType::Float64Pointer
        | CType::Float32PointerPointer
        | CType::Float64PointerPointer => Some(memory.symbolic_pointer_load(
            pointer,
            value_type.pointee_type()?.byte_width(),
            value_type,
        )),
        CType::FunctionPointer(_) => {
            let load = Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory.clone()),
                Box::new(pointer.clone()),
                LoadKind::Bits32,
            );
            let (variable, _) = load_variable_for_term(&load)?;
            Some(CValue::typed_pointer(
                Pointer::symbolic_function(variable),
                value_type,
            ))
        }
        CType::Int8Array(_) => None,
        CType::Int32Array(_)
        | CType::UInt8Array(_)
        | CType::Int16Array(_)
        | CType::UInt16Array(_)
        | CType::UInt32Array(_)
        | CType::Int128Array(_)
        | CType::Int64Array(_)
        | CType::UInt128Array(_)
        | CType::UInt64Array(_)
        | CType::Float32Array(_)
        | CType::Float64Array(_) => None,
        CType::PointerArray(_, _) => None,
    }
}

/// The value a symbolic static-storage cell of type `c_type` at `pointer`
/// holds at function entry, where `memory` holds only the storage's block: a
/// fresh symbolic pointer named by the cell's load for an object pointer (a
/// stored pointer may point into any block), and otherwise the cell's typed
/// load, its integer loads named as their load variables.
///
/// `record_width` says the access width here, as [`symbolic_load_value`]
/// does; a caller that declared it for a whole array
/// ([`declare_symbolic_array_access_widths`]) passes `false`. An object
/// pointer's load retains the same typed definition as a logical read.
/// Reuse only a load already named at this exact snapshot and address.
/// An optional cell-cache reconciliation must not canonicalize a cold load
/// by walking its unrelated memory history. Missing names give no evidence.
pub(in crate::kernel) fn cached_symbolic_storage_cell_value(
    memory: &CMemory,
    pointer: &Pointer,
    c_type: CType,
) -> Option<CValue> {
    let (kind, wrap): (LoadKind, fn(Bitvector32Term) -> CValue) = match c_type {
        CType::Int8 => (LoadKind::Int8, CValue::Int8),
        CType::Int16 => (LoadKind::Int16, CValue::Int16),
        CType::Int32 => (LoadKind::Bits32, CValue::Int32),
        CType::UInt8 => (LoadKind::UInt8, CValue::UInt8),
        CType::UInt16 => (LoadKind::UInt16, CValue::UInt16),
        CType::UInt32 => (LoadKind::Bits32, CValue::UInt32),
        CType::Int64 => (LoadKind::Bits64, CValue::Int64),
        CType::UInt64 => (LoadKind::Bits64, CValue::UInt64),
        _ if c_type.is_object_pointer() => {
            let load = Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory.clone()),
                Box::new(pointer.clone()),
                LoadKind::Bits32,
            );
            return LOAD_VARIABLE_CACHE.with(|cache| {
                let variable = cache.borrow().get(&load)?.0;
                Some(CValue::typed_pointer(Pointer::symbolic(variable), c_type))
            });
        }
        _ => return None,
    };
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory.clone()),
        Box::new(pointer.clone()),
        kind,
    );
    crate::instrumentation::record_deterministic_work(1);
    TERM_CACHE
        .with(|cache| cache.borrow().get(&load).cloned())
        .or_else(|| {
            LOAD_VARIABLE_CACHE.with(|cache| {
                cache
                    .borrow()
                    .get(&load)
                    .map(|(variable, _)| Bitvector32Term::Variable(*variable))
            })
        })
        .map(wrap)
}

pub(in crate::kernel) fn symbolic_storage_cell_value(
    memory: &CMemory,
    pointer: &Pointer,
    c_type: CType,
    record_width: bool,
) -> Option<CValue> {
    if c_type.is_object_pointer() {
        if record_width && pointer.block.starts_with("local:") {
            record_load_access_width(memory, pointer, c_type.byte_width());
        }
        let load = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(memory.clone()),
            Box::new(pointer.clone()),
            LoadKind::Bits32,
        );
        let (variable, _) = load_variable_for_term(&load)
            .expect("symbolic pointer cells must be backed by memory loads");
        let definition = registered_load_term_for_variable(&variable)
            .expect("a symbolic pointer cell retains its immutable defining term");
        let value = Pointer::symbolic(variable);
        let value = pointer_value_with_load_designation(
            CPointerValue::new(value, c_type),
            &registered_load_term_for_variable(&variable)
                .expect("a load retains its defining term"),
        );
        if let Bitvector32Term::MemoryLoad(snapshot, address, _) = definition {
            crate::kernel::equality_graph::EqualityGraph::default()
                .register_pointer_read_definition(value.pointer(), &snapshot, &address);
        }
        return Some(CValue::Pointer(value));
    }
    // The cell holds the load of this storage at its symbolic base, and a
    // term is canonical at creation: name the load as its load variable,
    // exactly as a contract clause over the same storage names it. A raw
    // load here reached the facts a callee's `old(...)` produced, where
    // nothing equates it with the caller's name for the same cell.
    let value = if record_width {
        symbolic_load_value(memory, pointer, c_type)
    } else {
        symbolic_load_value_unrecorded(memory, pointer, c_type)
    };
    value.map(|value| match value {
        CValue::Int8(bits) => CValue::Int8(canonical_term(&bits)),
        CValue::Int16(bits) => CValue::Int16(canonical_term(&bits)),
        CValue::Int32(bits) => CValue::Int32(canonical_term(&bits)),
        CValue::UInt8(bits) => CValue::UInt8(canonical_term(&bits)),
        CValue::UInt16(bits) => CValue::UInt16(canonical_term(&bits)),
        CValue::UInt32(bits) => CValue::UInt32(canonical_term(&bits)),
        CValue::Int64(bits) => CValue::Int64(canonical_term(&bits)),
        CValue::UInt64(bits) => CValue::UInt64(canonical_term(&bits)),
        CValue::Int128(bits) => CValue::Int128(canonical_term(&bits)),
        CValue::UInt128(bits) => CValue::UInt128(canonical_term(&bits)),
        other => other,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn load_width_substitution_preserves_typed_observations_without_inference() {
        let _session = crate::kernel::VerificationSession::enter();
        let from = Variable(946_100);
        let source = crate::kernel::intern_c_memory(CMemory::new().store(
            CMemory::local_pointer("width-substitution-snapshot"),
            CValue::Int32(Bitvector32Term::Variable(from)),
        ));
        let address = |base| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::add(
                PointerOffsetTerm::Constant(base),
                PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(from), 4),
            ),
        };
        let rewrite = |pointer: &Pointer| {
            crate::kernel::reasoning::substitute_bitvector_variable(
                &Bitvector32Term::MemoryLoad(
                    source.clone(),
                    Box::new(pointer.clone()),
                    LoadKind::Bits32,
                ),
                from,
                &Bitvector32Term::Constant(3),
            )
        };
        let parts = |term| {
            let Bitvector32Term::MemoryLoad(memory, pointer, kind) = term else {
                panic!("expected load")
            };
            (memory, pointer, kind)
        };
        let unknown = address(0);
        let (memory, pointer, kind) = parts(rewrite(&unknown));
        assert_eq!(recorded_load_access_width(&memory, &pointer), None);
        assert_eq!(
            load_term_access_width(&memory, &pointer, kind),
            crate::kernel::C_POINTER_BYTE_WIDTH
        );

        let typed = address(64);
        symbolic_load_value(&source, &typed, CType::Int32).unwrap();
        let (memory, pointer, kind) = parts(rewrite(&typed));
        assert_ne!(memory, source, "snapshot terms were substituted too");
        assert_eq!(load_term_access_width(&memory, &pointer, kind), 4);
        let replacement = Bitvector32Term::Variable(Variable(946_101));
        let source_index = Bitvector32Term::Variable(from);
        let mut walker = crate::kernel::proof::term_rewrite::TermRewrite::for_bits_checked(
            &source_index,
            &replacement,
        );
        let walked = walker.bits(&Bitvector32Term::MemoryLoad(
            source.clone(),
            Box::new(typed.clone()),
            LoadKind::Bits32,
        ));
        assert!(walker.refusal().is_none());
        let (memory, pointer, kind) = parts(walked);
        assert_eq!(load_term_access_width(&memory, &pointer, kind), 4);

        let conflicting = address(128);
        symbolic_load_value(&source, &conflicting, CType::Int32).unwrap();
        // Use the actual substituted spelling, which removes the old index.
        let destination = Pointer {
            block: conflicting.block.clone(),
            offset: PointerOffsetTerm::Constant(140),
        };
        symbolic_load_value(&source, &destination, CType::Int64).unwrap();
        let (memory, pointer, kind) = parts(rewrite(&conflicting));
        assert_eq!(load_term_access_width(&memory, &pointer, kind), 8);
        assert_eq!(recorded_load_access_width(&source, &destination), Some(8));
        let fixed_index = Bitvector32Term::Constant(3);
        let mut walker = crate::kernel::proof::term_rewrite::TermRewrite::for_bits_checked(
            &source_index,
            &fixed_index,
        );
        let walked = walker.bits(&Bitvector32Term::MemoryLoad(
            source.clone(),
            Box::new(conflicting),
            LoadKind::Bits32,
        ));
        assert!(walker.refusal().is_none());
        let (memory, pointer, kind) = parts(walked);
        assert_eq!(memory, source);
        assert_eq!(load_term_access_width(&memory, &pointer, kind), 8);
    }

    #[test]
    fn legacy_pointer_loads_do_not_issue_designations_from_numeric_read_names() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = CMemory::new();
        let context = PureFactContext::new();
        let cell = Pointer::symbolic(Variable(92_320));
        let mut facts = ExecutionFacts::new();
        let CValue::Pointer(symbolic) = canonicalized_symbolic_load_value_with_identity(
            &memory,
            &cell,
            CType::Int64Pointer,
            &mut facts,
            &context,
            true,
            None,
            LoadPurpose::Logical,
        )
        .unwrap() else {
            panic!()
        };
        assert!(symbolic.designation().is_none());
        let load = registered_load_term_for_variable(
            &typed_pointer_read_variable(symbolic.pointer()).unwrap(),
        )
        .unwrap();

        let CValue::Pointer(storage) =
            symbolic_storage_cell_value(&memory, &cell, CType::Int64Pointer, true).unwrap()
        else {
            panic!()
        };
        assert_eq!(storage.designation(), symbolic.designation());
        let CValue::Pointer(cached) = canonicalized_pointer_value_from_int_cell(
            &cell,
            &CValue::Int32(load.clone()),
            CType::Int64Pointer,
            &mut facts,
            &context,
            None,
            LoadPurpose::Logical,
        )
        .unwrap() else {
            panic!()
        };
        assert_eq!(cached.designation(), symbolic.designation());
        let CValue::Pointer(unrecorded) =
            symbolic_load_value_unrecorded(&memory, &cell, CType::Int64Pointer).unwrap()
        else {
            panic!()
        };
        assert!(unrecorded.designation().is_none());

        let sibling_cell = Pointer::symbolic(Variable(92_321));
        let CValue::Pointer(sibling) = canonicalized_symbolic_load_value_with_identity(
            &memory,
            &sibling_cell,
            CType::Int64Pointer,
            &mut facts,
            &context,
            true,
            None,
            LoadPurpose::Logical,
        )
        .unwrap() else {
            panic!()
        };
        assert!(sibling.designation().is_none());
        assert_ne!(symbolic.pointer(), sibling.pointer());
        // Legacy address equality still supplies no authenticated Object.
        let sibling = sibling.with_pointer(symbolic.pointer().clone());
        assert_eq!(symbolic, sibling);
    }

    #[test]
    fn designated_pointer_stores_reload_the_complete_carrier() {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = Pointer {
            block: PointerBlock::from("global:pointer_slot"),
            offset: PointerOffsetTerm::Constant(0),
        };
        let referent = Pointer::symbolic(Variable(92_322));
        let stored = CPointerValue::new(referent.clone(), CType::Int64Pointer).with_designation(
            PointerDesignation::Object {
                root: referent.clone(),
                base: referent,
                path: vec![PointerDomainSelection::Member("array".into())].into(),
                element_type: CType::Int64,
                stride: 8,
                count: IntegerTerm::constant_i64(4).into(),
            },
        );
        let memory = CMemory::new()
            .with_block(cell.block.clone(), 8)
            .store(cell.clone(), CValue::Pointer(stored.clone()));
        let context = PureFactContext::new();
        assert_eq!(
            symbolic_storage_cell_value(&memory, &cell, CType::Int64Pointer, true),
            Some(CValue::Pointer(stored.clone()))
        );
        assert_eq!(
            symbolic_load_value_unrecorded(&memory, &cell, CType::Int64Pointer),
            Some(CValue::Pointer(stored.clone()))
        );
        let paths = evaluate_c_memory_load_paths(
            &memory,
            cell.clone(),
            CType::Int64Pointer,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
            true,
            false,
            None,
            None,
        );
        assert_eq!(paths.len(), 1);
        let CExpressionOutcome::Value(CValue::Pointer(reloaded)) = &paths[0].outcome else {
            panic!()
        };
        assert_eq!(reloaded, &stored);
        assert!(std::ptr::eq(
            reloaded.designation().unwrap(),
            stored.designation().unwrap()
        ));
        let paths = evaluate_spec_memory_load_paths(
            &memory,
            cell,
            CType::Int64Pointer,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
        );
        assert_eq!(paths.len(), 1);
        let CExpressionOutcome::Value(CValue::Pointer(reloaded)) = &paths[0].outcome else {
            panic!()
        };
        assert_eq!(reloaded, &stored);
    }

    #[test]
    fn load_registry_reset_and_restore_invalidate_cached_names() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = intern_c_memory(CMemory::new());
        let load = |id| {
            Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(Pointer::symbolic(Variable(id))),
                LoadKind::Bits32,
            )
        };
        let first = load(955_801);
        let (variable, _) = load_variable_for_term(&first).unwrap();
        assert!(registered_load_term_for_variable(&variable).is_some());
        clear_load_variable_registry();
        assert!(registered_load_term_for_variable(&variable).is_none());
        let (variable, _) = load_variable_for_term(&first).unwrap();
        assert_eq!(registered_load_term_for_variable(&variable), Some(first));
        let saved = capture_load_variable_registry();
        let later = load(955_802);
        let (later_variable, _) = load_variable_for_term(&later).unwrap();
        restore_load_variable_registry(&saved);
        assert!(registered_load_term_for_variable(&later_variable).is_none());
        let (later_variable, _) = load_variable_for_term(&later).unwrap();
        assert_eq!(
            registered_load_term_for_variable(&later_variable),
            Some(later)
        );
    }

    #[test]
    fn logical_cached_pointer_read_carries_its_current_cell_equation() {
        let _session = crate::kernel::VerificationSession::enter();
        let empty = PureFactContext::new();
        let base = CMemory::new();
        let address = Pointer::symbolic(Variable(955_901));
        let alias = Pointer::symbolic(Variable(955_902));
        let model = Pointer::symbolic(Variable(955_903));
        let cached = logical_pointer_read(&base, &address, &empty);
        let variable = typed_pointer_read_variable(&cached).unwrap();
        let mut samples = Vec::new();
        for size in [16u64, 64, 256, 1024] {
            let mut memory = base.clone().materialize_named_cell(
                address.clone(),
                CValue::Int32(Bitvector32Term::Variable(variable)),
            );
            let mut context = empty
                .clone()
                .assume_condition(
                    ConditionTerm::pointer_equal(address.clone(), alias.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::pointer_equal(cached.clone(), model.clone()),
                    true,
                );
            for i in 0..size {
                memory = memory.store(Pointer::symbolic(Variable(956_000 + i)), int32(7));
                context = context.assume_condition(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(958_000 + i)),
                        Bitvector32Term::Constant(7),
                    ),
                    true,
                );
            }
            let ((paths, work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    evaluate_logical_memory_load_paths(
                        &memory,
                        address.clone(),
                        CType::Int64Pointer,
                        ExecutionFacts::new(),
                        Vec::new(),
                        &context,
                    )
                })
            });
            samples.push((work, map_work));
            let [path] = paths.as_slice() else {
                panic!("one logical read");
            };
            assert_eq!(
                path.outcome,
                CExpressionOutcome::Value(CValue::Pointer(pointer_value_with_load_designation(
                    CPointerValue::new(cached.clone(), CType::Int64Pointer),
                    &registered_load_term_for_variable(&variable).unwrap(),
                )))
            );
            let CExpressionOutcome::Value(CValue::Pointer(value)) = &path.outcome else {
                panic!("one pointer-valued read")
            };
            assert!(path.obligations.is_empty());
            assert_eq!(path.facts.len(), 1);
            assert!(!path.facts.has_path_conditions());
            let required = Pointer::loaded_value(&intern_c_memory_ref(&memory), &alias);
            let equal = |facts: &PureFactContext| {
                crate::kernel::resource_arguments_proven_equal(
                    &AlgebraicValue::C(CValue::Pointer(value.clone().with_pointer(model.clone()))),
                    &AlgebraicValue::C(CValue::Pointer(
                        value.clone().with_pointer(required.clone()),
                    )),
                    facts,
                )
            };
            assert!(
                !equal(&context),
                "constructing the result must not mutate caller evidence"
            );
            let retained = assumptions_with_path_context(&context, &path.facts, &path.obligations);
            assert!(equal(&retained));
            assert!(!equal(&context));
            assert!(!equal(&retained.restricted_to_facts(&[], &[])));
            assert!(!ResourceContext::new().permits_memory_read(&alias, 8, &retained));
            let missing_alias = empty.clone().assume_condition(
                ConditionTerm::pointer_equal(cached.clone(), model.clone()),
                true,
            );
            assert!(!equal(&assumptions_with_path_context(
                &missing_alias,
                &path.facts,
                &[]
            )));

            let replacement = Pointer::symbolic(Variable(955_904));
            let changed = memory.clone().store(
                address.clone(),
                CValue::typed_pointer(replacement.clone(), CType::Int64Pointer),
            );
            let changed_paths = evaluate_logical_memory_load_paths(
                &changed,
                address.clone(),
                CType::Int64Pointer,
                ExecutionFacts::new(),
                Vec::new(),
                &retained,
            );
            let changed_context =
                assumptions_with_path_context(&retained, &changed_paths[0].facts, &[]);
            let changed_read = Pointer::loaded_value(&intern_c_memory_ref(&changed), &alias);
            assert!(changed_context.pointers_known_equal(&changed_read, &replacement));
            assert!(!changed_context.pointers_known_equal(&changed_read, &cached));
        }
        assert!(samples[3].0 <= samples[0].0 * 3 + 128, "{samples:?}");
        assert!(samples[3].1 <= samples[0].1 * 6 + 512, "{samples:?}");
    }

    #[test]
    fn logical_read_equations_are_not_conditions_or_quantifier_guards() {
        let value = Pointer::symbolic(Variable(959_001));
        let read = Pointer::loaded_value(&intern_c_memory(CMemory::new()), &value);
        let fact = ExecutionPureFact::logical_read_equation(value, read);
        let facts: ExecutionFacts = vec![fact.clone()].into();
        assert!(!facts.has_path_conditions());
        let goal = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
        assert_eq!(wrap_path_context(goal.clone(), &facts, &[]), goal);
        assert_eq!(guard_quantified_witness(goal.clone(), &facts), goal);
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
        let base = CMemory::new();
        let mut facts = ExecutionFacts::new();
        let value = canonicalized_symbolic_load_value_with_identity(
            &base,
            &address,
            CType::Int32,
            &mut facts,
            &context,
            false,
            None,
            LoadPurpose::Logical,
        )
        .unwrap();
        let memory = base.materialize_named_cell(address.clone(), value);
        let paths = evaluate_logical_memory_load_paths(
            &memory,
            address,
            CType::Int64Pointer,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
        );
        assert!(paths.iter().all(|path| path.facts.is_empty()));
    }

    // Typed observations must preserve the complete pointer, selected alias
    // premises, snapshot changes, and session boundaries without corpus scans.
    // A cached pointer can still denote an older defining load after a frame
    // materializes its named scalar cell. A checked index must retain where
    // that value was read now, without publishing evidence to another context.
    #[test]
    fn checked_resource_index_retains_its_current_pointer_cell() {
        let _session = crate::kernel::VerificationSession::enter();
        let empty = PureFactContext::new();
        let base = CMemory::new();
        let source = Pointer::symbolic(Variable(955_001));
        let cached = logical_pointer_read(&base, &source, &empty);
        let variable = typed_pointer_read_variable(&cached).expect("typed cached load");
        let address = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(955_002)), 4),
        };
        let alias = Pointer::symbolic(Variable(955_003));
        let current = base.materialize_named_cell(
            address.clone(),
            CValue::Int32(Bitvector32Term::Variable(variable)),
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
                ConditionTerm::pointer_equal(model.clone(), logical.clone()),
                true,
            );
        let context = base_context.clone().require_owned_expression_loads();
        let isolated = context.clone();
        let paths = evaluate_c_memory_load_paths(
            &current,
            address.clone(),
            CType::Int64Pointer,
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
        let CExpressionOutcome::Value(CValue::Pointer(value)) = &path.outcome else {
            panic!("a pointer-valued read");
        };
        let arguments_equal = |facts: &PureFactContext| {
            crate::kernel::resource_arguments_proven_equal(
                &AlgebraicValue::C(CValue::Pointer(value.clone().with_pointer(model.clone()))),
                &AlgebraicValue::C(CValue::Pointer(value.clone())),
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
            ConditionTerm::pointer_equal(model.clone(), logical.clone()),
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
            let paths = evaluate_c_memory_load_paths(
                &current,
                address.clone(),
                CType::Int64Pointer,
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
    }

    #[test]
    fn pointer_read_observations_check_frames_scope_and_scaling() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer::symbolic(Variable(960_000));
        let alias = Pointer::symbolic(Variable(960_001));
        let base = CMemory::new();
        let empty = PureFactContext::new();
        let facts = empty.clone().assume_condition(
            ConditionTerm::pointer_equal(address.clone(), alias.clone()),
            true,
        );
        let read = |memory: &CMemory, address: &Pointer, purpose| {
            let CValue::Pointer(value) = canonicalized_symbolic_load_value_with_identity(
                memory,
                address,
                CType::Int32Pointer,
                &mut Vec::new().into(),
                &empty,
                false,
                None,
                purpose,
            )
            .unwrap() else {
                panic!("expected a typed pointer read");
            };
            value.pointer().clone()
        };
        let left = read(&base, &address, LoadPurpose::Logical);
        let right = read(&base, &alias, LoadPurpose::Logical);
        let equal = |left: &Pointer, right: &Pointer, facts: &PureFactContext| {
            crate::kernel::memory_provenance::pointer_read_has_recorded_value(left, right, facts)
        };
        assert!(equal(&left, &right, &facts));
        assert!(!equal(&left, &right, &empty));
        let partial = base
            .clone()
            .store(address.offset_by_bytes(4), CValue::Int32(0u32.into()));
        let changed = read(&partial, &address, LoadPurpose::Logical);
        assert!(!equal(&left, &changed, &facts));
        let replaced = base.clone().store(
            address.clone(),
            CValue::typed_pointer(Pointer::null(), CType::Int32Pointer),
        );
        let changed = read(&replaced, &address, LoadPurpose::Logical);
        assert!(!equal(&left, &changed, &facts));
        let mut previous = None;
        for count in [16_u64, 64, 256, 1024] {
            for index in 0..count {
                read(
                    &base,
                    &Pointer::symbolic(Variable(970_000 + index)),
                    LoadPurpose::Logical,
                );
            }
            let (proved, work) =
                crate::instrumentation::measure_deterministic_work(|| equal(&left, &right, &facts));
            assert!(proved);
            if let Some(previous) = previous {
                assert!(work <= previous + 16, "{count}: {work} after {previous}");
            }
            previous = Some(work);
        }
        let original = latest_pointer_read_observation(&left).unwrap();
        let saved = capture_load_variable_registry();
        begin_load_origin_epoch();
        assert!(latest_pointer_read_observation(&left).is_none());
        let volatile = read(&base, &address, LoadPurpose::VolatileProgram);
        assert!(latest_pointer_read_observation(&volatile).is_none());
        let scalar = Bitvector32Term::MemoryLoad(
            intern_c_memory(base.clone()),
            Box::new(address.clone()),
            LoadKind::Bits32,
        );
        let scalar = load_variable_for_term(&scalar).unwrap().0;
        assert!(latest_pointer_read_observation(&Pointer::symbolic(scalar)).is_none());
        restore_load_variable_registry(&saved);
        assert_eq!(latest_pointer_read_observation(&left), Some(original));
        clear_load_variable_registry();
        assert!(latest_pointer_read_observation(&left).is_none());
    }

    // Model arms can share a canonical word but have different live DAGs.
    // Refresh only its producer observation, including on a naming-cache hit.
    #[test]
    fn wide_observations_preserve_width_scope_and_selected_query_scaling() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::symbolic(Variable(940_000));
        let other = Pointer::symbolic(Variable(940_001));
        let base = intern_c_memory(CMemory::new());
        let load = |memory: &SharedCMemory, pointer: &Pointer, kind| {
            Bitvector32Term::MemoryLoad(memory.clone(), Box::new(pointer.clone()), kind)
        };
        let first = load(&base, &pointer, LoadKind::Bits64);
        let (word, _) = load_variable_for_term(&first).unwrap();
        let word_term = Bitvector32Term::Variable(word);
        let second_memory = intern_c_memory(base.memory().clone().store(
            Pointer {
                block: "observation:unrelated".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            CValue::UInt64(Bitvector32Term::UInt64Constant(7)),
        ));
        // Materialize the same named value in an independent live snapshot.
        let second_memory = intern_c_memory(
            second_memory
                .memory()
                .clone()
                .store(pointer.clone(), CValue::UInt64(word_term.clone())),
        );
        let second = load(&second_memory, &pointer, LoadKind::Bits64);
        assert_eq!(load_variable_for_term(&second).unwrap().0, word);
        assert_eq!(latest_wide_load_observation(&word), Some(second.clone()));
        assert_eq!(load_variable_for_term(&first).unwrap().0, word);
        assert_eq!(latest_wide_load_observation(&word), Some(first.clone()));
        load_variable_for_term(&second).unwrap();
        let facts = PureFactContext::new();
        assert!(
            crate::kernel::memory_provenance::wide_read_has_recorded_value(
                &word_term, &second, &facts,
            )
        );
        assert!(
            !crate::kernel::memory_provenance::wide_read_has_recorded_value(
                &word_term,
                &load(&second_memory, &other, LoadKind::Bits64),
                &facts,
            )
        );
        let changed = intern_c_memory(second_memory.memory().clone().store(
            pointer.clone(),
            CValue::UInt64(Bitvector32Term::UInt64Constant(9)),
        ));
        assert!(
            !crate::kernel::memory_provenance::wide_read_has_recorded_value(
                &word_term,
                &load(&changed, &pointer, LoadKind::Bits64),
                &facts,
            )
        );
        let narrow = load(&base, &pointer, LoadKind::Bits32);
        let (narrow_word, _) = load_variable_for_term(&narrow).unwrap();
        assert!(latest_wide_load_observation(&narrow_word).is_none());
        assert!(
            !crate::kernel::memory_provenance::wide_read_has_recorded_value(
                &word_term,
                &Bitvector32Term::Variable(narrow_word),
                &facts,
            )
        );
        let mut previous = None;
        for count in [16_u64, 64, 256, 1024] {
            for index in 0..count {
                let unrelated = Pointer::symbolic(Variable(950_000 + index));
                load_variable_for_term(&load(&base, &unrelated, LoadKind::Bits64)).unwrap();
            }
            let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::memory_provenance::wide_read_has_recorded_value(
                    &word_term, &second, &facts,
                )
            });
            assert!(proved);
            if let Some(previous) = previous {
                assert!(work <= previous + 16, "{count}: {work} after {previous}");
            }
            previous = Some(work);
        }
        let saved = capture_load_variable_registry();
        load_variable_for_term(&first).unwrap();
        assert_eq!(latest_wide_load_observation(&word), Some(first));
        restore_load_variable_registry(&saved);
        assert_eq!(latest_wide_load_observation(&word), Some(second.clone()));
        begin_load_origin_epoch();
        assert!(latest_wide_load_observation(&word).is_none());
        restore_load_variable_registry(&saved);
        assert_eq!(latest_wide_load_observation(&word), Some(second));
    }

    #[test]
    fn a_loaded_pointer_cannot_reach_a_local_declared_after_the_read() {
        let storage = PointerBlock::Heap(8710);
        let early: PointerBlock = "local:early_object".into();
        let later: PointerBlock = "local:later_object".into();
        let cell = Pointer {
            block: storage.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = CMemory::new()
            .with_block(storage.clone(), 16)
            .with_block(early.clone(), 4);
        let value_type = CType::Int32Pointer;
        let assumptions = PureFactContext::new()
            .assume_proposition(Proposition::CMemoryReadDefined {
                memory: memory.clone(),
                pointer: cell.clone(),
                value_type,
            })
            .assume_proposition(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: cell.clone(),
                bytes: Bitvector32Term::Constant(8),
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
        let CExpressionOutcome::Value(CValue::Pointer(value)) = &path.outcome else {
            panic!("pointer value expected");
        };
        let loaded = &value.pointer().block;
        assert!(loaded.proven_distinct(&later));
        assert!(later.proven_distinct(loaded));
        assert!(!loaded.proven_distinct(&early));
        assert!(!loaded.proven_distinct(&PointerBlock::Heap(8711)));
    }

    #[test]
    fn unknown_pointer_in_fresh_storage_does_not_inherit_storage_provenance() {
        for block in [PointerBlock::Heap(8700), PointerBlock::Temporary(8701)] {
            for offset in [0, 8] {
                let cell = Pointer {
                    block: block.clone(),
                    offset: PointerOffsetTerm::Constant(offset),
                };
                let memory = CMemory::new().with_block(block.clone(), 16);
                let value_type = CType::Int32Pointer;
                let assumptions = PureFactContext::new()
                    .assume_proposition(Proposition::CMemoryReadDefined {
                        memory: memory.clone(),
                        pointer: cell.clone(),
                        value_type,
                    })
                    .assume_proposition(Proposition::CMemoryLoadable {
                        memory: memory.clone(),
                        base: cell.clone(),
                        bytes: Bitvector32Term::Constant(8),
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
                    let CExpressionOutcome::Value(CValue::Pointer(value)) = &path.outcome else {
                        panic!("pointer value expected");
                    };
                    assert!(matches!(value.pointer().block, PointerBlock::Symbolic(_)));
                    assert!(
                        !value
                            .pointer()
                            .block
                            .proven_distinct(&PointerBlock::Heap(8702))
                    );
                    assert_eq!(value.c_type(), value_type);
                }
                let bits = Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory_ref(&memory),
                    Box::new(cell.clone()),
                    crate::kernel::LoadKind::Bits32,
                );
                let mut facts = crate::kernel::ExecutionFacts::new();
                let cached = canonicalized_pointer_value_from_int_cell(
                    &cell,
                    &CValue::Int32(bits),
                    value_type,
                    &mut facts,
                    &assumptions,
                    None,
                    LoadPurpose::Validity,
                )
                .unwrap();
                let CValue::Pointer(cached) = cached else {
                    panic!("cached pointer expected");
                };
                assert!(matches!(cached.pointer().block, PointerBlock::Symbolic(_)));
                let target = Pointer {
                    block: PointerBlock::Heap(8702),
                    offset: PointerOffsetTerm::Constant(0),
                };
                let stored = memory.store(
                    cell.clone(),
                    CValue::typed_pointer(target.clone(), value_type),
                );
                let paths = evaluate_logical_memory_load_paths(
                    &stored,
                    cell,
                    value_type,
                    Vec::new().into(),
                    Vec::new(),
                    &assumptions,
                );
                assert!(
                    matches!(&paths[0].outcome, CExpressionOutcome::Value(CValue::Pointer(value)) if value.pointer() == &target)
                );
            }
        }
    }

    #[test]
    fn logical_scalar_read_preserves_cached_offset_spelling() {
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(Bitvector32Term::Variable(Variable(944_021))),
                    byte_width: 4,
                }),
                Box::new(PointerOffsetTerm::Constant(16)),
            ),
        };
        let expected = CValue::Int32(Bitvector32Term::Constant(7));
        let memory = CMemory::new().store(pointer.clone(), expected.clone());
        let paths = evaluate_logical_memory_load_paths(
            &memory,
            pointer,
            CType::Int32,
            Vec::new().into(),
            Vec::new(),
            &PureFactContext::new(),
        );
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].outcome, CExpressionOutcome::Value(expected));
    }

    #[test]
    fn logical_reads_of_a_returned_field_share_checked_alias_identity() {
        let field = Pointer {
            block: "local:parent-guard".into(),
            offset: PointerOffsetTerm::Constant(8),
        };
        let alias = Pointer::symbolic(Variable(944_019));
        let before = CMemory::new()
            .with_block(field.block.clone(), 16)
            .store(field.clone(), CValue::Int32(Bitvector32Term::Constant(1)));
        let range =
            CMemoryRange::new_with_element_width(field.clone(), 0u32.into(), 4u32.into(), 1);
        let memory = before.with_call_memory_havoc(
            Variable(944_020),
            &[range],
            &PureFactContext::new(),
            None,
        );
        let facts = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(alias.clone(), field.clone()),
            true,
        );
        let read = |pointer, assumptions: &PureFactContext| {
            evaluate_logical_memory_load_paths(
                &memory,
                pointer,
                CType::Int32,
                Vec::new().into(),
                Vec::new(),
                assumptions,
            )
        };
        let direct = read(field, &facts);
        let returned = read(alias.clone(), &facts);
        assert!(matches!(
            direct[0].outcome,
            CExpressionOutcome::Value(CValue::Int32(_))
        ));
        let CExpressionOutcome::Value(CValue::Int32(left)) = &direct[0].outcome else {
            panic!("scalar read expected");
        };
        let CExpressionOutcome::Value(CValue::Int32(right)) = &returned[0].outcome else {
            panic!("scalar read expected");
        };
        let capture = crate::kernel::memory_provenance::CheckedLoadEqualityCapture::start();
        assert!(facts.memory_loads_proven_equal(left, right));
        let evidence = capture.finish();
        assert!(!evidence.is_empty());
        assert!(evidence.iter().all(|proof| proof.checks(&facts)));
        assert!(
            evidence
                .iter()
                .all(|proof| !proof.checks(&PureFactContext::new()))
        );
        let mut work = Vec::new();
        for count in [16, 64, 256, 1024] {
            let mut context = facts.clone();
            for index in 0..count {
                context = context.assume_condition(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(960_000 + index)),
                        Bitvector32Term::Constant(index as u32),
                    ),
                    true,
                );
            }
            let (valid, units) = crate::instrumentation::measure_deterministic_work(|| {
                let capture = crate::kernel::memory_provenance::CheckedLoadEqualityCapture::start();
                let equal = context.memory_loads_proven_equal(left, right);
                let evidence = capture.finish();
                equal && !evidence.is_empty() && evidence.iter().all(|proof| proof.checks(&context))
            });
            assert!(valid);
            work.push(units);
        }
        assert!(
            work[3] <= work[0] * 4 + 64,
            "ambient alias-equality scan: {work:?}"
        );
        let unrelated = read(alias, &PureFactContext::new());
        assert_ne!(
            direct[0].outcome, unrelated[0].outcome,
            "a missing alias premise cannot join reads"
        );
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
            let value_type = CType::Int32Pointer;
            let before = CMemory::new()
                .with_block(target.block.clone(), 4)
                .with_block(cell.block.clone(), 16)
                .store(
                    cell.clone(),
                    CValue::typed_pointer(target.clone(), value_type),
                );
            let range =
                CMemoryRange::new_with_element_width(cell.clone(), 0u32.into(), 8u32.into(), 1);
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
                let CExpressionOutcome::Value(CValue::Pointer(value)) = &path.outcome else {
                    panic!("pointer value expected");
                };
                assert!(matches!(value.pointer().block, PointerBlock::Symbolic(_)));
                assert!(!value.pointer().block.proven_distinct(&target.block));
            }
            let bits = Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(&memory),
                Box::new(cell.clone()),
                crate::kernel::LoadKind::Bits32,
            );
            let cached = canonicalized_pointer_value_from_int_cell(
                &cell,
                &CValue::Int32(bits),
                value_type,
                &mut ExecutionFacts::new(),
                &assumptions,
                None,
                LoadPurpose::Validity,
            )
            .unwrap();
            let CValue::Pointer(cached) = cached else {
                panic!("cached pointer expected");
            };
            assert!(matches!(cached.pointer().block, PointerBlock::Symbolic(_)));
            assert!(!cached.pointer().block.proven_distinct(&target.block));
        }
    }

    #[test]
    fn indexed_local_load_uses_proven_alias_without_inventing_initialization() {
        let index = Bitvector32Term::Variable(Variable(839));
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
        let assumptions = PureFactContext::new().assume_condition(
            ConditionTerm::equal(index, Bitvector32Term::Constant(1)),
            true,
        );
        let memory = CMemory::new()
            .with_block(base.block.clone(), 12)
            .store(base.offset_by_bytes(4), int32(3));
        for initialized in [false, true] {
            let memory = if initialized {
                memory.clone().store(base.offset_by_bytes(8), int32(7))
            } else {
                memory.clone()
            };
            let paths = evaluate_c_memory_load_paths(
                &memory,
                pointer.clone(),
                CType::Int32,
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
                    CExpressionOutcome::Value(int32(7))
                } else {
                    CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead)
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
        let retained_index = Bitvector32Term::Variable(Variable(812));
        let written_index = Bitvector32Term::Variable(Variable(813));
        let read_index = Bitvector32Term::Variable(Variable(814));
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
        let ancestor_memory = CMemory::new().store(retained, int32(1));
        let ancestor = intern_c_memory_ref(&ancestor_memory);
        let current = ancestor_memory.store(written.clone(), int32(2));
        let distinct = PureFactContext::new().assume_condition(
            ConditionTerm::equal(read_index.clone(), written_index.clone()),
            false,
        );
        let aliasing = PureFactContext::new()
            .assume_condition(ConditionTerm::equal(read_index, written_index), true);
        let mut cache = MemoryLoadAliasCache::default();

        let distinct_paths = evaluate_c_memory_load_paths_with_alias_cache(
            &current,
            read.clone(),
            CType::Int32,
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
        let CExpressionOutcome::Value(CValue::Int32(Bitvector32Term::Variable(variable))) =
            &distinct_path.outcome
        else {
            panic!("the unresolved distinct load should have a symbolic identity");
        };
        let (named_memory, named_pointer) = registered_load_for_variable(variable)
            .expect("the symbolic identity should retain its exact load");
        assert_eq!(named_memory, ancestor);
        assert_eq!(named_pointer, read);

        // Reuse the same per-load cache deliberately. Its assumption-context
        // key must prevent the distinct answer, and therefore the ancestor
        // name, from leaking into the sibling context where the write aliases.
        let aliasing_paths = evaluate_c_memory_load_paths_with_alias_cache(
            &current,
            read,
            CType::Int32,
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
        assert_eq!(aliasing_path.outcome, CExpressionOutcome::Value(int32(2)));
    }

    #[test]
    fn minted_load_fact_carries_exact_producer_binding() {
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(12),
        };
        let load = Bitvector32Term::MemoryLoad(
            memory.clone(),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Bits32,
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
                snapshot,
                pointer: recorded_pointer,
                load: recorded_load,
                ..
            }) if *recorded == variable
                && *snapshot == CMemorySnapshotIdentity::of(memory.memory())
                && recorded_pointer == &pointer
                && recorded_load == &canonical
        ));
    }

    #[test]
    fn repeated_mint_keeps_each_exact_source_observation_on_one_fact() {
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(12),
        };
        let load =
            Bitvector32Term::MemoryLoad(memory, Box::new(pointer), crate::kernel::LoadKind::Bits32);
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
        let first_memory = crate::kernel::intern_c_memory(CMemory::new());
        let first_load = Bitvector32Term::MemoryLoad(
            first_memory.clone(),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Bits32,
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
        let fact = &facts[0];
        assert!(fact.generated_load_binding().is_some());
        assert_eq!(fact.generated_load_source_events().len(), 1);

        // A fresh arena represents a new epoch. Its empty CMemory is
        // structurally equal to the first one, but its embedded snapshot
        // identity is intentionally different.
        crate::kernel::primitives::start_fresh_c_memory_arena();
        let second_memory = crate::kernel::intern_c_memory(CMemory::new());
        let second_load = Bitvector32Term::MemoryLoad(
            second_memory.clone(),
            Box::new(pointer),
            crate::kernel::LoadKind::Bits32,
        );
        let replacement = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(variable)),
                Box::new(second_load),
            ),
            true,
        );
        assert_eq!(fact.proposition(), &replacement);
        assert_ne!(
            CMemorySnapshotIdentity::of(first_memory.memory()),
            CMemorySnapshotIdentity::of(second_memory.memory())
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
    fn a_symbolic_load_over_many_undecided_cells_splits_without_recursing() {
        const CELLS: u32 = 400;
        let paths = std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(|| {
                let block = PointerBlock::from("global:split_table");
                let mut memory = CMemory::new().with_block(block.clone(), CELLS * 4);
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
                    offset: PointerOffsetTerm::scale_int32(
                        Bitvector32Term::Variable(Variable(841)),
                        4,
                    ),
                };
                evaluate_c_memory_load_paths(
                    &memory,
                    pointer,
                    CType::Int32,
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
                &CExpressionOutcome::Value(int32(u32::try_from(index).unwrap()))
            );
        }
    }

    fn logical_pointer_read(
        memory: &CMemory,
        address: &Pointer,
        context: &PureFactContext,
    ) -> Pointer {
        let paths = evaluate_logical_memory_load_paths(
            memory,
            address.clone(),
            CType::Int64Pointer,
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
        let CExpressionOutcome::Value(CValue::Pointer(value)) = &path.outcome else {
            panic!("pointer value expected");
        };
        value.pointer().clone()
    }

    #[test]
    fn program_and_logical_reads_share_an_opaque_alias_load_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(95_000)), 4),
        };
        let alias = Pointer::symbolic(Variable(95_001));
        let memory = CMemory::new();
        let empty = PureFactContext::new();
        let resources = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(
            CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                owner.clone(),
                0u32.into(),
                1u32.into(),
                8,
            )),
        );
        let without_alias = empty
            .assume_proposition(Proposition::CResourceComposition(resources))
            .assume_proposition(Proposition::CMemoryReadDefined {
                memory: memory.clone(),
                pointer: alias.clone(),
                value_type: CType::UInt64,
            })
            .assume_proposition(Proposition::CMemoryLoadable {
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
            CType::UInt64,
            Vec::new().into(),
            Vec::new(),
            &context,
        );
        let program = evaluate_c_memory_load_paths(
            &memory,
            alias.clone(),
            CType::UInt64,
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
        assert!(matches!(logical[0].outcome, CExpressionOutcome::Value(_)));
        assert_eq!(program[0].outcome, logical[0].outcome);
        let unrelated = evaluate_logical_memory_load_paths(
            &memory,
            alias.clone(),
            CType::UInt64,
            Vec::new().into(),
            Vec::new(),
            &without_alias,
        );
        assert_ne!(
            unrelated[0].outcome, logical[0].outcome,
            "an unpublished address equality must not merge different reads"
        );
        // The C read may have been named before this model alias existed.
        // Reusing the materialized cell must preserve that earlier value.
        let CExpressionOutcome::Value(earlier_value) = &unrelated[0].outcome else {
            panic!("the earlier read should denote a scalar value");
        };
        let CExpressionOutcome::Value(alias_value) = &logical[0].outcome else {
            panic!("the newly exposed alias should denote a scalar value");
        };
        let cached_memory = memory
            .clone()
            .materialize_named_cell(alias.clone(), earlier_value.clone())
            .materialize_named_cell(owner.clone(), alias_value.clone());
        let reloaded = evaluate_logical_memory_load_paths(
            &cached_memory,
            alias.clone(),
            CType::UInt64,
            Vec::new().into(),
            Vec::new(),
            &context,
        );
        let program_reload = evaluate_c_memory_load_paths(
            &cached_memory,
            alias,
            CType::UInt64,
            Vec::new().into(),
            Vec::new(),
            &context,
            true,
            false,
            None,
            None,
        );
        assert_eq!(reloaded.len(), 1);
        assert_eq!(program_reload.len(), 1);
        assert_eq!(reloaded[0].outcome, unrelated[0].outcome);
        assert_eq!(program_reload[0].outcome, reloaded[0].outcome);
        let displaced = evaluate_logical_memory_load_paths(
            &memory,
            owner.offset_by_bytes(8),
            CType::UInt64,
            Vec::new().into(),
            Vec::new(),
            &context,
        );
        assert_ne!(
            displaced[0].outcome, logical[0].outcome,
            "different field offsets must retain different load identities"
        );
    }

    #[test]
    fn logical_read_address_uses_class_index_without_scanning_aliases_or_frames() {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int64(
                Bitvector32Term::Variable(Variable(95_000)),
                1,
                false,
            ),
        };
        let alias = Pointer::symbolic(Variable(95_001));
        let empty = PureFactContext::new();
        let resources = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(
            CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                owner.clone(),
                0u32.into(),
                3u32.into(),
                4,
            )),
        );
        let before = empty.assume_proposition(Proposition::CResourceComposition(resources));
        let mut memory = CMemory::new();
        for offset in [0, 4, 8] {
            memory = memory.store(owner.offset_by_bytes(offset), int32(7));
        }
        let mut samples = Vec::new();
        for size in [4u64, 64, 1024] {
            let mut context = before.clone().assume_condition(
                ConditionTerm::pointer_equal(owner.clone(), alias.clone()),
                true,
            );
            for i in 0..size {
                // Unrelated admitted frames and many names of the selected
                // address must not become a spelling search at the read.
                let frame = ResourceContext::new_with_equalities(&context).unchecked_with_fact(
                    CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                        Pointer::symbolic(Variable(196_000 + i)),
                        0u32.into(),
                        1u32.into(),
                        4,
                    )),
                );
                context = context
                    .assume_proposition(Proposition::CResourceComposition(frame))
                    .assume_condition(
                        ConditionTerm::pointer_equal(
                            alias.clone(),
                            Pointer::symbolic(Variable(297_000 + i)),
                        ),
                        true,
                    );
            }
            let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    for offset in [0, 4, 8] {
                        assert_eq!(
                            logical_memory_load_address(
                                &memory,
                                alias.offset_by_bytes(offset),
                                CType::Int32,
                                &context
                            ),
                            owner.offset_by_bytes(offset)
                        );
                        let paths = evaluate_logical_memory_load_paths(
                            &memory,
                            alias.offset_by_bytes(offset),
                            CType::Int32,
                            Vec::new().into(),
                            Vec::new(),
                            &context,
                        );
                        assert_eq!(paths.len(), 1);
                        assert_eq!(paths[0].outcome, CExpressionOutcome::Value(int32(7)));
                        assert!(paths[0].facts.is_empty());
                        assert!(paths[0].obligations.is_empty());
                    }
                })
            });
            samples.push((work, map_work));
            assert_eq!(
                logical_memory_load_address(&memory, alias.clone(), CType::Int32, &before),
                alias
            );
        }
        assert!(
            samples[2].0 <= samples[0].0 * 3 + 128,
            "address lookup scanned aliases or frames: {samples:?}"
        );
        assert!(
            samples[2].1 <= samples[0].1 * 4 + 256,
            "address lookup copied unrelated indexes: {samples:?}"
        );
        eprintln!("logical read address work: {samples:?}");
    }

    #[test]
    fn logical_scalar_read_reuses_model_cell_through_later_external_alias() {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = Pointer::symbolic(Variable(95_300));
        let alias = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(95_301)), 4),
        };
        let field = owner.offset_by_bytes(8);
        let queried = alias.offset_by_bytes(8);
        let value = CValue::UInt64(Bitvector32Term::UInt64Constant(17));
        let memory = CMemory::new().materialize_named_cell(field.clone(), value.clone());
        let empty = PureFactContext::new();
        let resources = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(
            CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                field.clone(),
                0u32.into(),
                1u32.into(),
                8,
            )),
        );
        let before = empty.assume_proposition(Proposition::CResourceComposition(resources));
        let read = |memory: &CMemory, pointer: Pointer, context: &PureFactContext| {
            let paths = evaluate_logical_memory_load_paths(
                memory,
                pointer,
                CType::UInt64,
                Vec::new().into(),
                Vec::new(),
                context,
            );
            assert_eq!(paths.len(), 1);
            assert!(paths[0].facts.is_empty());
            assert!(paths[0].obligations.is_empty());
            paths[0].outcome.clone()
        };
        let mut samples = Vec::new();
        for size in [8u64, 64, 512] {
            let mut context = before.clone().assume_condition(
                ConditionTerm::pointer_equal(owner.clone(), alias.clone()),
                true,
            );
            for i in 0..size {
                context = context.assume_condition(
                    ConditionTerm::pointer_equal(
                        owner.clone(),
                        Pointer::symbolic(Variable(98_000 + i)),
                    ),
                    true,
                );
            }
            let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    assert_eq!(
                        read(&memory, queried.clone(), &context),
                        CExpressionOutcome::Value(value.clone())
                    );
                    assert_eq!(
                        read(
                            &memory,
                            queried.clone(),
                            &context.clone().keep_spec_loads_symbolic()
                        ),
                        CExpressionOutcome::Value(value.clone())
                    );
                })
            });
            samples.push((work, map_work));
            assert_ne!(
                read(&memory, queried.clone(), &before),
                CExpressionOutcome::Value(value.clone())
            );
            assert_ne!(
                read(&memory, alias.offset_by_bytes(16), &context),
                CExpressionOutcome::Value(value.clone())
            );
            assert!(!ResourceContext::new().permits_memory_read(&queried, 8, &context));
            let changed_value = CValue::UInt64(Bitvector32Term::UInt64Constant(19));
            let changed = memory.clone().store(field.clone(), changed_value.clone());
            assert_eq!(
                read(&changed, queried.clone(), &context),
                CExpressionOutcome::Value(changed_value)
            );
            // An exact newer cell takes precedence over a cached alias.
            let direct_value = CValue::UInt64(Bitvector32Term::UInt64Constant(23));
            let direct = memory.clone().store(queried.clone(), direct_value.clone());
            assert_eq!(
                read(&direct, queried.clone(), &context),
                CExpressionOutcome::Value(direct_value)
            );
        }
        assert!(
            samples[2].0 <= samples[0].0 * 3 + 64,
            "cached coordinate lookup scanned aliases: {samples:?}"
        );
        assert!(
            samples[2].1 <= samples[0].1 * 4 + 128,
            "cached coordinate lookup copied indexes: {samples:?}"
        );
    }

    #[test]
    fn logical_pointer_read_definitions_are_not_hypotheses_or_read_authority() {
        let memory = CMemory::new();
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
            CValue::typed_pointer(Pointer::symbolic(Variable(92_202)), CType::Int64Pointer),
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
    fn pointer_read_premises_register_definitions_before_transitive_queries() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = CMemory::new();
        let snapshot = intern_c_memory_ref(&memory);
        let base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(95_600)), 4),
        };
        let parent = Pointer::symbolic(Variable(95_601));
        let successor = Pointer::symbolic(Variable(95_602));
        let address = base.offset_by_bytes(16);
        let load = canonical_form_of_load(snapshot, address.clone(), LoadKind::Bits32);
        let CValue::Pointer(stored) =
            crate::kernel::cell_run_value(&address, CType::Int64Pointer, load)
        else {
            panic!("pointer field");
        };
        let bare = PureFactContext::new();
        let read = logical_pointer_read(&memory, &parent.offset_by_bytes(16), &bare);
        let base_equality = ConditionTerm::pointer_equal(parent.clone(), base);
        let read_equality =
            ConditionTerm::pointer_equal(stored.pointer().clone(), successor.clone());
        let mut samples = Vec::new();
        for size in [8u64, 32, 128, 512] {
            let mut ambient = bare.clone();
            for i in 0..size {
                ambient = ambient.assume_condition(
                    ConditionTerm::pointer_equal(
                        Pointer::symbolic(Variable(96_600 + i)),
                        Pointer::symbolic(Variable(97_600 + i)),
                    ),
                    true,
                );
            }
            let (context, insertion_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    ambient
                        .clone()
                        .assume_condition(base_equality.clone(), true)
                        .assume_condition(read_equality.clone(), true)
                });
            let ((equal, query_work), map_work) =
                crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        context.pointers_known_equal(&read, &successor)
                    })
                });
            assert!(
                equal,
                "a query must not depend on first comparing the two read spellings"
            );
            samples.push((insertion_work, query_work));
            assert!(
                map_work < 1024 * (size.ilog2() as usize + 1),
                "size={size}, map work={map_work}"
            );
            assert!(!ambient.pointers_known_equal(&read, &successor));
            assert!(
                !ambient
                    .clone()
                    .assume_condition(base_equality.clone(), true)
                    .pointers_known_equal(&read, &successor)
            );
            assert!(
                !ambient
                    .assume_condition(read_equality.clone(), true)
                    .pointers_known_equal(&read, &successor)
            );
            let other = logical_pointer_read(&memory, &parent.offset_by_bytes(24), &bare);
            assert!(!context.pointers_known_equal(&other, &successor));
            let changed = memory.clone().store(
                address.clone(),
                CValue::typed_pointer(Pointer::symbolic(Variable(95_603)), CType::Int64Pointer),
            );
            let replacement = logical_pointer_read(&changed, &address, &context);
            assert!(!context.pointers_known_equal(&replacement, &successor));
            assert!(!ResourceContext::new().permits_memory_read(&address, 8, &context));
        }
        assert!(
            samples.iter().all(
                |(insert, query)| *insert <= samples[0].0 + 100 && *query <= samples[0].1 + 100
            ),
            "read registration scanned unrelated equalities: {samples:?}"
        );
    }

    #[test]
    fn seeded_pointer_cells_retain_their_typed_load_definition() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = CMemory::new();
        let snapshot = intern_c_memory_ref(&memory);
        let base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(95_400)), 4),
        };
        let alias = Pointer::symbolic(Variable(95_401));
        let address = base.offset_by_bytes(16);
        let alias_address = alias.offset_by_bytes(16);
        let load = canonical_form_of_load(snapshot, address.clone(), LoadKind::Bits32);
        let CValue::Pointer(seeded) =
            crate::kernel::cell_run_value(&address, CType::Int64Pointer, load)
        else {
            panic!("seeded pointer");
        };
        let bare = PureFactContext::new();
        let read = logical_pointer_read(&memory, &alias_address, &bare);
        assert!(!bare.pointers_known_equal(seeded.pointer(), &read));
        let mut samples = Vec::new();
        for size in [8u64, 32, 128, 512] {
            for i in 0..size {
                let unrelated = Pointer::symbolic(Variable(96_400 + i)).offset_by_bytes(16);
                let load = canonical_form_of_load(
                    intern_c_memory_ref(&memory),
                    unrelated.clone(),
                    LoadKind::Bits32,
                );
                crate::kernel::cell_run_value(&unrelated, CType::Int64Pointer, load);
            }
            let context = bare.clone().assume_condition(
                ConditionTerm::pointer_equal(base.clone(), alias.clone()),
                true,
            );
            let ((equal, work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    context.pointers_known_equal(seeded.pointer(), &read)
                })
            });
            assert!(equal);
            samples.push(work);
            assert!(
                map_work < 512 * (size.ilog2() as usize + 1),
                "size={size}, map work={map_work}"
            );
            assert!(!bare.pointers_known_equal(seeded.pointer(), &read));
            assert!(!ResourceContext::new().permits_memory_read(&alias_address, 8, &context));
            let other = logical_pointer_read(&memory, &alias.offset_by_bytes(24), &context);
            assert!(!context.pointers_known_equal(seeded.pointer(), &other));
            let changed = memory.clone().store(
                address.clone(),
                CValue::typed_pointer(Pointer::symbolic(Variable(95_402)), CType::Int64Pointer),
            );
            let replacement = logical_pointer_read(&changed, &address, &context);
            assert!(!context.pointers_known_equal(seeded.pointer(), &replacement));
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 40),
            "read definition lookup scanned unrelated cells: {samples:?}"
        );
    }

    #[test]
    fn known_pointer_read_names_require_a_complete_pointer_cell() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = CMemory::new();
        let source = intern_c_memory_ref(&memory);
        let wide = Pointer::symbolic(Variable(210_100));
        let narrow = Pointer::symbolic(Variable(210_101));
        record_load_access_width(&memory, &wide, crate::kernel::C_POINTER_BYTE_WIDTH);
        record_load_access_width(&memory, &narrow, 4);
        let term = |address: &Pointer| {
            Bitvector32Term::MemoryLoad(source.clone(), Box::new(address.clone()), LoadKind::Bits32)
        };
        assert!(known_pointer_read_variable_for_term(&term(&wide)).is_none());
        let (wide_name, _) = load_variable_for_term(&term(&wide)).unwrap();
        let (narrow_name, _) = load_variable_for_term(&term(&narrow)).unwrap();
        assert_eq!(
            known_pointer_read_variable_for_term(&term(&wide)),
            Some(wide_name)
        );
        assert!(known_pointer_read_variable_for_term(&term(&narrow)).is_none());
        let selected = Pointer::symbolic(Variable(210_102));
        for (value, expected) in [
            (
                CValue::Int32(Bitvector32Term::Variable(wide_name)),
                Some(wide_name),
            ),
            (CValue::Int32(Bitvector32Term::Variable(narrow_name)), None),
            (
                CValue::Int32(Bitvector32Term::Variable(Variable(210_103))),
                None,
            ),
            (CValue::UInt64(Bitvector32Term::UInt64Constant(0)), None),
        ] {
            let cached = memory
                .clone()
                .materialize_named_cell(selected.clone(), value);
            let read = Bitvector32Term::MemoryLoad(
                intern_c_memory_ref(&cached),
                Box::new(selected.clone()),
                LoadKind::Bits32,
            );
            assert_eq!(known_pointer_read_variable_for_term(&read), expected);
        }
        let wrong_kind = Bitvector32Term::MemoryLoad(source, Box::new(wide), LoadKind::Bits64);
        assert!(known_pointer_read_variable_for_term(&wrong_kind).is_none());
    }

    /// A selected cached load denotes one pointer even when its cell is
    /// reached through a loop cursor in another symbolic coordinate system.
    #[test]
    fn cached_pointer_value_keeps_its_defining_coordinates_and_scales() {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = Pointer::symbolic(Variable(195_100));
        let cursor = Pointer::symbolic(Variable(195_101));
        let address = owner.offset_by_bytes(16);
        let cursor_address = cursor.offset_by_bytes(16);
        let memory = CMemory::new();
        let snapshot = intern_c_memory_ref(&memory);
        let bits = canonical_form_of_typed_load(snapshot, address.clone(), CType::Int64Pointer)
            .expect("complete pointer read");
        let cached = CValue::Int32(bits);
        let mut samples = Vec::new();
        for count in [16u64, 64, 256, 1024] {
            let mut context = PureFactContext::new().assume_condition(
                ConditionTerm::pointer_equal(owner.clone(), cursor.clone()),
                true,
            );
            for i in 0..count {
                context = context.assume_condition(
                    ConditionTerm::pointer_equal(
                        Pointer::symbolic(Variable(196_000 + i)),
                        Pointer::symbolic(Variable(198_000 + i)),
                    ),
                    true,
                );
            }
            let read = |at: &Pointer| {
                canonicalized_pointer_value_from_int_cell(
                    at,
                    &cached,
                    CType::Int64Pointer,
                    &mut ExecutionFacts::new(),
                    &context,
                    None,
                    LoadPurpose::Program,
                )
                .expect("selected pointer cache")
            };
            let expected = read(&address);
            let ((actual, work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| read(&cursor_address))
            });
            assert_eq!(actual, expected, "alias rebased a cached pointer value");
            samples.push((work, map_work));
            assert!(
                canonicalized_pointer_value_from_int_cell(
                    &cursor_address,
                    &CValue::UInt64(Bitvector32Term::UInt64Constant(0)),
                    CType::Int64Pointer,
                    &mut ExecutionFacts::new(),
                    &context,
                    None,
                    LoadPurpose::Program,
                )
                .is_none(),
                "an arbitrary scalar must not gain pointer identity"
            );
        }
        assert!(
            samples.iter().all(|sample| sample.0 <= samples[0].0 + 32),
            "{samples:?}"
        );
        assert!(
            samples.iter().all(|sample| sample.1 <= samples[0].1 + 128),
            "{samples:?}"
        );
    }

    #[test]
    fn cached_pointer_reads_retain_their_current_cell_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let alias = Pointer::symbolic(Variable(95_510));
        let address = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(95_511)), 4),
        };
        let stored = Pointer::symbolic(Variable(95_512));
        let replacement = Pointer::symbolic(Variable(95_513));
        let empty = PureFactContext::new();
        let mut samples = Vec::new();
        for count in [8u64, 32, 128, 512] {
            let mut memory = CMemory::new().store(
                alias.clone(),
                CValue::typed_pointer(stored.clone(), CType::Int64Pointer),
            );
            let mut context = empty.clone().assume_condition(
                ConditionTerm::pointer_equal(alias.clone(), address.clone()),
                true,
            );
            for index in 0..count {
                memory = memory.store(
                    Pointer {
                        block: PointerBlock::Heap(96_000 + index),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    int32(7),
                );
                context = context.assume_condition(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(97_000 + index)),
                        Bitvector32Term::Constant(7),
                    ),
                    true,
                );
            }
            let snapshot = intern_c_memory_ref(&memory);
            assert_eq!(logical_pointer_read(&memory, &address, &context), stored);

            // A later projection may name the same cell by its scalar load.
            // The checked C pointer read must still denote the cached value.
            let name = canonical_form_of_load(snapshot, address.clone(), LoadKind::Bits32);
            let projected = memory
                .clone()
                .materialize_named_cell(address.clone(), CValue::Int32(name));
            let paths = evaluate_c_memory_load_paths(
                &projected,
                address.clone(),
                CType::Int64Pointer,
                ExecutionFacts::new(),
                Vec::new(),
                &context,
                true,
                false,
                None,
                None,
            );
            let [path] = paths.as_slice() else {
                panic!("one C read expected");
            };
            let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    for fact in &path.facts {
                        fact.retain_pointer_read_definition(&context);
                    }
                })
            });
            samples.push((work, map_work));
            let CExpressionOutcome::Value(CValue::Pointer(checked)) = &path.outcome else {
                panic!("pointer read expected");
            };
            assert!(context.pointers_known_equal(&stored, checked.pointer()));
            assert!(
                !empty.pointers_known_equal(&stored, checked.pointer()),
                "a cache alias is scoped to its checked context"
            );
            let displaced = logical_pointer_read(&memory, &address.offset_by_bytes(8), &context);
            assert!(!context.pointers_known_equal(&stored, &displaced));
            let later = memory.store(
                alias.clone(),
                CValue::typed_pointer(replacement.clone(), CType::Int64Pointer),
            );
            let changed = logical_pointer_read(&later, &address, &context);
            assert_eq!(changed, replacement);
            assert!(!context.pointers_known_equal(&stored, &changed));
            let later_read = Pointer::symbolic(Variable(98_000 + count));
            context.register_checked_pointer_read(
                &later_read,
                &intern_c_memory_ref(&later),
                &address,
            );
            assert!(context.pointers_known_equal(&replacement, &later_read));
            assert!(!context.pointers_known_equal(&stored, &later_read));
        }
        assert!(samples[3].0 <= samples[0].0 * 3 + 128, "{samples:?}");
        assert!(samples[3].1 <= samples[0].1 * 6 + 512, "{samples:?}");
    }

    #[test]
    fn logical_pointer_read_registration_invalidates_an_earlier_memoized_miss() {
        let memory = CMemory::new();
        let a = Pointer::symbolic(Variable(92_210));
        let b = Pointer::symbolic(Variable(92_211));
        let context = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
        let program_read = |address: &Pointer| {
            let paths = evaluate_c_memory_load_paths(
                &memory,
                address.clone(),
                CType::Int64Pointer,
                Vec::new().into(),
                Vec::new(),
                &context,
                true,
                false,
                None,
                None,
            );
            let CExpressionOutcome::Value(CValue::Pointer(value)) = &paths[0].outcome else {
                panic!("pointer read");
            };
            value.pointer().clone()
        };
        let x = program_read(&a);
        let y = program_read(&b);
        let _scope = context.enter_id_scope();
        assert!(!pointers_proven_equal_for_memory_resolution(
            &x, &y, &context
        ));
        // Warm compound-query dependency misses before producer metadata
        // appears. New definitions must invalidate those misses as well.
        for _ in 0..2 {
            assert!(!context.pointers_known_equal(&x.offset_by_bytes(8), &y.offset_by_bytes(8)));
        }
        assert_eq!(logical_pointer_read(&memory, &a, &context), x);
        assert_eq!(logical_pointer_read(&memory, &b, &context), y);
        assert!(pointers_proven_equal_for_memory_resolution(
            &x, &y, &context
        ));
        assert!(context.pointers_known_equal(&x.offset_by_bytes(8), &y.offset_by_bytes(8)));
    }

    #[test]
    fn logical_pointer_read_queries_do_not_scan_unrelated_definitions() {
        let memory = CMemory::new();
        let context = PureFactContext::new();
        let a = Pointer::symbolic(Variable(92_220));
        let b = Pointer::symbolic(Variable(92_221));
        let x = logical_pointer_read(&memory, &a, &context);
        let y = logical_pointer_read(&memory, &b, &context);
        let branch = context.assume_condition(ConditionTerm::pointer_equal(a, b), true);
        assert!(branch.pointers_known_equal(&x, &y));
        for size in [16u64, 64, 256, 1024] {
            for i in 0..size {
                logical_pointer_read(&memory, &Pointer::symbolic(Variable(93_000 + i)), &branch);
            }
            let (equal, work) =
                crate::persistent::measure_persistent_work(|| branch.pointers_known_equal(&x, &y));
            assert!(equal);
            assert!(
                work < 80 * (size.ilog2() as usize + 1),
                "size={size}, map work={work}"
            );
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                branch.pointers_known_equal(&x, &y)
            });
            assert!(equal);
            assert!(work < 40, "size={size}, work={work}");
            let ((equal, work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    branch.pointers_known_equal(&x.offset_by_bytes(8), &y.offset_by_bytes(8))
                })
            });
            assert!(equal);
            assert!(
                work < 100,
                "shifted read scanned definitions: size={size}, work={work}"
            );
            assert!(
                map_work < 200 * (size.ilog2() as usize + 1),
                "shifted read copied definitions: size={size}, work={map_work}"
            );
            // Cold class lookup must resolve one newly produced term without
            // scanning the session's unrelated retained definitions.
            let address = Pointer::symbolic(Variable(94_000 + size));
            let value = logical_pointer_read(&memory, &address, &branch);
            let application = Pointer::loaded_value(&intern_c_memory_ref(&memory), &address);
            let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let class = branch.equality_graph.address_class(&value).unwrap();
                    let other = branch.equality_graph.address_class(&application).unwrap();
                    assert_eq!(branch.equality_graph.address_class_root(class), other);
                })
            });
            assert!(work < 100, "size={size}, work={work}");
            assert!(
                map_work < 512 * (size.ilog2() as usize + 1),
                "size={size}, map work={map_work}"
            );
        }
    }

    #[test]
    fn retained_pointer_cell_uses_one_immutable_full_width_definition() {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = Pointer {
            block: "local:retained-pointer-definition".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = CMemory::new().with_block(cell.block.clone(), C_POINTER_BYTE_WIDTH);
        record_load_access_width(&memory, &cell, C_POINTER_BYTE_WIDTH);
        let first = symbolic_storage_cell_value(&memory, &cell, CType::Int32Pointer, true).unwrap();
        let CValue::Pointer(first) = first else {
            panic!("pointer cell");
        };
        let variable = typed_pointer_read_variable(first.pointer()).unwrap();
        let definition = registered_load_term_for_variable(&variable).unwrap();
        assert_eq!(
            registered_load_bytes_for_variable(&variable),
            Some(C_POINTER_BYTE_WIDTH)
        );
        let retained = memory.materialize_named_cell(
            cell.clone(),
            CValue::typed_pointer(
                Pointer::loaded(cell.block.clone(), Bitvector32Term::Variable(variable), 4),
                CType::Int32Pointer,
            ),
        );
        let CValue::Pointer(second) =
            symbolic_storage_cell_value(&retained, &cell, CType::Int32Pointer, true).unwrap()
        else {
            panic!("retained pointer cell");
        };
        let context = PureFactContext::new();
        let CValue::Pointer(cached) = canonicalized_pointer_value_from_int_cell(
            &cell,
            &CValue::Int32(Bitvector32Term::Variable(variable)),
            CType::Int32Pointer,
            &mut ExecutionFacts::new(),
            &context,
            None,
            LoadPurpose::Logical,
        )
        .unwrap() else {
            panic!("cached pointer cell");
        };
        assert_eq!(first, second);
        assert_eq!(second, cached);
        let Bitvector32Term::MemoryLoad(snapshot, address, _) = definition else {
            panic!("definition");
        };
        assert!(context.pointers_known_equal(
            cached.pointer(),
            &Pointer::loaded_value(&snapshot, &address)
        ));
    }

    #[test]
    fn wider_pointer_naming_rechecks_a_cached_narrow_scalar_source() {
        let _session = crate::kernel::VerificationSession::enter();
        let source = CMemory::new();
        let address = Pointer::symbolic(Variable(92_314));
        let snapshot = intern_c_memory_ref(&source);
        let scalar =
            canonical_form_of_typed_load(snapshot.clone(), address.clone(), CType::Int32).unwrap();
        let Bitvector32Term::Variable(scalar_name) = scalar else {
            panic!("scalar name");
        };
        let seeded = source
            .with_named_cell_run(address.clone(), 4, CType::Int32, 0, 2, snapshot)
            .unwrap();
        let selected = intern_c_memory_ref(&seeded);
        let narrow = canonical_form_of_load(selected.clone(), address.clone(), LoadKind::Bits32);
        assert_eq!(narrow, scalar);
        assert_eq!(registered_load_bytes_for_variable(&scalar_name), Some(4));

        // Keep a different four-byte producer narrow. Only this selected
        // read has gained an actual full-width typed observation.
        let other = Pointer::symbolic(Variable(92_315));
        let other = canonical_form_of_typed_load(selected.clone(), other, CType::Int32).unwrap();
        let Bitvector32Term::Variable(other_name) = other else {
            panic!("other scalar name");
        };
        let full =
            canonical_form_of_typed_load(selected, address.clone(), CType::Int32Pointer).unwrap();
        let Bitvector32Term::Variable(full_name) = full else {
            panic!("complete pointer name");
        };
        assert_eq!(
            registered_load_bytes_for_variable(&full_name),
            Some(C_POINTER_BYTE_WIDTH)
        );
        assert_eq!(registered_load_bytes_for_variable(&other_name), Some(4));
        let CValue::Pointer(value) = canonicalized_pointer_value_from_int_cell(
            &address,
            &CValue::Int32(full),
            CType::Int32Pointer,
            &mut ExecutionFacts::new(),
            &PureFactContext::new(),
            None,
            LoadPurpose::Logical,
        )
        .unwrap() else {
            panic!("pointer value");
        };
        assert!(crate::kernel::memory_provenance::legacy_stored_pointer_read(&value).is_some());
    }

    #[test]
    fn cached_scalar_reads_require_a_complete_pointer_producer() {
        let _session = crate::kernel::VerificationSession::enter();
        let source = CMemory::new();
        let address = Pointer::symbolic(Variable(92_312));
        let snapshot = intern_c_memory_ref(&source);
        let scalar =
            canonical_form_of_typed_load(snapshot.clone(), address.clone(), CType::Int32).unwrap();
        let Bitvector32Term::Variable(scalar_name) = scalar else {
            panic!("scalar read name");
        };
        assert_eq!(registered_load_bytes_for_variable(&scalar_name), Some(4));
        let context = PureFactContext::new();
        let mut facts = ExecutionFacts::new();
        assert!(
            canonicalized_pointer_value_from_int_cell(
                &address,
                &CValue::Int32(scalar.clone()),
                CType::Int32Pointer,
                &mut facts,
                &context,
                None,
                LoadPurpose::Program,
            )
            .is_none()
        );
        assert!(facts.is_empty());
        let narrow = source
            .clone()
            .materialize_named_cell(address.clone(), CValue::Int32(scalar));
        let refused = evaluate_c_memory_load_paths(
            &narrow,
            address.clone(),
            CType::Int32Pointer,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
            false,
            false,
            None,
            None,
        );
        assert!(matches!(
            &refused[0].outcome,
            CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch { .. })
        ));
        assert_eq!(registered_load_bytes_for_variable(&scalar_name), Some(4));

        let foreign_address = Pointer::symbolic(Variable(92_313));
        let foreign =
            canonical_form_of_typed_load(snapshot.clone(), foreign_address.clone(), CType::Int64)
                .unwrap();
        let Bitvector32Term::Variable(foreign_name) = foreign else {
            panic!("wide scalar read name");
        };
        assert_eq!(registered_load_bytes_for_variable(&foreign_name), Some(8));
        assert_eq!(
            registered_load_kind_for_variable(&foreign_name),
            Some(LoadKind::Bits64)
        );
        assert!(
            canonicalized_pointer_value_from_int_cell(
                &foreign_address,
                &CValue::Int32(foreign.clone()),
                CType::Int32Pointer,
                &mut ExecutionFacts::new(),
                &context,
                None,
                LoadPurpose::Logical,
            )
            .is_none()
        );
        let foreign_cache = source
            .clone()
            .materialize_named_cell(foreign_address.clone(), CValue::Int32(foreign.clone()));
        let foreign_snapshot = intern_c_memory_ref(&foreign_cache);
        record_load_access_width(&foreign_snapshot, &foreign_address, C_POINTER_BYTE_WIDTH);
        let pointer_read = Bitvector32Term::MemoryLoad(
            foreign_snapshot,
            Box::new(foreign_address),
            LoadKind::Bits32,
        );
        assert_ne!(
            crate::kernel::memory_provenance::canonicalize_atomic_loads(&pointer_read),
            foreign
        );

        // Naming two unchanged four-byte words does not write their bytes.
        // With authority for a complete pointer read, the existing no-write
        // history supplies that read instead of reinterpreting either word.
        let seeded = source
            .with_named_cell_run(address.clone(), 4, CType::Int32, 0, 2, snapshot)
            .unwrap();
        let read = |memory: &CMemory| {
            let paths = evaluate_c_memory_load_paths(
                memory,
                address.clone(),
                CType::Int32Pointer,
                ExecutionFacts::new(),
                Vec::new(),
                &context,
                true,
                false,
                None,
                None,
            );
            let CExpressionOutcome::Value(CValue::Pointer(value)) = &paths[0].outcome else {
                panic!("complete pointer read: {:?}", paths[0].outcome);
            };
            assert_eq!(
                registered_load_bytes_for_variable(
                    &typed_pointer_read_variable(value.pointer()).unwrap()
                ),
                Some(C_POINTER_BYTE_WIDTH)
            );
            value.clone()
        };
        let before = read(&seeded);
        let after = read(&seeded.store(address.offset_by_bytes(8), int32(17u32)));
        assert_eq!(before, after);
    }

    #[test]
    fn cached_typed_read_retains_exact_definition_without_admitting_facts() {
        let context = PureFactContext::new();
        let address = Pointer::symbolic(Variable(92_310));
        let snapshot = intern_c_memory(CMemory::new());
        record_load_access_width(&snapshot, &address, C_POINTER_BYTE_WIDTH);
        let load = Bitvector32Term::MemoryLoad(
            snapshot.clone(),
            Box::new(address.clone()),
            crate::kernel::LoadKind::Bits32,
        );
        let (variable, _) = load_variable_for_term(&load).expect("load identity");
        let mut facts = crate::kernel::ExecutionFacts::new();
        let source = test_load_source(0);
        let CValue::Pointer(value) = canonicalized_pointer_value_from_int_cell(
            &address,
            &CValue::Int32(Bitvector32Term::Variable(variable)),
            CType::Int64Pointer,
            &mut facts,
            &context,
            Some(&source),
            LoadPurpose::Program,
        )
        .expect("cached typed pointer") else {
            panic!("expected pointer");
        };
        let application = Pointer::loaded_value(&snapshot, &address);
        assert!(!context.pointers_known_equal(value.pointer(), &application));
        assert_eq!(facts.len(), 1);
        let fact = &facts[0];
        assert!(
            matches!(fact.generated_load_binding(), Some(GeneratedLoadBinding::Exact {
            typed_pointer_value: Some(recorded), ..
        }) if recorded == value.pointer())
        );
        assert_eq!(fact.generated_load_source_events().len(), 1);
        assert_eq!(fact.generated_load_source_events()[0].source(), &source);
        assert!(matches!(fact.generated_load_source_events()[0].binding(),
            GeneratedLoadBinding::Exact { typed_pointer_value: Some(recorded), .. }
                if recorded == value.pointer()));
        // An ordinary proposition, even with copied metadata, is not a producer.
        let forged = ExecutionPureFact::new(fact.proposition().clone())
            .with_generated_load_binding(fact.generated_load_binding().unwrap().clone());
        forged.retain_pointer_read_definition(&context);
        assert!(!context.pointers_known_equal(value.pointer(), &application));
        fact.retain_pointer_read_definition(&context);
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
        let later =
            intern_c_memory(CMemory::new().with_block(PointerBlock::from("global:other"), 8));
        assert!(
            !context
                .pointers_known_equal(value.pointer(), &Pointer::loaded_value(&later, &address))
        );
    }

    #[test]
    fn cached_volatile_pointer_read_has_no_retainable_definition() {
        let context = PureFactContext::new();
        let address = Pointer::symbolic(Variable(92_311));
        let snapshot = intern_c_memory(CMemory::new());
        record_load_access_width(&snapshot, &address, C_POINTER_BYTE_WIDTH);
        let load = Bitvector32Term::MemoryLoad(
            snapshot.clone(),
            Box::new(address.clone()),
            crate::kernel::LoadKind::Bits32,
        );
        let (variable, _) = load_variable_for_term(&load).expect("load identity");
        let mut facts = crate::kernel::ExecutionFacts::new();
        let CValue::Pointer(value) = canonicalized_pointer_value_from_int_cell(
            &address,
            &CValue::Int32(Bitvector32Term::Variable(variable)),
            CType::Int64Pointer,
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
        assert!(
            !context
                .pointers_known_equal(value.pointer(), &Pointer::loaded_value(&snapshot, &address))
        );
    }

    #[test]
    fn completed_pointer_reads_join_through_later_graph_address_equality() {
        let memory = CMemory::new();
        let snapshot = intern_c_memory(memory.clone());
        let a = Pointer::symbolic(Variable(92_100));
        let b = Pointer::symbolic(Variable(92_101));
        let read = |address: &Pointer, volatile| {
            let paths = evaluate_c_memory_load_paths(
                &memory,
                address.clone(),
                CType::Int64Pointer,
                Vec::new().into(),
                Vec::new(),
                &PureFactContext::new(),
                true,
                volatile,
                None,
                None,
            );
            assert_eq!(paths.len(), 1);
            let CExpressionOutcome::Value(CValue::Pointer(value)) = &paths[0].outcome else {
                panic!("expected a pointer read: {:?}", paths[0].outcome);
            };
            (value.pointer().clone(), paths[0].facts.clone())
        };
        let (x, x_facts) = read(&a, false);
        let (y, y_facts) = read(&b, false);
        let empty = PureFactContext::new();
        assert!(!empty.pointers_known_equal(&x, &Pointer::loaded_value(&snapshot, &a)));
        let available = x_facts
            .iter()
            .chain(&y_facts)
            .fold(empty.clone(), |context, fact| {
                context.assume_execution_pure_fact(fact)
            });
        assert!(available.pointers_known_equal(&x, &Pointer::loaded_value(&snapshot, &a)));
        assert!(!empty.pointers_known_equal(&x, &y));
        let branch = available
            .clone()
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
        assert!(branch.equality_graph.are_equal(&a, &b));
        assert!(
            branch
                .equality_graph
                .are_pointer_loads_equal(&snapshot, &a, &b)
        );
        assert!(branch.pointers_known_equal(&x, &y));
        let owner = ResourceContext::new_with_equalities(&available).unchecked_with_fact(
            CResourceFact::own_memory(CMemoryRange::new_with_element_width(
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
        // Fork before filing the x read's defining fact. This sibling has
        // the y read and the late address equality, but never received the
        // bridge that would identify x with the loaded pointer.
        let without_x = x_facts
            .iter()
            .skip(1)
            .chain(&y_facts)
            .fold(empty.clone(), |context, fact| {
                context.assume_execution_pure_fact(fact)
            })
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
        assert!(!without_x.pointers_known_equal(&x, &Pointer::loaded_value(&snapshot, &a)));
        assert!(!owner.permits_memory_read(&y, 4, &without_x));
        let address_only = empty
            .clone()
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b), true);
        assert!(!address_only.pointers_known_equal(&x, &Pointer::loaded_value(&snapshot, &a)));
        let later = intern_c_memory(
            memory
                .clone()
                .with_block(PointerBlock::from("global:later"), 8),
        );
        assert!(!available.pointers_known_equal(&x, &Pointer::loaded_value(&later, &a)));
        let volatile_address = Pointer::symbolic(Variable(92_102));
        let (volatile_value, volatile_facts) = read(&volatile_address, true);
        let volatile_context = volatile_facts.iter().fold(empty, |context, fact| {
            context.assume_execution_pure_fact(fact)
        });
        assert!(!volatile_context.pointers_known_equal(
            &volatile_value,
            &Pointer::loaded_value(&snapshot, &volatile_address),
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
        assert_eq!(normal_only.condition_facts, volatile_only.condition_facts);
        assert_ne!(
            normal_only.memo_fingerprint(),
            volatile_only.memo_fingerprint()
        );
        assert_ne!(normal_only, volatile_only);
        assert!(
            !volatile_only
                .pointers_known_equal(&volatile_same, &Pointer::loaded_value(&snapshot, &a),)
        );
        let scalar_paths = evaluate_c_memory_load_paths(
            &memory,
            a.clone(),
            CType::Int64,
            Vec::new().into(),
            Vec::new(),
            &PureFactContext::new(),
            true,
            false,
            None,
            None,
        );
        assert_eq!(scalar_paths.len(), 1);
        let scalar_only = scalar_paths[0]
            .facts
            .iter()
            .fold(PureFactContext::new(), |context, fact| {
                context.assume_execution_pure_fact(fact)
            });
        assert!(!scalar_only.pointers_known_equal(&x, &Pointer::loaded_value(&snapshot, &a)));
    }
    #[test]
    fn stored_pointer_read_preserves_blocks_and_ignores_unrelated_cells() {
        let mut samples = Vec::new();
        for count in [16, 64, 256] {
            let context = PureFactContext::new();
            let address = Pointer::symbolic(Variable(97_001));
            let stored = Pointer::symbolic(Variable(97_002));
            let wrong = Pointer::symbolic(Variable(97_003));
            let mut memory = CMemory::new();
            for index in 1..=count {
                memory = memory.store(
                    address.offset_by_bytes(index * 8),
                    CValue::Int64(Bitvector32Term::Int64Constant(i64::from(index))),
                );
            }
            memory = memory.store(
                address.clone(),
                CValue::typed_pointer(stored.clone(), CType::Int64Pointer),
            );
            let projected = memory;
            let read = Pointer::symbolic(Variable(98_000 + u64::from(count)));
            record_load_access_width(&projected, &address, 8);
            context.register_pointer_read(&read, &intern_c_memory(projected.clone()), &address);
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::memory_provenance::pointer_read_has_stored_value(
                    &read, &stored, &context,
                )
            });
            assert!(equal);
            assert!(
                !crate::kernel::memory_provenance::pointer_read_has_stored_value(
                    &read, &wrong, &context
                )
            );
            assert!(
                !crate::kernel::memory_provenance::pointer_read_has_stored_value(
                    &read.offset_by_bytes(8),
                    &stored,
                    &context
                )
            );
            let changed = projected
                .without_possible_aliasing_cells(&address.offset_by_bytes(4), 4, &context)
                .store(
                    address.offset_by_bytes(4),
                    CValue::Int32(Bitvector32Term::Constant(0)),
                );
            let changed_read = Pointer::symbolic(Variable(99_000 + u64::from(count)));
            record_load_access_width(&changed, &address, 8);
            context.register_pointer_read(&changed_read, &intern_c_memory(changed), &address);
            assert!(
                !crate::kernel::memory_provenance::pointer_read_has_stored_value(
                    &changed_read,
                    &stored,
                    &context
                )
            );
            samples.push(work);
        }
        assert!(samples[2] <= samples[0] * 4 + 32, "{samples:?}");
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
        let memory = CMemory::new().store(
            address.clone(),
            CValue::typed_pointer(stored.clone(), CType::Int32Pointer),
        );
        let read = |memory: CMemory, address: &Pointer, variable, width| {
            record_load_access_width(&memory, address, width);
            let value = Pointer::symbolic(Variable(variable));
            empty.register_pointer_read(&value, &intern_c_memory(memory), address);
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
                CValue::Int32(Bitvector32Term::Constant(0)),
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
            CMemory::new().store(
                narrow_address.clone(),
                CValue::typed_pointer(stored, CType::Int32Pointer),
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
            CMemory::new().store(
                scalar_address.clone(),
                CValue::UInt64(Bitvector32Term::UInt64Constant(0)),
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

    /// The selected read does not scan unrelated cached cells, and a failed
    /// history search stops at a fixed number of edges as history grows.
    #[test]
    fn recorded_pointer_normalization_has_bounded_history_work() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer {
            block: "bounded-pointer-normalization".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let stored = Pointer::symbolic(Variable(99_120));
        let assumptions = PureFactContext::new();
        // The first query includes cold graph registration. Larger inputs
        // may reuse it, but must never exceed that constant work bound.
        let mut known_work = None;
        let mut missing_work = None;
        let mut offset_work = None;
        for count in [64, 256, 1024] {
            let mut memory = CMemory::new().with_block("bounded-pointer-normalization", 16384);
            for index in 1..=count {
                memory = memory.store(
                    address.offset_by_bytes(index * 8),
                    CValue::UInt64(Bitvector32Term::UInt64Constant(u64::from(index))),
                );
            }
            let read = Pointer::symbolic(Variable(99_200 + u64::from(count)));
            record_load_access_width(&memory, &address, 8);
            assumptions.register_pointer_read(&read, &intern_c_memory(memory.clone()), &address);
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::memory_provenance::pointer_read_has_recorded_value(
                    &read,
                    &stored,
                    &assumptions,
                )
            });
            assert!(!equal);
            if let Some(previous) = missing_work {
                assert!(work <= previous, "count={count}: {work} > {previous}");
            }
            missing_work.get_or_insert(work);
            let memory = memory.store(
                address.clone(),
                CValue::typed_pointer(stored.clone(), CType::Int32Pointer),
            );
            let read = Pointer::loaded(
                PointerBlock::ExternalArgument,
                Bitvector32Term::Variable(Variable(101_000 + u64::from(count))),
                4,
            );
            record_load_access_width(&memory, &address, 8);
            let memory = intern_c_memory(memory);
            assumptions.register_pointer_read(&read, &memory, &address);
            for index in 0..count {
                let unrelated = Pointer::loaded(
                    PointerBlock::ExternalArgument,
                    Bitvector32Term::Variable(Variable(
                        120_000 + u64::from(count) * 2048 + u64::from(index),
                    )),
                    4,
                );
                assumptions.register_pointer_read(&unrelated, &memory, &address);
            }
            let (offset_equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::memory_provenance::pointer_offset_read_has_recorded_value(
                    &read.offset,
                    &stored.offset,
                    &assumptions,
                )
            });
            assert!(offset_equal);
            if let Some(previous) = offset_work {
                assert!(work <= previous, "count={count}: {work} > {previous}");
            }
            offset_work.get_or_insert(work);
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::memory_provenance::pointer_read_has_recorded_value(
                    &read,
                    &stored,
                    &assumptions,
                )
            });
            assert!(equal);
            if let Some(previous) = known_work {
                assert!(work <= previous, "count={count}: {work} > {previous}");
            }
            known_work.get_or_insert(work);
        }
    }
    /// Same-block pointer equality is lowered to offset equality. It still
    /// needs an exact typed read, including its stride and unambiguous origin.
    #[test]
    fn normalize_recorded_pointer_offsets_checks_definition_and_stride() {
        use crate::kernel::proof::ProofFacts;
        use crate::kernel::proof::fact_reasoning::normalize_using_conditions;
        let _session = crate::kernel::VerificationSession::enter();
        let context = PureFactContext::new();
        let facts = ProofFacts::from_ordered(&[]);
        let address = Pointer::symbolic(Variable(103_001));
        let stored = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(103_002)),
            4,
        );
        let read = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(103_003)),
            4,
        );
        let memory = CMemory::new().store(
            address.clone(),
            CValue::typed_pointer(stored.clone(), CType::Int32Pointer),
        );
        record_load_access_width(&memory, &address, 8);
        context.register_pointer_read(&read, &intern_c_memory(memory.clone()), &address);
        let equality = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
            Proposition::ConditionIs(
                ConditionTerm::pointer_offset_equal(left.clone(), right.clone()),
                true,
            )
        };
        for goal in [
            equality(&read.offset, &stored.offset),
            equality(&stored.offset, &read.offset),
        ] {
            assert!(normalize_using_conditions(&goal, &[], &facts).is_ok());
        }
        let wrong_stride = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(103_003)),
            8,
        );
        assert!(
            normalize_using_conditions(
                &equality(&wrong_stride.offset, &stored.offset),
                &[],
                &facts
            )
            .is_err()
        );
        assert!(
            normalize_using_conditions(
                &equality(&read.offset_by_bytes(4).offset, &stored.offset),
                &[],
                &facts
            )
            .is_err()
        );
        let wrong_value = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(103_004)),
            4,
        );
        assert!(
            normalize_using_conditions(&equality(&read.offset, &wrong_value.offset), &[], &facts)
                .is_err()
        );
        let partial = memory
            .without_possible_aliasing_cells(&address.offset_by_bytes(4), 4, &context)
            .store(
                address.offset_by_bytes(4),
                CValue::Int32(Bitvector32Term::Constant(0)),
            );
        let changed = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(103_005)),
            4,
        );
        record_load_access_width(&partial, &address, 8);
        context.register_pointer_read(&changed, &intern_c_memory(partial), &address);
        assert!(
            normalize_using_conditions(&equality(&changed.offset, &stored.offset), &[], &facts)
                .is_err()
        );
        // The same offset shape registered in a different block must not let
        // the last registration choose between two incompatible definitions.
        let conflict = Pointer {
            block: "conflicting-offset-origin".into(),
            offset: read.offset.clone(),
        };
        let conflicting_memory = CMemory::new().store(
            address.clone(),
            CValue::typed_pointer(wrong_value, CType::Int32Pointer),
        );
        record_load_access_width(&conflicting_memory, &address, 8);
        context.register_pointer_read(&conflict, &intern_c_memory(conflicting_memory), &address);
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_for_offset(&read.offset).is_none()
        );
        assert!(
            normalize_using_conditions(&equality(&read.offset, &stored.offset), &[], &facts)
                .is_err()
        );
    }
    /// Canonical read snapshots retain an exact projection edge back to the
    /// execution source. The selected alias is still required to find its store.
    #[test]
    fn normalize_recorded_pointer_value_follows_exact_projection_source() {
        use crate::kernel::proof::ProofFacts;
        use crate::kernel::proof::fact_reasoning::normalize_using_conditions;
        let _session = crate::kernel::VerificationSession::enter();
        let context = PureFactContext::new();
        let address = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(104_001)),
            4,
        );
        let written = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(104_002)),
            4,
        );
        let stored = Pointer::symbolic(Variable(104_003));
        let source = CMemory::new()
            .with_block_without_derivation("local:projection", 4)
            .store(
                written.clone(),
                CValue::typed_pointer(stored.clone(), CType::Int32Pointer),
            );
        record_load_access_width(&source, &address, 8);
        let source = intern_c_memory(source);
        let original = Bitvector32Term::MemoryLoad(
            source.clone(),
            Box::new(address.clone()),
            LoadKind::Bits32,
        );
        let projected = crate::kernel::memory_provenance::canonicalize_atomic_loads_deep(&original);
        let Bitvector32Term::MemoryLoad(projected, _, _) = projected else {
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
}
