use super::*;

pub(crate) fn c_checked_function_proposition_with_reason(
    function: &CFunction,
    specification: &CFunctionSpecification,
    theorem: &Theorem,
    completion: &crate::kernel::proof::CheckedProposition,
    path: &SymbolicCExecutionPath,
) -> Result<CCheckedFunctionProposition, String> {
    fn conclusion(theorem: &Theorem) -> &Proposition {
        let mut proposition = theorem.proposition();
        while let Proposition::Implies(_, body) = proposition {
            proposition = body;
        }
        proposition
    }
    match conclusion(theorem) {
        Proposition::CFunctionSatisfiesSpecification {
            function: proved_function,
            specification: proved_specification,
        }
        | Proposition::CFunctionPartiallySatisfiesSpecification {
            function: proved_function,
            specification: proved_specification,
        } if **proved_function == *function && proved_specification.as_ref() == specification => {}
        _ => {
            return Err(
                "the completion theorem does not certify the requested specification".to_string(),
            );
        }
    }
    // The origin is evidence for this exact checked path, never an arbitrary
    // caller-supplied snapshot. Its producer checked the body against its
    // retained trace and applied the contract exit rule to that same trace.
    match conclusion(path.theorem()) {
        Proposition::CFunctionVerifies {
            state,
            function: proved_function,
            arguments,
            outcome,
        } if **state == *specification.state()
            && **proved_function == *function
            && arguments == specification.arguments()
            && outcome == specification.outcome() => {}
        _ => {
            return Err(
                "the checked path does not produce the requested specification outcome".to_string(),
            );
        }
    }
    let completed = completion
        .outcome()
        .ok_or_else(|| "the proposition completion has no concrete function outcome".to_string())?;
    let exceptional = match specification.outcome() {
        CFunctionOutcome::Return { .. } => false,
        CFunctionOutcome::Throw { .. } => true,
        CFunctionOutcome::VerificationDiverges => {
            return Err("the checked path outcome is verification divergence".to_string());
        }
        CFunctionOutcome::UndefinedBehavior(_) => {
            return Err("the checked path outcome is undefined behavior".to_string());
        }
        CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(message)) => {
            return Err(format!(
                "the checked path outcome is a function-contract runtime error: {message}"
            ));
        }
        CFunctionOutcome::RuntimeError(error) => {
            return Err(format!(
                "the checked path outcome is a runtime error: {}",
                super::describe_certification_runtime_error(error)
            ));
        }
    };
    if completed.is_exceptional != exceptional {
        return Err(
            "the proposition completion has the wrong exceptional outcome kind".to_string(),
        );
    }
    let matches_program_state = |outcome: &CFunctionOutcome| {
        let (value, state, exceptional) = match outcome {
            CFunctionOutcome::Return { value, state } => (value, state, false),
            CFunctionOutcome::Throw { value, state } => (value, state, true),
            _ => return false,
        };
        completed.is_exceptional == exceptional
            && completed.result.as_ref() == value
            && completed.state.memory() == state.memory()
            && completed.state.locals() == state.locals()
            && completed.state.typed_access_policy() == state.typed_access_policy()
            && completed.state.aggregate_destination == state.aggregate_destination
    };
    // Resource/population representation can change at exit. Aggregate return
    // completion can also retain the body's sparse block layout, while the
    // exit rule restores the caller's layout. Only the producer's checked
    // correspondence admits that difference; memory contents are never erased
    // or matched by source spelling. A state-embedded proposition still must
    // match the exact contract lowering when this evidence is consumed.
    if !matches_program_state(specification.outcome())
        && !path
            .completion_origin
            .as_ref()
            .is_some_and(matches_program_state)
    {
        return Err(
            "the proposition completion does not match the checked program state".to_string(),
        );
    }
    Ok(CCheckedFunctionProposition {
        function: function.clone(),
        specification: specification.clone(),
        proposition: completion.proposition().clone(),
        claim: completion.claim().cloned(),
    })
}

pub fn c_function_outcomes_definitionally_equal(
    function: &CFunction,
    left: &CFunctionOutcome,
    right: &CFunctionOutcome,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (
            CFunctionOutcome::Return {
                value: _,
                state: left_state,
            },
            CFunctionOutcome::Return {
                value: _,
                state: right_state,
            },
        ) => {
            if !c_function_outcomes_program_state_definitionally_equal(left, right, assumptions) {
                return false;
            }
            resource_context_definitionally_contains(
                left_state.resources(),
                right_state.resources(),
                function.composite_resource_definitions(),
                left_state.memory(),
                assumptions,
            ) || resource_context_definitionally_contains(
                right_state.resources(),
                left_state.resources(),
                function.composite_resource_definitions(),
                left_state.memory(),
                assumptions,
            ) || resource_contexts_definitionally_equal(
                function,
                left_state.memory(),
                left_state.resources(),
                right_state.memory(),
                right_state.resources(),
                assumptions,
            )
        }
        _ => left == right,
    }
}

/// Compares the observable program portion of two outcomes, leaving ghost
/// resource representation to the definitional resource checks.
pub fn c_function_outcomes_program_state_definitionally_equal(
    left: &CFunctionOutcome,
    right: &CFunctionOutcome,
    assumptions: &PureFactContext,
) -> bool {
    match (left, right) {
        (
            CFunctionOutcome::Return {
                value: left_value,
                state: left_state,
            },
            CFunctionOutcome::Return {
                value: right_value,
                state: right_state,
            },
        ) => {
            left_state.typed_access_policy() == right_state.typed_access_policy()
                && c_values_proven_equal_for_memory_resolution(left_value, right_value, assumptions)
                && c_memories_definitionally_equal(
                    left_state.memory(),
                    right_state.memory(),
                    assumptions,
                )
        }
        _ => left == right,
    }
}

/// Proves two return outcomes equal from matching certified execution
/// histories. This recognizes equal store chains and alpha-equivalent call
/// havoc snapshots without treating unrelated fresh havoc identities as
/// interchangeable.
pub fn c_function_outcomes_equal_by_execution_provenance(
    function: &CFunction,
    left: &CFunctionOutcome,
    left_facts: &(impl ExecutionFactSource + ?Sized),
    right: &CFunctionOutcome,
    right_facts: &(impl ExecutionFactSource + ?Sized),
    assumptions: &PureFactContext,
) -> bool {
    if !c_function_outcomes_program_state_equal_by_execution_provenance(
        left,
        left_facts,
        right,
        right_facts,
        assumptions,
    ) {
        return false;
    }
    let (
        CFunctionOutcome::Return {
            state: left_state, ..
        },
        CFunctionOutcome::Return {
            state: right_state, ..
        },
    ) = (left, right)
    else {
        return false;
    };
    resource_context_definitionally_contains(
        left_state.resources(),
        right_state.resources(),
        function.composite_resource_definitions(),
        left_state.memory(),
        assumptions,
    ) || resource_context_definitionally_contains(
        right_state.resources(),
        left_state.resources(),
        function.composite_resource_definitions(),
        left_state.memory(),
        assumptions,
    ) || resource_contexts_definitionally_equal(
        function,
        left_state.memory(),
        left_state.resources(),
        right_state.memory(),
        right_state.resources(),
        assumptions,
    )
}

/// Compares the observable program state of two return paths by matching their
/// certified execution histories. Resource representation remains the
/// responsibility of the separate resource certificate.
pub fn c_function_outcomes_program_state_equal_by_execution_provenance(
    left: &CFunctionOutcome,
    left_facts: &(impl ExecutionFactSource + ?Sized),
    right: &CFunctionOutcome,
    right_facts: &(impl ExecutionFactSource + ?Sized),
    assumptions: &PureFactContext,
) -> bool {
    let (
        CFunctionOutcome::Return {
            value: left_value,
            state: left_state,
        },
        CFunctionOutcome::Return {
            value: right_value,
            state: right_state,
        },
    ) = (left, right)
    else {
        return false;
    };
    left_state.typed_access_policy() == right_state.typed_access_policy()
        && memories_equal_by_execution_provenance(
            left_state.memory(),
            left_facts,
            right_state.memory(),
            right_facts,
            assumptions,
        )
        && c_values_proven_equal_for_memory_resolution(left_value, right_value, assumptions)
}

fn memories_equal_by_execution_provenance(
    left_final: &CMemory,
    left_facts: &(impl ExecutionFactSource + ?Sized),
    right_final: &CMemory,
    right_facts: &(impl ExecutionFactSource + ?Sized),
    assumptions: &PureFactContext,
) -> bool {
    if memories_equal_by_matching_derivations(left_final, right_final, assumptions) {
        return true;
    }
    let left_stores = left_facts
        .fact_iter()
        .filter_map(ExecutionPureFact::certified_store_data)
        .collect::<Vec<_>>();
    let right_stores = right_facts
        .fact_iter()
        .filter_map(ExecutionPureFact::certified_store_data)
        .collect::<Vec<_>>();
    if left_stores.is_empty() || left_stores.len() != right_stores.len() {
        return false;
    }
    let chain_reaches_final = |stores: &[&CertifiedMemoryStore], final_memory: &CMemory| {
        stores.windows(2).all(|pair| {
            c_memories_definitionally_equal(&pair[0].after, &pair[1].before, assumptions)
        }) && c_memories_definitionally_equal(
            &stores.last().expect("store chain is nonempty").after,
            final_memory,
            assumptions,
        )
    };
    c_memories_definitionally_equal(&left_stores[0].before, &right_stores[0].before, assumptions)
        && chain_reaches_final(&left_stores, left_final)
        && chain_reaches_final(&right_stores, right_final)
        && left_stores.iter().zip(&right_stores).all(|(left, right)| {
            (pointers_proven_equal_for_memory_resolution(
                &left.pointer,
                &right.pointer,
                assumptions,
            ) || (left.pointer.block == right.pointer.block
                && c_pointer_offsets_proven_equal_for_effect(
                    &left.pointer.offset,
                    &right.pointer.offset,
                    assumptions,
                )))
                && c_values_proven_equal_for_memory_resolution(
                    &left.value,
                    &right.value,
                    assumptions,
                )
        })
}

/// Two memories are equal when their derivation chains match edge by
/// edge down to a definitionally equal pair. Each step descends one side's
/// `base`, whose id is strictly smaller, so the recursion is finite with
/// no depth cut.
fn memories_equal_by_matching_derivations(
    left: &CMemory,
    right: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    matching_recomputed_call_havoc_views(left, right, assumptions).is_some()
}

/// Matches two recomputed memory histories and returns the exact pairs of call
/// result snapshots encountered on the successful path. Execution-proof
/// construction uses these pairs to register another concrete view of an
/// already checked call event; the pairs themselves are never authority.
pub(crate) fn matching_recomputed_call_havoc_views(
    left: &CMemory,
    right: &CMemory,
    assumptions: &PureFactContext,
) -> Option<Vec<(SharedCMemory, SharedCMemory)>> {
    fn transparent_base(derivation: &CMemoryDerivation) -> Option<&SharedCMemory> {
        match derivation {
            CMemoryDerivation::Store {
                base,
                pointer,
                value,
                ..
            } if pointer.block.starts_with("local:")
                || store_is_self_materialization(base, pointer, value) =>
            {
                Some(base)
            }
            CMemoryDerivation::BlockDeclared { base, block } if block.starts_with("local:") => {
                Some(base)
            }
            CMemoryDerivation::ContractAllocationClaimsChanged { base } => Some(base),
            CMemoryDerivation::CellsForgotten { base } => Some(base),
            _ => None,
        }
    }
    /// A store whose value is the base memory's own load at the stored
    /// pointer is a no-op: the produced memory denotes the same state as its
    /// base, differing only in which cells are materialized. Proof execution
    /// mints such edges when a tactic forces a symbolic load into a concrete
    /// cell, and independent certification never does, so chain matching
    /// must see through them. Purely structural — the load's memory operand
    /// must be the base itself (by interned identity), no proving.
    fn store_is_self_materialization(
        base: &SharedCMemory,
        pointer: &Pointer,
        value: &CValue,
    ) -> bool {
        let (CValue::Int8(Bitvector32Term::MemoryLoad(load_memory, load_pointer, kind))
        | CValue::Int16(Bitvector32Term::MemoryLoad(load_memory, load_pointer, kind))
        | CValue::Int32(Bitvector32Term::MemoryLoad(load_memory, load_pointer, kind))
        | CValue::UInt8(Bitvector32Term::MemoryLoad(load_memory, load_pointer, kind))
        | CValue::UInt16(Bitvector32Term::MemoryLoad(load_memory, load_pointer, kind))
        | CValue::UInt32(Bitvector32Term::MemoryLoad(load_memory, load_pointer, kind))
        | CValue::Int64(Bitvector32Term::MemoryLoad(load_memory, load_pointer, kind))
        | CValue::UInt64(Bitvector32Term::MemoryLoad(load_memory, load_pointer, kind))) = value
        else {
            return false;
        };
        // Storing a read back is a no-op only when it is the cell's own read:
        // a narrower or differently signed read changes the cell.
        load_pointer.as_ref() == pointer
            && kind.reads_value(value)
            && intern_c_memory_ref(load_memory).arena_id() == base.arena_id()
    }
    fn match_inner(
        left: &CMemory,
        right: &CMemory,
        assumptions: &PureFactContext,
        views: &mut Vec<(SharedCMemory, SharedCMemory)>,
    ) -> bool {
        if c_memories_definitionally_equal(left, right, assumptions) {
            return true;
        }
        let left = intern_c_memory_ref(left);
        let right = intern_c_memory_ref(right);
        let left_derivation = left.derivation();
        let right_derivation = right.derivation();
        if let Some(base) = left_derivation.as_deref().and_then(transparent_base) {
            return match_inner(base, &right, assumptions, views);
        }
        if let Some(base) = right_derivation.as_deref().and_then(transparent_base) {
            return match_inner(&left, base, assumptions, views);
        }
        match (left_derivation.as_deref(), right_derivation.as_deref()) {
            (
                Some(CMemoryDerivation::CallHavoc {
                    base: left_base,
                    mutable_ranges: left_ranges,
                    ..
                }),
                Some(CMemoryDerivation::CallHavoc {
                    base: right_base,
                    mutable_ranges: right_ranges,
                    ..
                }),
            ) => {
                if !memory_range_lists_definitionally_equal(left_ranges, right_ranges, assumptions)
                    || !match_inner(left_base, right_base, assumptions, views)
                {
                    return false;
                }
                views.push((left, right));
                true
            }
            (
                Some(CMemoryDerivation::LoopHavoc {
                    base: left_base,
                    mutable_ranges: left_ranges,
                    ..
                }),
                Some(CMemoryDerivation::LoopHavoc {
                    base: right_base,
                    mutable_ranges: right_ranges,
                    ..
                }),
            ) => {
                let ranges_match = match (left_ranges, right_ranges) {
                    (Some(left_ranges), Some(right_ranges)) => {
                        memory_range_lists_definitionally_equal(
                            left_ranges,
                            right_ranges,
                            assumptions,
                        )
                    }
                    (None, None) => true,
                    _ => false,
                };
                ranges_match && match_inner(left_base, right_base, assumptions, views)
            }
            (
                Some(CMemoryDerivation::Store {
                    base: left_base,
                    pointer: left_pointer,
                    value: left_value,
                    ..
                }),
                Some(CMemoryDerivation::Store {
                    base: right_base,
                    pointer: right_pointer,
                    value: right_value,
                    ..
                }),
            ) => {
                pointers_proven_equal_for_memory_resolution(
                    left_pointer,
                    right_pointer,
                    assumptions,
                ) && c_values_proven_equal_for_memory_resolution(
                    left_value,
                    right_value,
                    assumptions,
                ) && match_inner(left_base, right_base, assumptions, views)
            }
            // Two seeded runs are two sequences of stores, matched store for
            // store as above.
            (
                Some(
                    left_seeded @ CMemoryDerivation::CellsSeeded {
                        base: left_base, ..
                    },
                ),
                Some(
                    right_seeded @ CMemoryDerivation::CellsSeeded {
                        base: right_base, ..
                    },
                ),
            ) => {
                let (Some(left_stores), Some(right_stores)) =
                    (left_seeded.seeded_stores(), right_seeded.seeded_stores())
                else {
                    return false;
                };
                left_stores.len() == right_stores.len()
                    && left_stores.iter().zip(&right_stores).all(
                        |((left_pointer, left_value), (right_pointer, right_value))| {
                            pointers_proven_equal_for_memory_resolution(
                                left_pointer,
                                right_pointer,
                                assumptions,
                            ) && c_values_proven_equal_for_memory_resolution(
                                left_value,
                                right_value,
                                assumptions,
                            )
                        },
                    )
                    && match_inner(left_base, right_base, assumptions, views)
            }
            _ => false,
        }
    }

    let mut views = Vec::new();
    match_inner(left, right, assumptions, &mut views).then_some(views)
}

fn memory_range_lists_definitionally_equal(
    left: &[CMemoryRange],
    right: &[CMemoryRange],
    assumptions: &PureFactContext,
) -> bool {
    left.len() == right.len()
        && left.iter().zip(right).all(|(left, right)| {
            // Wide endpoints currently require exact structural equality;
            // the residual equality oracle below has signed 32-bit semantics.
            left == right
                || (left.int32_bounds().is_some()
                    && right.int32_bounds().is_some()
                    && left.element_width() == right.element_width()
                    && pointers_proven_equal_for_memory_resolution(
                        left.base(),
                        right.base(),
                        assumptions,
                    )
                    && int32_values_proven_equal_for_memory_resolution(
                        left.start(),
                        right.start(),
                        assumptions,
                    )
                    && int32_values_proven_equal_for_memory_resolution(
                        left.end(),
                        right.end(),
                        assumptions,
                    ))
        })
}

#[cfg(test)]
mod range_list_equality_graph_tests {
    use super::*;

    fn var(id: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(id))
    }

    #[test]
    fn certified_range_list_endpoints_use_graph_with_snapshot_scope() {
        let _session = crate::kernel::VerificationSession::enter();
        let before = crate::kernel::intern_c_memory(CMemory::new().with_block("range-list", 8));
        let pointer = |index| Pointer {
            block: "range-list".into(),
            offset: PointerOffsetTerm::scale_int32(index, 4),
        };
        let load = |memory: &SharedCMemory, index| {
            Bitvector32Term::Variable(crate::kernel::load_variable_for_cell_with_origin(
                memory,
                &pointer(index),
                crate::kernel::LoadKind::Bits32,
                4,
                memory,
            ))
        };
        let (a, b) = (var(91), var(92));
        let after = crate::kernel::intern_c_memory(before.memory().clone().store(
            pointer(b.clone()),
            CValue::Int32(Bitvector32Term::Constant(9)),
        ));
        let base = Pointer::symbolic(Variable(9100));
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let range = |start| CMemoryRange::new(base.clone(), start, Bitvector32Term::Constant(16));
        let left = range(sum(load(&before, a.clone())));
        let right = range(sum(load(&before, b.clone())));
        let later = range(sum(load(&after, b.clone())));
        let premise = ConditionTerm::equal(a, b);
        let parent = PureFactContext::new();
        let branch = parent.clone().assume_condition(premise.clone(), true);
        let matches = |context: &PureFactContext, right: &CMemoryRange| {
            memory_range_lists_definitionally_equal(
                std::slice::from_ref(&left),
                std::slice::from_ref(right),
                context,
            )
        };
        let _scope = branch.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        assert!(matches(&branch, &right));
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(!matches(&branch, &later));
        assert!(!matches(&parent, &right));
        let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(premise, true));
        assert!(!matches(&withdrawn, &right));
        assert!(!matches(
            &branch,
            &CMemoryRange::new_with_element_width(
                base,
                right.start().clone(),
                right.end().clone(),
                1,
            ),
        ));
    }

    #[test]
    fn certified_range_list_graph_queries_scale_without_fact_index() {
        for size in [16u64, 64, 256, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let base = Pointer::symbolic(Variable(9200));
            let range = |value| {
                CMemoryRange::new(
                    base.clone(),
                    Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
                    Bitvector32Term::Constant(16),
                )
            };
            let left = range(var(0));
            let mut context = PureFactContext::new();
            for index in 0..size {
                context = context
                    .assume_condition(ConditionTerm::equal(var(index), var(index + 1)), true);
            }
            let _scope = context.enter_id_scope();
            PureFactContext::reset_bitvector_equality_index_fact_visits();
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                for index in 1..=size {
                    let right = range(var(index));
                    assert!(memory_range_lists_definitionally_equal(
                        std::slice::from_ref(&left),
                        std::slice::from_ref(&right),
                        &context,
                    ));
                }
            });
            assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
            assert!(work < 300 * size as usize, "size={size}, work={work}");
        }
    }
}

/// Whether two memory snapshots have the same heap status and are the same
/// program state, up to definitional equality of the terms in their cells.
///
/// The `local:` blocks this skips are the ones
/// [`local_block_no_pointer_can_reach`] allows a pointerless comparison to
/// skip, and that function carries the argument. This is the certification
/// side of one rule, so it must select cells and blocks with exactly that
/// filter and nothing wider.
pub(in crate::kernel) fn c_memories_definitionally_equal(
    left: &CMemory,
    right: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    if left.heap != right.heap {
        return false;
    }
    if memories_proven_equal_for_memory_resolution(left, right, assumptions) {
        return true;
    }
    if !left
        .blocks
        .iter()
        .filter(|(block, _)| !local_block_no_pointer_can_reach(block))
        .eq(right
            .blocks
            .iter()
            .filter(|(block, _)| !local_block_no_pointer_can_reach(block)))
    {
        return false;
    }
    if left.forgotten.ended_local_blocks != right.forgotten.ended_local_blocks {
        return false;
    }
    memory_cells_definitionally_contained(left, right, assumptions)
        && memory_cells_definitionally_contained(right, left, assumptions)
}

fn memory_cells_definitionally_contained(
    source: &CMemory,
    target: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    for (source_pointer, source_value) in source
        .cells
        .iter()
        .filter(|(pointer, _)| !local_block_no_pointer_can_reach(&pointer.block))
    {
        // A cell the target holds under the same spelling is the match. One
        // it does not hold is most often a read of the target that only the
        // source has cached, which is the target's own value there whatever
        // else the target caches. Only then is the cell looked for under
        // another spelling, which asks an equality of every target cell.
        let equal = if let Some(target_value) = target.cells.get(source_pointer) {
            c_values_proven_equal_for_memory_resolution(source_value, &target_value, assumptions)
        } else if materialized_load_is_unchanged(source_value, target, source_pointer, assumptions)
        {
            true
        } else {
            target
                .cells
                .iter()
                .find(|(target_pointer, _)| {
                    pointers_proven_equal_for_memory_resolution(
                        source_pointer,
                        target_pointer,
                        assumptions,
                    )
                })
                .is_some_and(|(_, target_value)| {
                    c_values_proven_equal_for_memory_resolution(
                        source_value,
                        target_value,
                        assumptions,
                    )
                })
        };
        if !equal {
            return false;
        }
    }
    for ((source_pointer, source_type), source_value) in source
        .union_cells
        .iter()
        .filter(|((pointer, _), _)| !local_block_no_pointer_can_reach(&pointer.block))
    {
        let matching = target
            .union_cells
            .iter()
            .find(|((target_pointer, target_type), _)| {
                source_type == target_type
                    && pointers_proven_equal_for_memory_resolution(
                        source_pointer,
                        target_pointer,
                        assumptions,
                    )
            });
        let equal = if let Some((_, target_value)) = matching {
            c_values_proven_equal_for_memory_resolution(source_value, target_value, assumptions)
        } else {
            materialized_load_is_unchanged(source_value, target, source_pointer, assumptions)
        };
        if !equal {
            return false;
        }
    }
    true
}

fn materialized_load_is_unchanged(
    value: &CValue,
    symbolic_memory: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    // With terms canonical at creation a materialized cell holds the load
    // variable for its load; the registry records the load it stands for.
    let load_of = |bits: &Bitvector32Term| match bits {
        Bitvector32Term::MemoryLoad(_, _, _) => Some(bits.clone()),
        Bitvector32Term::Variable(variable) if crate::kernel::eval::is_load_variable(variable) => {
            crate::kernel::eval::registered_load_term_for_variable(variable)
        }
        _ => None,
    };
    let load = match value {
        crate::kernel::integer64_c_value!(bits) => load_of(bits),
        // A pointer-typed cell materialized from a load scales the load (or
        // its load variable) by the pointee width, as the kernel's own
        // symbolic pointer loads do.
        CValue::Pointer(pointer_value) => {
            if pointer_value.designation().is_some() {
                return false;
            }
            let Pointer {
                offset: PointerOffsetTerm::Int32Scaled { value: bits, .. },
                ..
            } = pointer_value.pointer()
            else {
                return false;
            };
            load_of(bits)
        }
        _ => return false,
    };
    // The cell is the read only when it is a read of the cell's own kind: a
    // narrower or differently signed load stored in it holds another value
    // than a read of the cell returns.
    let Some(left) = load else {
        return false;
    };
    let Bitvector32Term::MemoryLoad(_, load_pointer, kind) = &left else {
        return false;
    };
    let kind = *kind;
    if LoadKind::of_value(value) != Some(kind) {
        return false;
    }
    let right = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(symbolic_memory.clone()),
        Box::new(pointer.clone()),
        kind,
    );
    pointers_proven_equal_for_memory_resolution(load_pointer, pointer, assumptions)
        && crate::kernel::checked_atomic_load_equality(&left, &right, assumptions)
}

struct CertifiedFunctionClaimPath {
    checked_resource_guard_case: Option<Arc<CCheckedResourceGuardCase>>,
    independent_entry: std::cell::OnceCell<bool>,
    entry_assumptions: PureFactContext,
    caller_state: CState,
    arguments: Vec<CExpression>,
    outcome: CFunctionOutcome,
    exit_state: Option<CState>,
    entry_state: CState,
    body_entry_state: CState,
    required_resources: ResourceContext,
    checked_required_resources: Vec<crate::kernel::functions::CCheckedResourceFact>,
    entry_resources: ResourceContext,
    post_state: Option<CState>,
    post_resources: Option<ResourceContext>,
    assumptions: PureFactContext,
    effect_facts: ExecutionFacts,
    checked_resource_claims: Vec<CFunctionContractClaimKey>,
    checked_resource_transition: bool,
}

/// Diagnostic evidence from a failed contract path preparation. This carries
/// no authority into certification; only the failed obligation and a bounded
/// view of the facts available to its exact check are retained.
#[derive(Clone, Debug)]
pub(crate) struct ContractPathPreparationFailure {
    pub reason: String,
    pub obligation: Option<Proposition>,
    pub available: Vec<Proposition>,
    pub available_count: usize,
}

impl From<String> for ContractPathPreparationFailure {
    fn from(reason: String) -> Self {
        Self {
            reason,
            obligation: None,
            available: Vec::new(),
            available_count: 0,
        }
    }
}

fn unproved_contract_path_condition(
    reason: String,
    obligation: &ProofObligation,
    assumptions: &PureFactContext,
) -> ContractPathPreparationFailure {
    // Sample both ends of the fact index without retaining the whole context.
    // Its order is index order, not execution order. These are the facts
    // consulted by certification, including resource population facts,
    // rather than a second execution or a speculative proof search.
    let mut first = Vec::new();
    let mut last = std::collections::VecDeque::new();
    let mut count = 0;
    let facts = assumptions
        .condition_fact_pairs()
        .map(|(condition, polarity)| Proposition::ConditionIs(condition.clone(), polarity))
        .chain(assumptions.proposition_facts().cloned());
    for fact in facts {
        count += 1;
        if first.len() < 8 {
            first.push(fact);
        } else {
            if last.len() == 24 {
                last.pop_front();
            }
            last.push_back(fact);
        }
    }
    first.extend(last);
    ContractPathPreparationFailure {
        reason,
        obligation: Some(obligation.proposition().clone()),
        available: first,
        available_count: count,
    }
}

fn prepare_function_claim_path(
    function: &CFunction,
    path: &SymbolicCExecutionPath,
    checked_resource_claims: Vec<CFunctionContractClaimKey>,
    checked_resource_transition: bool,
    deferred_contract_exit: bool,
    deferred_contract_exit_error: Option<CRuntimeError>,
    checked_returned_resources: crate::kernel::ResourceContext,
    capture_failure: bool,
    checked_transfer: Option<&crate::kernel::functions::CheckedBoundaryResourceTransfer>,
    checked_resource_guard_case: Option<Arc<CCheckedResourceGuardCase>>,
) -> Result<CertifiedFunctionClaimPath, ContractPathPreparationFailure> {
    // The boundary transfer is captured from the proof's entry function,
    // before loop annotations are attached. It depends only on the
    // function's signature and contract, so it must agree on those; the path
    // itself belongs to the annotated function.
    if checked_transfer.is_some_and(|transfer| {
        let checked = transfer.checked_function();
        checked.name() != function.name()
            || checked.parameters() != function.parameters()
            || checked.contract_interface() != function.contract_interface()
    }) {
        return Err("the checked boundary transfer belongs to another function"
            .to_string()
            .into());
    }
    let Some((caller_state, arguments, outcome, assumptions)) =
        certified_function_path_parts(function, path)
    else {
        return Err("the certified path does not belong to the exact function"
            .to_string()
            .into());
    };
    let entry_assumptions = assumptions.clone();
    let independent_entry = std::cell::OnceCell::new();
    let Some(entry_state) =
        c_function_entry_state_with_assumptions(caller_state, function, arguments, &assumptions)
    else {
        return Err("the function entry state cannot be reconstructed"
            .to_string()
            .into());
    };
    // Contract observations use the incoming value image. Semantic effects
    // select the callee's actual private by-value object and its authority.
    let body_entry_state = entry_state.clone();
    let mut entry_state = contract_view_of_entry(entry_state, function, arguments);
    let mut budget = ExecutionBudget::beside_live_state();
    let (required_resources, checked_required_resources) =
        match evaluate_function_resource_context_with_metadata(
            &entry_state,
            function.resource_requires(),
            function.composite_resource_definitions(),
            &assumptions,
            &mut budget,
        ) {
            Ok(Ok(resources)) => resources,
            Ok(Err(error)) => {
                return Err(format!(
                    "the required resource context cannot be evaluated: {error:?}"
                )
                .into());
            }
            Err(limit) => {
                return Err(format!(
                    "the required resource context stopped at {}",
                    limit.describe()
                )
                .into());
            }
        };
    let expanded_required = {
        let required_state = entry_state
            .clone()
            .with_resource_context(required_resources.clone());
        super::super::super::functions::expand_all_composite_resource_facts_and_propositions_at_state(
            &required_resources,
            function.composite_resource_definitions(),
            &required_state,
            &assumptions,
        )
    };
    let Some((_, definition_facts)) = expanded_required else {
        return Err("the required composite resources cannot be expanded"
            .to_string()
            .into());
    };
    let mut assumptions = assumptions_with_propositions(&assumptions, &definition_facts);
    let Some(population_facts) = evaluate_resource_population_fact_propositions(
        &required_resources,
        function.composite_resource_definitions(),
        &entry_state,
        &assumptions,
    ) else {
        return Err("the counted population facts cannot be evaluated"
            .to_string()
            .into());
    };
    for fact in population_facts {
        assumptions = assumptions.assume_proposition(fact);
    }
    let deferred_body_outcome = if deferred_contract_exit {
        match outcome {
            CFunctionOutcome::Return { value, state } => {
                // An authority deferred exit can retain an output occurrence that was
                // already folded in the body. The checked return context
                // describes that occurrence, rather than a second owner.
                // Preserve every checked output and replace only identical
                // representations left in the body outcome.
                let mut body_resources = state.resources().clone();
                {
                    for fact in checked_returned_resources.facts() {
                        if let Some(without) =
                            body_resources.clone().without_exact_representation(fact)
                        {
                            body_resources = without;
                        }
                    }
                }
                let resources = body_resources
                    .try_compose_with_facts(
                        checked_returned_resources.facts().iter().cloned(),
                        &assumptions,
                    )
                    .map_err(|error| {
                        format!(
                            "the checked returned resources cannot be composed into the deferred body outcome: {error:?}"
                        )
                    })?;
                let mut state = state.clone();
                state = Box::new(state.with_resource_context(resources));
                Some(CFunctionOutcome::Return {
                    value: value.clone(),
                    state,
                })
            }
            CFunctionOutcome::Throw { .. } => Some(outcome.clone()),
            _ => None,
        }
    } else {
        None
    };
    let resolved_outcome = if deferred_contract_exit {
        let Some(error) = deferred_contract_exit_error.as_ref().filter(|error| {
            crate::kernel::functions::is_deferred_conditional_resource_effect_error(error)
        }) else {
            return Err(
                "the deferred conditional contract exit has no valid boundary error"
                    .to_string()
                    .into(),
            );
        };
        let _ = error;
        match crate::kernel::functions::resolve_deferred_contract_exit(
            caller_state,
            checked_transfer.map_or(function, |transfer| transfer.checked_function()),
            arguments,
            deferred_body_outcome.as_ref().unwrap_or(outcome),
            checked_transfer,
            &assumptions,
            &mut budget,
        ) {
            Ok(Ok(outcome)) => Some(outcome),
            Ok(Err(error)) => {
                return Err(format!(
                    "the deferred conditional contract exit cannot be resolved: {error:?}"
                )
                .into());
            }
            Err(limit) => {
                return Err(format!(
                    "the deferred conditional contract exit stopped at {}",
                    limit.describe()
                )
                .into());
            }
        }
    } else {
        None
    };
    let outcome = resolved_outcome.as_ref().unwrap_or(outcome);
    let Some(entry_resources) =
        super::super::super::functions::expand_all_composite_resource_facts_at_state(
            entry_state.resources(),
            function.composite_resource_definitions(),
            &entry_state,
            &assumptions,
        )
    else {
        return Err("the entry resource context cannot be expanded"
            .to_string()
            .into());
    };
    // The contract's own folded field-bearing instances make the cells their
    // unmatched bodies own readable, as they did while the clauses were
    // evaluated; certification reads the entry through the same authority.
    let entry_resources = with_unmatched_instance_body_views(
        entry_resources,
        required_resources.facts(),
        function,
        &entry_state,
        &assumptions,
    );
    let Ok(resource_facts) = entry_resources.observable_facts(&assumptions) else {
        return Err("the entry resource context is not observable"
            .to_string()
            .into());
    };
    entry_state = entry_state.with_resource_context(entry_resources.clone());
    #[cfg(test)]
    let context_entries_before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
    // A verification condition may be local to one symbolic path. Branch
    // guards and independently certified callee postconditions are evidence
    // on that path, just as assumable definedness obligations are; omitting
    // them here incorrectly rejects safe guarded calls after certification.
    // Non-assumable obligations are deliberately excluded by
    // `assumptions_with_path_context`, so this cannot prove a verification
    // condition by assuming the condition itself.
    let assumptions = if resource_facts.is_empty()
        && let Some(post_assumptions) = &path.post_assumptions
    {
        // Entry resources were evaluated above under entry premises only.
        // The completion producer retained this persistent body context;
        // extend it only by the assumable obligations, never the conditions
        // whose truth certification still needs to establish.
        assumptions_with_path_context(post_assumptions, &[], path.obligations())
    } else {
        // Keep the established resource-fact/path-fact precedence for legacy
        // producers and paths with observable entry-resource propositions.
        let execution_facts = path.execution_facts();
        let assumptions = assumptions_with_propositions(&assumptions, &resource_facts);
        assumptions_with_path_context(&assumptions, &execution_facts, path.obligations())
    };
    #[cfg(test)]
    crate::kernel::reasoning::path_facts::record_contract_path_context_entries(
        crate::kernel::reasoning::path_facts::context_rebuild_entries() - context_entries_before,
    );
    let effect_facts = path.effect_facts.clone();
    if matches!(outcome, CFunctionOutcome::VerificationDiverges) {
        if let Some(obligation) = path.obligations().iter().find(|obligation| {
            !assumptions.proves_exact(obligation.proposition())
                && !loadable_covered_by_fact(&assumptions, obligation.proposition())
                && !forall_loadable_covered_by_fact(&assumptions, obligation.proposition())
        }) {
            let reason = format!(
                "the divergent verification path has an unproved condition: {}",
                unproved_path_obligation_message(obligation)
            );
            return Err(if capture_failure {
                unproved_contract_path_condition(reason, obligation, &assumptions)
            } else {
                reason.into()
            });
        }
        return Ok(CertifiedFunctionClaimPath {
            checked_resource_guard_case,
            independent_entry,
            entry_assumptions,
            caller_state: caller_state.clone(),
            arguments: arguments.to_vec(),
            outcome: outcome.clone(),
            exit_state: None,
            entry_state,
            body_entry_state,
            required_resources,
            checked_required_resources,
            entry_resources,
            post_state: None,
            post_resources: None,
            assumptions,
            effect_facts,
            checked_resource_claims,
            checked_resource_transition,
        });
    }
    let (value, raw_exit_state, exceptional) = match outcome {
        CFunctionOutcome::Return { value, state } => (value, state, false),
        CFunctionOutcome::Throw { value, state }
            if function.exceptional_signature().permits(value) =>
        {
            (value, state, true)
        }
        _ => return Err(format!("the certified path is not safe: {outcome:?}").into()),
    };
    if !exceptional {
        {
            match crate::kernel::functions::check_acquired_control_member_effects(
                &entry_state,
                raw_exit_state,
                function.contract_interface(),
                &assumptions,
                &mut budget,
            ) {
                Ok(Ok(())) => {}
                Ok(Err(error)) => return Err(format!("{error:?}").into()),
                Err(limit) => return Err(limit.describe().to_string().into()),
            }
        }
        match crate::kernel::functions::check_wildcard_consumption_at_return(
            &entry_state,
            raw_exit_state,
            function.contract_interface(),
            &assumptions,
            &mut budget,
        ) {
            Ok(Ok(())) => {}
            Ok(Err(error)) => return Err(format!("{error:?}").into()),
            Err(limit) => return Err(limit.describe().to_string().into()),
        }
    }
    let exit_memory = if exceptional {
        raw_exit_state.memory().clone()
    } else {
        crate::kernel::functions::function_exit_memory(
            caller_state,
            raw_exit_state,
            value,
            function,
        )
    };
    let mut claim_exit_state = raw_exit_state.clone();
    claim_exit_state.set_memory(exit_memory.clone());
    let Some(post_resources) =
        super::super::super::functions::expand_all_composite_resource_facts_at_state(
            claim_exit_state.resources(),
            function.composite_resource_definitions(),
            &claim_exit_state,
            &assumptions,
        )
    else {
        return Err("the exit resource context cannot be expanded"
            .to_string()
            .into());
    };
    let post_resources = with_unmatched_instance_body_views(
        post_resources,
        claim_exit_state.resources().facts(),
        function,
        &claim_exit_state,
        &assumptions,
    );
    let Ok(post_resource_facts) = post_resources.observable_facts(&assumptions) else {
        return Err("the exit resource context is not observable"
            .to_string()
            .into());
    };
    let mut assumptions = assumptions_with_propositions(&assumptions, &post_resource_facts);
    let mut post_state = entry_state.clone().with_memory(exit_memory);
    post_state = post_state.with_resource_context(post_resources.clone());
    post_state.observed_population_families = raw_exit_state.observed_population_families.clone();
    // Population counts live in the creation ledger, and observed families
    // beside it. Both must describe the checked exit, not the reconstructed
    // entry used to bind locals.
    post_state.population_effects = raw_exit_state.population_effects.clone();
    if exceptional {
        post_state.locals.set_typed(
            C_EXCEPTIONAL_RESULT_NAME.to_string(),
            value.clone(),
            CType::Int32,
        );
    } else if function.return_type() != CType::Void {
        post_state.locals.set_typed(
            C_CONTRACT_RESULT_NAME.to_string(),
            value.clone(),
            function.return_type(),
        );
    }
    // A named predicate returned by a verified call is an opaque certified
    // execution fact. Reconstruct its registered body at the enclosing
    // function's exact post-state so other postconditions can use the
    // definition without trusting a surface-supplied expansion.
    for unfolding in function.predicate_unfoldings() {
        let Some((predicate, predicate_obligations, body, body_obligations)) =
            instantiate_contract_predicate_unfolding_with_obligations(
                &post_state,
                Some(&entry_state),
                unfolding,
                &assumptions,
                &mut budget,
            )
        else {
            continue;
        };
        let obligations_hold =
            predicate_obligations
                .iter()
                .chain(&body_obligations)
                .all(|obligation| {
                    assumptions.proves_exact(obligation)
                        || contract_endpoints_certify_loadability(
                            &entry_state,
                            &entry_resources,
                            &post_state,
                            &post_resources,
                            obligation,
                            &assumptions,
                        )
                        || loadable_covered_by_fact(&assumptions, obligation)
                        || forall_loadable_covered_by_fact(&assumptions, obligation)
                });
        let predicate_holds = assumptions.proves_exact(&predicate);
        if obligations_hold && predicate_holds {
            assumptions = assumptions.assume_proposition(body);
        }
    }
    if let Some(obligation) = path.obligations().iter().find(|obligation| {
        let proved = assumptions.proves_exact(obligation.proposition())
            || loadable_covered_by_fact(&assumptions, obligation.proposition())
            || forall_loadable_covered_by_fact(&assumptions, obligation.proposition())
            || contract_endpoints_certify_loadability(
                &entry_state,
                &entry_resources,
                &post_state,
                &post_resources,
                obligation.proposition(),
                &assumptions,
            );
        !proved
    }) {
        let reason = format!(
            "the execution path has an unproved verification condition: {}",
            unproved_path_obligation_message(obligation)
        );
        return Err(if capture_failure {
            unproved_contract_path_condition(reason, obligation, &assumptions)
        } else {
            reason.into()
        });
    }

    // A certificate can instantiate exit terms by variable substitution,
    // which intentionally rebuilds structural resources without old graph
    // equalities. Publish that explicit output once at path preparation,
    // before any individual claim consumes it. Already published persistent
    // outputs keep their pairing; claim lookup must never attach a cold frame.
    claim_exit_state
        .resources()
        .synchronize_memory_equalities(&assumptions);

    Ok(CertifiedFunctionClaimPath {
        checked_resource_guard_case,
        independent_entry,
        entry_assumptions,
        caller_state: caller_state.clone(),
        arguments: arguments.to_vec(),
        outcome: outcome.clone(),
        exit_state: Some(*claim_exit_state),
        entry_state,
        body_entry_state,
        required_resources,
        checked_required_resources,
        entry_resources,
        post_state: Some(post_state),
        post_resources: Some(post_resources),
        assumptions,
        effect_facts,
        checked_resource_claims,
        checked_resource_transition,
    })
}

/// `resources` with the read views the unmatched bodies of the field-bearing
/// instances among `instances` publish at `state`. The instances are the
/// contract's own entry clauses or the function's own exit frame, which the
/// composite expansion beside this call already visits.
fn with_unmatched_instance_body_views(
    resources: crate::kernel::ResourceContext,
    instances: &[CResourceFact],
    function: &CFunction,
    state: &CState,
    assumptions: &PureFactContext,
) -> crate::kernel::ResourceContext {
    let views = instances
        .iter()
        .flat_map(|fact| {
            crate::kernel::unmatched_instance_body_views(
                fact,
                function.composite_resource_definitions(),
                state,
                assumptions,
            )
        })
        .collect::<Vec<_>>();
    if views.is_empty() {
        resources
    } else {
        resources.unchecked_with_facts(views)
    }
}

fn unproved_path_obligation_message(obligation: &ProofObligation) -> String {
    // The kernel has no source spelling of the condition itself; its context
    // is the sentence the lowering wrote for it. A captured failure carries
    // the proposition to the surface, which renders it in the certification
    // trace, so the message never prints a kernel term dump.
    match obligation.context() {
        Some(context) => context.to_string(),
        None => {
            "a condition with no recorded source context (see the certification trace)".to_string()
        }
    }
}

fn function_claim_holds_on_prepared_path(
    function: &CFunction,
    claim: &CFunctionContractClaim,
    path: &CertifiedFunctionClaimPath,
    checked_propositions: &CheckedPropositionIndex<'_>,
    completion_origin_state: Option<&CState>,
) -> bool {
    let CertifiedFunctionClaimPath {
        checked_resource_guard_case: _,
        independent_entry: _,
        entry_assumptions: _,
        body_entry_state: _,
        caller_state,
        arguments,
        outcome,
        exit_state,
        entry_state,
        required_resources,
        checked_required_resources,
        entry_resources,
        post_state,
        post_resources,
        assumptions,
        effect_facts,
        checked_resource_claims,
        checked_resource_transition,
    } = path;
    let mut budget = ExecutionBudget::beside_live_state();
    match claim.target() {
        CFunctionContractClaimTarget::BodySafety => true,
        CFunctionContractClaimTarget::EnsureProposition(_index)
        | CFunctionContractClaimTarget::ExceptionalEnsureProposition(_index) => {
            let (Some(post_state), Some(post_resources)) = (post_state, post_resources) else {
                return true;
            };
            let ensure = match (claim.target(), outcome) {
                (
                    CFunctionContractClaimTarget::EnsureProposition(index),
                    CFunctionOutcome::Return { .. },
                ) => function.contract_ensures().get(*index),
                (
                    CFunctionContractClaimTarget::ExceptionalEnsureProposition(index),
                    CFunctionOutcome::Throw { .. },
                ) => function.exceptional_ensures().get(*index),
                (CFunctionContractClaimTarget::EnsureProposition(_), _)
                | (CFunctionContractClaimTarget::ExceptionalEnsureProposition(_), _) => {
                    return true;
                }
                _ => unreachable!("the enclosing match selects a proposition claim"),
            };
            let Some(ensure) = ensure else {
                return false;
            };
            // A surface predicate ensure is stored operationally as its
            // expanded body, plus an exact registered opaque identity. If
            // that identity is already certified at this post-state, it is
            // the kernel authority for the named predicate claim itself.
            // This path deliberately applies only to the exact registered
            // body; arbitrary proposition ensures continue through ordinary
            // lowering and loadability checks below.
            // One completion match rule for every form the ensure is compared
            // in: its lowering, and its registered predicate identity.
            // One rule for a load the claim needs to be legal: the contract's
            // resources at either endpoint supply it, or the path states it.
            let load_obligation_holds = |obligation: &Proposition| {
                contract_endpoints_certify_loadability(
                    entry_state,
                    entry_resources,
                    post_state,
                    post_resources,
                    obligation,
                    assumptions,
                ) || loadable_covered_by_fact(assumptions, obligation)
                    || forall_loadable_covered_by_fact(assumptions, obligation)
                    || certification_proves_exists_obligation_from_facts(assumptions, obligation)
                    || assumptions.proves_exact(obligation)
                    || crate::kernel::api::checked_int32_reassociated_add_domain(
                        assumptions,
                        obligation,
                    )
            };
            let certifies = |proof: &&CCheckedFunctionProposition| {
                // Cheapest checks first: a completion from another
                // path or function is rejected before any proving.
                // A completion made at the state the artifact's
                // proof ran at certifies a path rebased from it.
                let completion_state = proof.specification.state();
                if proof.function != *function
                    || (!completion_state.equal_up_to_unused_creation_ledgers(caller_state)
                        && Some(completion_state) != completion_origin_state)
                    || proof.specification.arguments() != arguments
                    || !c_function_outcomes_definitionally_equal(
                        function,
                        proof.specification.outcome(),
                        outcome,
                        assumptions,
                    )
                {
                    return false;
                }

                proof.specification.requires().iter().all(|requirement| {
                    assumptions.proves_exact(requirement)
                        || assumptions.states_required_goal(requirement)
                        || (matches!(requirement, Proposition::CMemoryLoadable { .. })
                            && load_obligation_holds(requirement))
                        || match requirement {
                            Proposition::CResourceComposition(required) => {
                                resource_context_definitionally_contains(
                                    required_resources,
                                    required,
                                    function.composite_resource_definitions(),
                                    entry_state.memory(),
                                    assumptions,
                                )
                            }
                            Proposition::Predicate { .. } => {
                                function.predicate_unfoldings().iter().any(|unfolding| {
                                    let mut budget = ExecutionBudget::beside_live_state();
                                    let Some((
                                        predicate,
                                        predicate_obligations,
                                        body,
                                        body_obligations,
                                    )) = instantiate_contract_predicate_unfolding_with_obligations(
                                        entry_state,
                                        None,
                                        unfolding,
                                        assumptions,
                                        &mut budget,
                                    )
                                    else {
                                        return false;
                                    };
                                    predicate == *requirement
                                        && predicate_obligations
                                            .iter()
                                            .chain(&body_obligations)
                                            .all(|obligation| assumptions.proves_exact(obligation))
                                        && assumptions.proves_exact(&body)
                                })
                            }
                            _ => false,
                        }
                })
            };
            // The proof closed this claim as the kernel's own goal for it, so
            // its completion is found by the claim, not by re-deriving and
            // comparing the proposition.
            let claim_completion_certifies = || {
                checked_propositions
                    .by_claim
                    .get(claim.target())
                    .is_some_and(|proofs| proofs.iter().any(certifies))
            };
            let registered_predicate_ensure_holds = function
                .predicate_unfoldings()
                .iter()
                .filter(|unfolding| unfolding.body() == ensure)
                .any(|unfolding| {
                    let Some((predicate, predicate_obligations, _, _)) =
                        instantiate_contract_predicate_unfolding_with_obligations(
                            post_state,
                            Some(entry_state),
                            unfolding,
                            assumptions,
                            &mut budget,
                        )
                    else {
                        return false;
                    };
                    predicate_obligations.iter().all(|obligation| {
                        assumptions.proves_exact(obligation)
                            || contract_endpoints_certify_loadability(
                                entry_state,
                                entry_resources,
                                post_state,
                                post_resources,
                                obligation,
                                assumptions,
                            )
                    }) && (claim_completion_certifies() || assumptions.proves_exact(&predicate))
                });
            if registered_predicate_ensure_holds {
                return true;
            }
            // Lowering records the ensure's load obligations instead of
            // searching the whole path context for each one as it goes; they
            // are discharged below from the contract's resources and exact
            // facts.
            let lowering_assumptions = assumptions
                .clone()
                .allow_symbolic_contract_loads()
                .defer_non_exact_loadability_obligations();
            let lowered = crate::instrumentation::measure_operation(
                function.name(),
                "contract claim",
                "ensure lowering",
                || {
                    lower_spec_proposition_at_state_with_loop_entry(
                        post_state,
                        ensure,
                        Some(entry_state),
                        &lowering_assumptions,
                        &mut budget,
                    )
                },
            );
            let Ok(paths) = lowered else {
                return false;
            };
            let Some(path) = exactly_selected_spec_proposition_path(&paths, assumptions) else {
                return false;
            };
            let obligations_hold = crate::instrumentation::measure_operation(
                function.name(),
                "contract claim",
                "obligation discharge",
                || {
                    let obligation_holds = |obligation: &ProofObligation| {
                        load_obligation_holds(obligation.proposition())
                    };
                    path.obligations.iter().all(obligation_holds)
                },
            );
            // A lowering that folded the ensure to a constant truth decided
            // the claim on this path by evaluation alone. Otherwise the
            // claim holds here because the proof completed it on this path.
            let proposition_holds = lowered_goal_is_constant_true(&path.proposition)
                || crate::instrumentation::measure_operation(
                    function.name(),
                    "contract claim",
                    "completion match",
                    claim_completion_certifies,
                );
            obligations_hold && proposition_holds
        }
        CFunctionContractClaimTarget::EnsureResource(index) => {
            if !matches!(outcome, CFunctionOutcome::Return { .. }) {
                return true;
            }
            if let Some(spec) = function.resource_ensures().get(*index)
                && (!spec.native_record_places().is_empty()
                    || !spec.native_span_requirements().is_empty())
                && post_state.as_ref().is_none_or(|state| {
                    check_native_record_specs(state, std::slice::from_ref(spec), assumptions)
                        .is_err()
                })
            {
                return false;
            }
            // The proof already checked this exact resource claim, including
            // its returned context and allocation-lifetime obligation. Reuse
            // that kernel-owned evidence rather than rebuilding the resource
            // transition and its population invariant.
            if *checked_resource_transition
                && checked_resource_claims
                    .iter()
                    .any(|key| key == &CFunctionContractClaimKey::Ensure(*index))
            {
                return true;
            }
            let (Some(exit_state), Some(post_state)) = (exit_state, post_state) else {
                return true;
            };
            if *index >= function.resource_ensures().len() {
                return false;
            }
            // Resource clauses describe one jointly returned context. Checking
            // each clause independently would let one resource unit certify two
            // identical clauses. The prefix makes every claim account for all
            // units claimed up to and including its own clause.
            // A borrowed resource is what the callee was lent: it is
            // evaluated at entry, where the clause's address expressions
            // still read the values the caller saw.
            let expected_result =
                crate::kernel::functions::evaluate_function_return_resource_context(
                    function,
                    checked_required_resources,
                    entry_state,
                    post_state,
                    *index + 1,
                    assumptions,
                    &mut budget,
                );
            let Ok(Ok(expected)) = expected_result else {
                return false;
            };
            if !expected.facts().iter().all(|fact| {
                resource_context_satisfies_definitional_fact(
                    exit_state.resources(),
                    fact,
                    function.composite_resource_definitions(),
                    exit_state.memory(),
                    assumptions,
                )
            }) {
                return false;
            }
            // Definitional validation answers each clause from the whole exit
            // state. The prefix is one multiset: consume it jointly so one
            // exclusive unit, or a folded composite and its own body child,
            // cannot certify two clauses.
            crate::kernel::functions::jointly_consume_returned_resource_units(
                exit_state.resources(),
                &expected,
                exit_state,
                function.contract_interface(),
                assumptions,
            )
        }
        CFunctionContractClaimTarget::Effect => {
            let Ok(Ok(projection)) =
                crate::kernel::functions::project_contract_memory_effects_with_guard_policy(
                    entry_state,
                    function.contract_interface(),
                    Some(checked_required_resources),
                    assumptions,
                    &mut budget,
                    true,
                )
            else {
                return false;
            };
            let mutable_ranges = projection.ranges().to_vec();
            // A footprint that reaches unnamed memory covers every write.
            let covers_everything = mutable_ranges
                .iter()
                .any(crate::kernel::CMemoryRange::is_unnamed_footprint);
            let mut effect_memory = caller_state.memory().clone();
            let mut seen_transitions = Vec::<(CMemory, CMemory)>::new();
            let is_function_fresh_heap_pointer = |pointer: &Pointer, current: &CMemory| {
                let matches_allocation = |memory: &CMemory| {
                    memory.heap.live_allocations.keys().any(|base| {
                        // Freshness is a property of the allocation, not of
                        // the particular address selected within it. An
                        // interior pointer into a block live at entry must
                        // still be covered by the function's mutable frame.
                        base.block == pointer.block
                            || base == pointer
                            || crate::kernel::assumptions::pointers_equal_ignoring_memories(
                                base, pointer,
                            )
                            || pointers_proven_equal_for_memory_resolution(
                                base,
                                pointer,
                                assumptions,
                            )
                    })
                };
                !matches_allocation(entry_state.memory())
                    && (matches!(pointer.block, PointerBlock::Heap(_))
                        || matches_allocation(current))
            };
            let effects_are_bounded = effect_facts.iter().all(|fact| match fact.proposition() {
                Proposition::CMemoryMutatesOnly {
                    before,
                    after,
                    writes,
                } => {
                    let repeats_transition =
                        seen_transitions.iter().any(|(seen_before, seen_after)| {
                            c_effect_memories_definitionally_equal(seen_before, before, assumptions)
                                && c_effect_memories_definitionally_equal(
                                    seen_after,
                                    after,
                                    assumptions,
                                )
                        });
                    if !repeats_transition
                        && !c_effect_memories_definitionally_equal(
                            &effect_memory,
                            before,
                            assumptions,
                        )
                        && !c_effect_memory_advances_over_internal_heap_state(
                            &effect_memory,
                            before,
                            entry_state.memory(),
                            assumptions,
                        )
                    {
                        return false;
                    }
                    if !repeats_transition {
                        effect_memory = after.clone();
                        seen_transitions.push((before.clone(), after.clone()));
                    }
                    writes
                        .iter()
                        .filter(|(pointer, _)| !pointer.block.starts_with("local:"))
                        .all(|(pointer, bytes)| {
                            covers_everything
                                || is_function_fresh_heap_pointer(pointer, before)
                                || mutable_ranges.iter().any(|range| {
                                    assumptions
                                        .pointer_access_in_memory_range(pointer, *bytes, range)
                                })
                        })
                }
                Proposition::CMemoryEffectSummary {
                    before,
                    after,
                    mutable_ranges: nested_ranges,
                } => {
                    let repeats_transition =
                        seen_transitions.iter().any(|(seen_before, seen_after)| {
                            c_effect_memories_definitionally_equal(seen_before, before, assumptions)
                                && c_effect_memories_definitionally_equal(
                                    seen_after,
                                    after,
                                    assumptions,
                                )
                        });
                    if !repeats_transition
                        && !c_effect_memories_definitionally_equal(
                            &effect_memory,
                            before,
                            assumptions,
                        )
                        && !c_effect_memory_advances_over_internal_heap_state(
                            &effect_memory,
                            before,
                            entry_state.memory(),
                            assumptions,
                        )
                    {
                        return false;
                    }
                    if !repeats_transition {
                        effect_memory = after.clone();
                        seen_transitions.push((before.clone(), after.clone()));
                    }
                    nested_ranges.iter().all(|nested| {
                        covers_everything
                            || is_function_fresh_heap_pointer(nested.base(), before)
                            || mutable_ranges
                                .iter()
                                .any(|allowed| memory_range_covers(allowed, nested, assumptions))
                    })
                }
                Proposition::CHeapAllocationFreed {
                    before,
                    after,
                    allocation_base,
                    bytes,
                } => {
                    let repeats_transition =
                        seen_transitions.iter().any(|(seen_before, seen_after)| {
                            c_effect_memories_definitionally_equal(seen_before, before, assumptions)
                                && c_effect_memories_definitionally_equal(
                                    seen_after,
                                    after,
                                    assumptions,
                                )
                        });
                    if !repeats_transition
                        && !c_effect_memories_definitionally_equal(
                            &effect_memory,
                            before,
                            assumptions,
                        )
                        && !c_effect_memory_advances_over_internal_heap_state(
                            &effect_memory,
                            before,
                            entry_state.memory(),
                            assumptions,
                        )
                    {
                        return false;
                    }
                    if !heap_free_effect_is_valid(before, after, allocation_base, bytes) {
                        return false;
                    }
                    if !repeats_transition {
                        effect_memory = after.clone();
                        seen_transitions.push((before.clone(), after.clone()));
                    }
                    true
                }
                _ => true,
            });
            let endpoint_matches = exit_state.as_ref().is_none_or(|exit_state| {
                c_effect_memories_definitionally_equal(
                    &effect_memory,
                    exit_state.memory(),
                    assumptions,
                ) || c_effect_memory_advances_over_internal_heap_state(
                    &effect_memory,
                    exit_state.memory(),
                    entry_state.memory(),
                    assumptions,
                )
            });
            effects_are_bounded && endpoint_matches
        }
    }
}

pub(in crate::kernel) fn c_effect_memories_definitionally_equal(
    left: &CMemory,
    right: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    let without_locals = |memory: &CMemory| {
        let mut external = memory.clone();
        std::sync::Arc::make_mut(&mut external.blocks)
            .retain(|block, _| !block.starts_with("local:"));
        std::sync::Arc::make_mut(&mut external.cells)
            .retain(|pointer, _| !pointer.block.starts_with("local:"));
        std::sync::Arc::make_mut(&mut external.forgotten)
            .ended_local_blocks
            .clear();
        external.record_diagnostic_transform(
            "project external effect memory",
            vec![memory.clone()],
            Vec::new(),
        );
        external
    };
    let left = without_locals(left);
    let right = without_locals(right);
    c_memories_definitionally_equal(&left, &right, assumptions)
}

/// Accepts internal heap bookkeeping between externally visible effects:
/// newly allocated trusted blocks and the registration of an already-owned
/// symbolic allocation before direct `free`. Removing only those additions
/// leaves a memory that must still match the preceding endpoint exactly.
pub(in crate::kernel) fn c_effect_memory_advances_over_internal_heap_state(
    before: &CMemory,
    after: &CMemory,
    function_entry: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    let fresh_blocks = after
        .blocks
        .keys()
        .filter(|block| {
            matches!(block, PointerBlock::Heap(_))
                && !before.blocks.contains_key(*block)
                && !function_entry.blocks.contains_key(*block)
        })
        .cloned()
        .collect::<BTreeSet<_>>();
    let added_allocation_claims = after
        .heap
        .live_allocations
        .keys()
        .filter(|pointer| !before.heap.live_allocations.contains_key(*pointer))
        .cloned()
        .collect::<BTreeSet<_>>();
    if fresh_blocks.is_empty() && added_allocation_claims.is_empty() {
        return false;
    }
    let mut stripped = after.clone();
    std::sync::Arc::make_mut(&mut stripped.blocks).retain(|block, _| !fresh_blocks.contains(block));
    std::sync::Arc::make_mut(&mut stripped.cells)
        .retain(|pointer, _| !fresh_blocks.contains(&pointer.block));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .live_allocations
        .retain(|pointer, _| {
            !fresh_blocks.contains(&pointer.block) && !added_allocation_claims.contains(pointer)
        });
    std::sync::Arc::make_mut(&mut stripped.heap)
        .deallocated_allocations
        .retain(|pointer, _| !fresh_blocks.contains(&pointer.block));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .pending_allocations
        .retain(|pointer, _| !fresh_blocks.contains(&pointer.block));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .uninitialized_allocations
        .retain(|pointer| !fresh_blocks.contains(&pointer.block));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .zeroed_allocations
        .retain(|pointer| !fresh_blocks.contains(&pointer.block));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .zeroed_prefix_allocations
        .retain(|pointer, _| !fresh_blocks.contains(&pointer.block));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .zeroed_pending_allocations
        .retain(|pointer| !fresh_blocks.contains(&pointer.block));
    stripped.record_diagnostic_transform(
        "remove internal heap bookkeeping",
        vec![after.clone(), before.clone(), function_entry.clone()],
        Vec::new(),
    );
    c_effect_memories_definitionally_equal(before, &stripped, assumptions)
}

fn heap_free_effect_is_valid(
    before: &CMemory,
    after: &CMemory,
    allocation_base: &Pointer,
    bytes: &Bitvector32Term,
) -> bool {
    let Some(live) = (if before.live_heap_block_size(allocation_base).is_some() {
        Some(before.clone())
    } else {
        before
            .clone()
            .with_heap_allocation_claim(allocation_base.clone(), bytes.clone())
    }) else {
        return false;
    };
    live.live_heap_block_size(allocation_base) == Some(bytes)
        && live
            .free_heap_block(allocation_base, &PureFactContext::new())
            .is_ok_and(|expected| expected == *after)
}

/// The goal a proof closes to establish one proposition claim of a contract
/// at one outcome: the kernel's lowering of that `ensures` there, with the
/// facts its loads introduced.
///
/// Only the kernel builds one, so a proof obligation opened from it
/// ([`crate::kernel::proof::PropositionObligation::for_claim_goal`]) is known
/// to state that claim, and the proposition completed from that obligation
/// says which claim it closes without anything being lowered or compared
/// again.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CClaimGoal {
    target: CFunctionContractClaimTarget,
    proposition: Proposition,
    facts: Vec<Proposition>,
}

impl CClaimGoal {
    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    /// The facts the goal's loads introduced.
    pub fn facts(&self) -> &[Proposition] {
        &self.facts
    }

    pub(crate) fn target(&self) -> &CFunctionContractClaimTarget {
        &self.target
    }
}

/// The entry state as a contract reads it. A by-value aggregate parameter
/// denotes the image of the caller's argument, which nothing writes; the
/// callee's copy of it is private storage the body may overwrite. A caller
/// applying the contract reads the same thing: `bind_c_contract_arguments`
/// copies the argument into a block of its own that no body runs against.
fn contract_view_of_entry(
    mut entry_state: CState,
    function: &CFunction,
    arguments: &[CExpression],
) -> CState {
    for (parameter, argument) in function.parameters().iter().zip(arguments) {
        if let (Some(layout), CExpression::Value(CValue::Pointer(argument))) =
            (parameter.aggregate_layout(), argument)
        {
            entry_state.locals.set_aggregate_object_at(
                parameter.name().to_string(),
                layout.clone(),
                argument.pointer().clone(),
            );
        }
    }
    entry_state
}

/// Certifies every exact contract claim in one pass over a kernel-produced,
/// complete execution frontier.
///
/// Path validity, resource expansion, and verification conditions are checked
/// once per path and then shared by the individual claim checks.
/// Lowers proposition ensure `contract_index` of `function` at the
/// post-state `outcome` reaches from `caller_state` with `arguments`: the
/// one lowering a claim proof closes and claim certification matches, so a
/// completion matches by construction. Each path pairs the ensure's
/// proposition with the facts its loads introduced. An ensure stated as a
/// registered predicate is closed as that predicate identity, the form the
/// proof states and unfolds on the goal, unless `unfolded_predicates` names
/// the predicate, in which case it is closed as the body the contract
/// stores. `None` when the outcome does not return or the states cannot be
/// reconstructed.
pub fn c_function_ensure_goals(
    function: &CFunction,
    contract_index: usize,
    caller_state: &CState,
    arguments: &[CExpression],
    outcome: &CFunctionOutcome,
    assumptions: &PureFactContext,
    unfolded_predicates: &[String],
) -> Option<Vec<CClaimGoal>> {
    let ensure = function.contract_ensures().get(contract_index)?;
    let ensure = function
        .predicate_unfoldings()
        .iter()
        .find(|unfolding| unfolding.body() == ensure)
        .filter(|unfolding| match unfolding.predicate() {
            SpecProposition::Predicate { name, .. } => !unfolded_predicates.contains(name),
            _ => false,
        })
        .map_or(ensure, CPredicateUnfolding::predicate);
    let CFunctionOutcome::Return {
        value,
        state: return_state,
    } = outcome
    else {
        return None;
    };
    let mut entry_state = contract_view_of_entry(
        c_function_entry_state_with_assumptions(caller_state, function, arguments, assumptions)?,
        function,
        arguments,
    );
    let expanded_entry_resources =
        crate::kernel::functions::expand_all_composite_resource_facts_at_state(
            entry_state.resources(),
            function.composite_resource_definitions(),
            &entry_state,
            assumptions,
        )?;
    entry_state = entry_state.with_resource_context(expanded_entry_resources);
    let exit_memory =
        crate::kernel::functions::function_exit_memory(caller_state, return_state, value, function);
    let claim_return_state = return_state.clone().with_memory(exit_memory.clone());
    let post_resources = crate::kernel::functions::expand_all_composite_resource_facts_at_state(
        claim_return_state.resources(),
        function.composite_resource_definitions(),
        &claim_return_state,
        assumptions,
    )?;
    let mut post_state = entry_state.clone().with_memory(exit_memory);
    post_state = post_state.with_resource_context(post_resources);
    post_state.observed_population_families = return_state.observed_population_families.clone();
    // Preserve checked body consumption evidence when reconstructing the exit.
    post_state.population_effects = return_state.population_effects.clone();
    if function.return_type() != CType::Void {
        post_state.locals.set_typed(
            C_CONTRACT_RESULT_NAME.to_string(),
            value.clone(),
            function.return_type(),
        );
    }
    let lowering_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .defer_non_exact_loadability_obligations();
    let mut budget = ExecutionBudget::beside_live_state();
    let paths = lower_spec_proposition_at_state_with_loop_entry(
        &post_state,
        ensure,
        Some(&entry_state),
        &lowering_assumptions,
        &mut budget,
    )
    .ok()?;
    // An ensure that reads memory the outcome shows freed is not stated at
    // this outcome: no goal, so the claim's own lowering reports the load.
    if paths.iter().any(|path| {
        path.obligations.iter().any(|obligation| {
            super::c_loadability_obligation_impossible_with_assumptions(
                obligation.proposition(),
                assumptions,
            )
        })
    }) {
        return None;
    }
    let selected = exactly_selected_spec_proposition_path(&paths, assumptions);
    let paths = match selected {
        Some(path) if paths.len() > 1 => std::slice::from_ref(path),
        _ => paths.as_slice(),
    };
    Some(
        paths
            .iter()
            .map(|path| CClaimGoal {
                target: CFunctionContractClaimTarget::EnsureProposition(contract_index),
                proposition: path.proposition.clone(),
                facts: path
                    .facts
                    .iter()
                    .map(|fact| fact.proposition().clone())
                    .collect(),
            })
            .collect(),
    )
}

/// Lowers one exceptional postcondition at a checked throwing outcome. The
/// exceptional family observes the thrown `int32` through the kernel's
/// reserved payload binding and observes the state at the throw boundary.
/// Returning outcomes do not owe an exceptional postcondition.
pub(crate) fn c_function_exceptional_ensure_goals(
    function: &CFunction,
    contract_index: usize,
    caller_state: &CState,
    arguments: &[CExpression],
    outcome: &CFunctionOutcome,
    assumptions: &PureFactContext,
) -> Option<Vec<CClaimGoal>> {
    let ensure = function.exceptional_ensures().get(contract_index)?;
    let CFunctionOutcome::Throw {
        value,
        state: throw_state,
    } = outcome
    else {
        return None;
    };
    let mut entry_state = contract_view_of_entry(
        c_function_entry_state_with_assumptions(caller_state, function, arguments, assumptions)?,
        function,
        arguments,
    );
    let expanded_entry_resources = expand_all_composite_resource_facts(
        entry_state.resources(),
        function.composite_resource_definitions(),
        entry_state.memory(),
        assumptions,
    )?;
    entry_state = entry_state.with_resource_context(expanded_entry_resources);
    let mut post_state = entry_state
        .clone()
        .with_memory(throw_state.memory().clone());
    post_state.observed_population_families = throw_state.observed_population_families.clone();
    post_state.locals.set_typed(
        C_EXCEPTIONAL_RESULT_NAME.to_string(),
        value.clone(),
        CType::Int32,
    );
    let lowering_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .defer_non_exact_loadability_obligations();
    let mut budget = ExecutionBudget::beside_live_state();
    let paths = lower_spec_proposition_at_state_with_loop_entry(
        &post_state,
        ensure,
        Some(&entry_state),
        &lowering_assumptions,
        &mut budget,
    )
    .ok()?;
    if paths.iter().any(|path| {
        path.obligations.iter().any(|obligation| {
            super::c_loadability_obligation_impossible_with_assumptions(
                obligation.proposition(),
                assumptions,
            )
        })
    }) {
        return None;
    }
    let selected = exactly_selected_spec_proposition_path(&paths, assumptions);
    let paths = match selected {
        Some(path) if paths.len() > 1 => std::slice::from_ref(path),
        _ => paths.as_slice(),
    };
    Some(
        paths
            .iter()
            .map(|path| CClaimGoal {
                target: CFunctionContractClaimTarget::ExceptionalEnsureProposition(contract_index),
                proposition: path.proposition.clone(),
                facts: path
                    .facts
                    .iter()
                    .map(|fact| fact.proposition().clone())
                    .collect(),
            })
            .collect(),
    )
}

pub fn c_verified_function_contract_claims(
    function: &CFunction,
    contract_execution: &CFunctionContractExecution,
) -> Option<Vec<CVerifiedFunctionContractClaim>> {
    c_verified_function_contract_claims_with_checked_propositions(function, contract_execution, &[])
}

/// Whether a lowered ensure folded to a constant truth: the kernel's own
/// evaluation at the outcome decided it, so it needs no completion.
fn lowered_goal_is_constant_true(proposition: &Proposition) -> bool {
    matches!(
        completion_key(proposition),
        Proposition::ConditionIs(ConditionTerm::Constant(true), true)
    )
}

/// The form in which a completed proposition is matched against a lowered
/// ensure. The two are lowerings of one claim by different code: the proof
/// folds trivial conditions as it lowers (a term compared with itself, a
/// constant premise), the contract lowering keeps them. This folds both to
/// one form by exact structural rules: no fact is consulted.
pub(crate) fn completion_key(proposition: &Proposition) -> Proposition {
    fn truth(value: bool) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::Constant(value), true)
    }
    fn as_truth(proposition: &Proposition) -> Option<bool> {
        match proposition {
            Proposition::ConditionIs(ConditionTerm::Constant(constant), value) => {
                Some(constant == value)
            }
            _ => None,
        }
    }
    fn reflexive(condition: &ConditionTerm) -> bool {
        match condition {
            ConditionTerm::Bitvector32Equal(left, right) => left == right,
            ConditionTerm::PointerEqual(left, right) => left == right,
            ConditionTerm::PointerOffsetEqual(left, right) => left == right,
            _ => false,
        }
    }
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            if let ConditionTerm::Constant(constant) = condition {
                truth(constant == value)
            } else if reflexive(condition) {
                truth(*value)
            } else {
                proposition.clone()
            }
        }
        // A predicate identity carries a resource-state snapshot only when
        // its definition observes resource counts; the proof's lowering
        // leaves it empty otherwise. The outcome the completion was made
        // at fixes that state, so the key compares predicates without it.
        Proposition::Predicate { name, arguments } => {
            let mut arguments = arguments.clone();
            if let Some(Term::CState(state)) = arguments.first_mut() {
                **state = CState::new();
            }
            Proposition::Predicate {
                name: name.clone(),
                arguments,
            }
        }
        Proposition::Not(body) => {
            let body = completion_key(body);
            match (as_truth(&body), body) {
                (Some(value), _) => truth(!value),
                (None, Proposition::ConditionIs(condition, value)) => {
                    Proposition::ConditionIs(condition, !value)
                }
                (None, body) => Proposition::Not(Box::new(body)),
            }
        }
        Proposition::And(left, right) => {
            let (left, right) = (completion_key(left), completion_key(right));
            match (as_truth(&left), as_truth(&right)) {
                (Some(false), _) | (_, Some(false)) => truth(false),
                (Some(true), _) => right,
                (_, Some(true)) => left,
                _ => Proposition::And(Box::new(left), Box::new(right)),
            }
        }
        Proposition::Or(left, right) => {
            let (left, right) = (completion_key(left), completion_key(right));
            match (as_truth(&left), as_truth(&right)) {
                (Some(true), _) | (_, Some(true)) => truth(true),
                (Some(false), _) => right,
                (_, Some(false)) => left,
                _ => Proposition::Or(Box::new(left), Box::new(right)),
            }
        }
        Proposition::Implies(premise, body) => {
            let (premise, body) = (completion_key(premise), completion_key(body));
            match (as_truth(&premise), as_truth(&body)) {
                (Some(true), _) => body,
                (Some(false), _) | (_, Some(true)) => truth(true),
                _ => Proposition::Implies(Box::new(premise), Box::new(body)),
            }
        }
        // A quantifier over a constant body is that constant: every sort a
        // binder ranges over is inhabited.
        Proposition::ForAll { body, .. } => {
            let body = completion_key(body);
            if as_truth(&body).is_some() {
                return body;
            }
            let mut forall = proposition.clone();
            if let Proposition::ForAll { body: slot, .. } = &mut forall {
                **slot = body;
            }
            forall
        }
        Proposition::Exists { body, .. } => {
            let body = completion_key(body);
            if as_truth(&body).is_some() {
                return body;
            }
            let mut exists = proposition.clone();
            if let Proposition::Exists { body: slot, .. } = &mut exists {
                **slot = body;
            }
            exists
        }
        _ => proposition.clone(),
    }
}

fn checked_proposition_index(
    checked_propositions: &[CCheckedFunctionProposition],
) -> CheckedPropositionIndex<'_> {
    let mut index = CheckedPropositionIndex::default();
    for checked in checked_propositions {
        if let Some(claim) = &checked.claim {
            index
                .by_claim
                .entry(claim.clone())
                .or_default()
                .push(checked);
        }
    }
    index
}

/// The proof's completed propositions, by the contract claim each closed.
#[derive(Default)]
struct CheckedPropositionIndex<'a> {
    by_claim: BTreeMap<CFunctionContractClaimTarget, Vec<&'a CCheckedFunctionProposition>>,
}

/// Certifies contract claims while reusing proposition judgments already
/// closed by the kernel proof object. Finalization still reconstructs the
/// exact function paths and checks resources, effects, obligations, and claim
/// coverage; it does not re-prove a proposition claim the proof completed.
pub(crate) fn c_verified_function_contract_claims_with_checked_propositions(
    function: &CFunction,
    contract_execution: &CFunctionContractExecution,
    checked_propositions: &[CCheckedFunctionProposition],
) -> Option<Vec<CVerifiedFunctionContractClaim>> {
    if !contract_execution.is_complete() {
        return None;
    }
    let timings = crate::instrumentation::enabled();
    let prepare_started = std::time::Instant::now();
    let cases = contract_path_set_views(contract_execution, false);
    let checked_propositions = checked_proposition_index(checked_propositions);
    let claims = function
        .contract_claims()
        .iter()
        .map(|claim| {
            let claim_started = std::time::Instant::now();
            let load_equality_capture =
                crate::kernel::CheckedLoadEqualityCapture::start_with_call_events(
                    &contract_execution.checked_call_events,
                );
            let operation_name = match claim.target() {
                CFunctionContractClaimTarget::BodySafety => "contract claim: body safety",
                CFunctionContractClaimTarget::EnsureProposition(_) => "contract claim: proposition",
                CFunctionContractClaimTarget::ExceptionalEnsureProposition(_) => {
                    "contract claim: exceptional proposition"
                }
                CFunctionContractClaimTarget::EnsureResource(_) => "contract claim: resource",
                CFunctionContractClaimTarget::Effect => "contract claim: effect",
            };
            let claim_key = format!("{:?}", claim.key());
            let holds = crate::instrumentation::measure_operation(
                function.name(),
                &claim_key,
                operation_name,
                || {
                    claim_holds_on_some_path_set_of_every_case(
                        function,
                        claim,
                        &cases,
                        &checked_propositions,
                    )
                },
            );
            if timings {
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::ClaimFinished {
                        function: function.name().to_string(),
                        key: format!("{:?}", claim.key()),
                        elapsed: claim_started.elapsed(),
                    },
                );
            }
            let load_equalities = load_equality_capture.finish();
            holds.then(|| CVerifiedFunctionContractClaim {
                function: function.clone(),
                // Every claim is backed by authenticated complete body path
                // sets. Effect inference independently prepares and checks all
                // cases; a proposition completion alone cannot supply it.
                pointer_result_effects: infer_pointer_result_effects(function, &cases).into(),
                pointer_store_effects: infer_pointer_store_effects(function, &cases).into(),
                native_output_places_certified: infer_native_output_places(function, &cases),
                key: claim.key().clone(),
                load_equalities,
                loop_semantics: contract_execution.loop_semantics,
                applied_tactics: contract_execution.applied_tactics.clone(),
                checked_callees: contract_execution.checked_callees.clone(),
            })
        })
        .collect::<Option<Vec<_>>>();
    if timings {
        crate::instrumentation::emit(
            crate::instrumentation::VerificationEvent::ClaimPathsPrepared {
                function: function.name().to_string(),
                count: cases
                    .iter()
                    .flatten()
                    .filter_map(|view| view.prepared.get())
                    .filter_map(|prepared| prepared.as_ref().ok())
                    .map(Vec::len)
                    .sum(),
                elapsed: prepare_started.elapsed(),
            },
        );
    }
    // A case none of whose path sets could be prepared certifies nothing.
    if cases.iter().any(|alternatives| {
        alternatives
            .iter()
            .all(|view| view.prepared.get().is_some_and(Result::is_err))
    }) {
        return None;
    }
    claims
}

fn infer_native_output_places(
    function: &CFunction,
    cases: &[Vec<ContractPathSetView<'_>>],
) -> bool {
    if !crate::kernel::functions::independent_entry::native_output_entry_is_relevant(
        function.contract_interface(),
    ) {
        return false;
    }
    let has_normal_return = cases.iter().flatten().any(|view| {
        view.prepared(function).as_ref().is_ok_and(|paths| {
            paths
                .iter()
                .any(|path| matches!(path.outcome, CFunctionOutcome::Return { .. }))
        })
    });
    has_normal_return
        && cases.iter().all(|alternatives| {
            alternatives.iter().any(|view| {
                view.prepared(function).as_ref().is_ok_and(|paths| {
                    !paths.is_empty()
                        && paths.iter().all(|path| {
                            pointer_effect_entry_has_independent_binders(function, path)
                                && match &path.outcome {
                                    CFunctionOutcome::Return { .. } => {
                                        path.post_state.as_ref().is_some_and(|state| {
                                            check_native_output_places(
                                                state,
                                                function.contract_interface(),
                                                &path.assumptions,
                                            )
                                            .is_ok()
                                        })
                                    }
                                    CFunctionOutcome::Throw { .. }
                                    | CFunctionOutcome::VerificationDiverges => true,
                                    _ => false,
                                }
                        })
                })
            })
        })
}

/// Infer only semantic relationships present in authenticated body outcomes.
fn pointer_store_arguments(
    function: &CFunction,
    path: &CertifiedFunctionClaimPath,
) -> Option<Vec<CValue>> {
    function
        .contract_interface()
        .parameters()
        .iter()
        .map(|parameter| {
            if let Some(layout) = parameter.aggregate_layout() {
                let Some(CLocalBinding::AggregateObject {
                    layout: bound,
                    slot,
                    ..
                }) = path.body_entry_state.locals().binding(parameter.name())
                else {
                    return None;
                };
                if bound != layout {
                    return None;
                }
                path.body_entry_state
                    .memory()
                    .declared_aggregate_pointer(slot, bound)
                    .map(|pointer| CValue::Pointer(pointer.with_type(parameter.c_type())))
            } else {
                path.body_entry_state
                    .locals()
                    .get(parameter.name())
                    .cloned()
            }
        })
        .collect()
}

fn pointer_store_effect_holds(
    function: &CFunction,
    effect: &CPointerStoreEffect,
    path: &CertifiedFunctionClaimPath,
) -> bool {
    if !matches!(path.outcome, CFunctionOutcome::Return { .. }) {
        return matches!(
            path.outcome,
            CFunctionOutcome::Throw { .. } | CFunctionOutcome::VerificationDiverges
        );
    }
    let Some(post_state) = path.post_state.as_ref() else {
        return false;
    };
    let Some(arguments) = pointer_store_arguments(function, path) else {
        return false;
    };
    let Some(destination) = crate::kernel::functions::pointer_store_effects::selected(
        &path.body_entry_state,
        function.contract_interface(),
        &arguments,
        &effect.destination,
        &effect.destination_path,
    ) else {
        return false;
    };
    let Some(element_type) = crate::kernel::functions::pointer_store_effects::selected_element_type(
        &path.body_entry_state,
        &destination,
        &path.assumptions,
    ) else {
        return false;
    };
    let writes = crate::kernel::reasoning::memory_effect_write_accesses(&path.effect_facts);
    // Another possibly overlapping write can invalidate a cached final cell,
    // including when two independently bound parameters alias at the call.
    if writes.iter().any(|(pointer, bytes)| {
        pointer != destination.pointer()
            && !crate::kernel::memory_provenance::write_access_is_disjoint_from_load(
                pointer,
                *bytes,
                destination.pointer(),
                effect.value_type.byte_width(),
                &path.assumptions,
            )
    }) {
        return false;
    }
    if element_type != effect.value_type
        || !effect.value_type.is_pointer()
        || !crate::kernel::reasoning::memory_effect_write_accesses(&path.effect_facts).contains(&(
            destination.pointer().clone(),
            effect.value_type.byte_width(),
        ))
        || !post_state.memory().has_initialized_bytes_under(
            destination.pointer(),
            effect.value_type.byte_width(),
            &path.assumptions,
        )
    {
        return false;
    }
    let source = if let Some(field) = &effect.source_field {
        crate::kernel::functions::pointer_store_effects::field_source(
            &path.body_entry_state,
            function.contract_interface(),
            &arguments,
            field,
            effect.value_type,
            &path.assumptions,
        )
    } else {
        crate::kernel::functions::pointer_store_effects::selected(
            &path.body_entry_state,
            function.contract_interface(),
            &arguments,
            &effect.source,
            &effect.source_path,
        )
        .map(|source| source.with_type(effect.value_type))
    };
    source.is_some_and(|source| {
        source.designation().is_some()
            && post_state.memory().known_value(destination.pointer())
                == Some(CValue::Pointer(source))
    })
}

fn infer_pointer_store_effects(
    function: &CFunction,
    cases: &[Vec<ContractPathSetView<'_>>],
) -> Vec<CPointerStoreEffect> {
    if !crate::kernel::functions::independent_entry::has_store_roots(function.contract_interface())
    {
        return Vec::new();
    }

    let mut candidates = BTreeSet::new();
    for view in cases.iter().flatten() {
        let Ok(paths) = view.prepared(function) else {
            continue;
        };
        for path in paths {
            let independent = pointer_effect_entry_has_independent_binders(function, path);

            if !independent || !matches!(path.outcome, CFunctionOutcome::Return { .. }) {
                continue;
            }
            let Some(post_state) = path.post_state.as_ref() else {
                continue;
            };
            let Some(arguments) = pointer_store_arguments(function, path) else {
                continue;
            };
            let mut roots = function
                .contract_interface()
                .parameters()
                .iter()
                .enumerate()
                .filter(|(_, parameter)| parameter.c_type().is_pointer())
                .map(|(index, _)| CPointerEffectRoot::Parameter(index))
                .collect::<Vec<_>>();
            if function.contract_interface().aggregate_return_mode()
                == CAggregateReturnMode::Construction
            {
                roots.push(CPointerEffectRoot::ConstructionDestination);
            }
            for destination_root in &roots {
                // A by-value parameter is private callee storage. Its member
                // stores cannot become writes to the caller's argument image.
                if matches!(destination_root, CPointerEffectRoot::Parameter(index)
                    if function.parameters()[*index].aggregate_layout().is_some())
                {
                    continue;
                }
                let Some(destination) = crate::kernel::functions::pointer_store_effects::root(
                    &path.body_entry_state,
                    function.contract_interface(),
                    &arguments,
                    destination_root,
                ) else {
                    continue;
                };

                let fields = crate::kernel::functions::pointer_store_effects::pointer_fields(
                    &path.body_entry_state,
                    &destination,
                );

                for (destination_path, value_type) in fields {
                    let Some(cell) = crate::kernel::functions::pointer_store_effects::selected(
                        &path.body_entry_state,
                        function.contract_interface(),
                        &arguments,
                        destination_root,
                        &destination_path,
                    ) else {
                        continue;
                    };

                    let Some(CValue::Pointer(stored)) =
                        post_state.memory().known_value(cell.pointer())
                    else {
                        continue;
                    };
                    for field in crate::kernel::functions::pointer_store_effects::field_sources(
                        &path.body_entry_state,
                        function.contract_interface(),
                        &arguments,
                        &path.assumptions,
                    ) {
                        let effect = CPointerStoreEffect {
                            destination: destination_root.clone(),
                            destination_path: destination_path.clone().into(),
                            value_type,
                            source: CPointerEffectRoot::Parameter(field.parameter),
                            source_path: Default::default(),
                            source_field: Some(field),
                        };
                        let holds = pointer_store_effect_holds(function, &effect, path);

                        if holds {
                            candidates.insert(effect);
                        }
                    }
                    for source_root in &roots {
                        let Some(source) = crate::kernel::functions::pointer_store_effects::root(
                            &path.body_entry_state,
                            function.contract_interface(),
                            &arguments,
                            source_root,
                        ) else {
                            continue;
                        };
                        let mut source_paths = vec![Vec::new()];
                        if let (
                            Some(PointerDesignation::Object {
                                root,
                                path: stored_path,
                                ..
                            }),
                            Some(PointerDesignation::Object {
                                root: source_root,
                                path: source_path,
                                ..
                            }),
                        ) = (stored.designation(), source.designation())
                            && root == source_root
                            && stored_path.starts_with(source_path)
                            && let Some(path) = stored_path[source_path.len()..]
                                .iter()
                                .map(|selection| match selection {
                                    PointerDomainSelection::Member(name) => Some(name.clone()),
                                    _ => None,
                                })
                                .collect::<Option<Vec<_>>>()
                        {
                            source_paths.push(path);
                        }
                        if let (
                            Some(PointerDesignation::InputSelected {
                                input,
                                origin,
                                path: stored_path,
                                ..
                            }),
                            Some(PointerDesignation::InputSelected {
                                input: source_input,
                                origin: source_origin,
                                path: source_path,
                                ..
                            }),
                        ) = (stored.designation(), source.designation())
                            && input == source_input
                            && origin == source_origin
                            && stored_path.starts_with(source_path)
                            && let Some(path) = stored_path[source_path.len()..]
                                .iter()
                                .map(|selection| match selection {
                                    PointerDomainSelection::Member(name) => Some(name.clone()),
                                    _ => None,
                                })
                                .collect::<Option<Vec<_>>>()
                        {
                            source_paths.push(path);
                        }
                        for source_path in source_paths {
                            let effect = CPointerStoreEffect {
                                destination: destination_root.clone(),
                                destination_path: destination_path.clone().into(),
                                value_type,
                                source: source_root.clone(),
                                source_path: source_path.into(),
                                source_field: None,
                            };
                            let holds = pointer_store_effect_holds(function, &effect, path);
                            if holds {
                                candidates.insert(effect);
                            }
                        }
                    }
                }
            }
        }
    }
    candidates
        .into_iter()
        .filter(|effect| {
            cases.iter().all(|alternatives| {
                alternatives.iter().any(|view| {
                    view.prepared(function).as_ref().is_ok_and(|paths| {
                        !paths.is_empty()
                            && paths.iter().all(|path| {
                                pointer_effect_entry_has_independent_binders(function, path)
                                    && pointer_store_effect_holds(function, effect, path)
                            })
                    })
                })
            })
        })
        .collect::<Vec<_>>()
}

fn infer_pointer_result_effects(
    function: &CFunction,
    cases: &[Vec<ContractPathSetView<'_>>],
) -> Vec<CPointerResultEffect> {
    if !function.contract_interface().return_type().is_pointer()
        || function
            .contract_interface()
            .return_aggregate_layout()
            .is_some()
    {
        return Vec::new();
    }
    // A real normal return supplies candidates. An all-throw or divergent
    // body cannot invent arbitrary designation promises by vacuity.
    let mut candidates = BTreeSet::new();
    for view in cases.iter().flatten() {
        let Ok(paths) = view.prepared(function) else {
            continue;
        };
        for path in paths {
            let CFunctionOutcome::Return {
                value: CValue::Pointer(result),
                ..
            } = &path.outcome
            else {
                continue;
            };
            let Some(designation) = result.designation() else {
                continue;
            };
            candidates.insert(CPointerResultEffect::Opaque);
            if !pointer_effect_entry_has_independent_binders(function, path) {
                continue;
            }
            if let Some(arguments) = pointer_store_arguments(function, path) {
                for source in crate::kernel::functions::pointer_store_effects::field_sources(
                    &path.entry_state,
                    function.contract_interface(),
                    &arguments,
                    &path.assumptions,
                ) {
                    let effect = CPointerResultEffect::ExactFromPointerField { source };
                    if pointer_result_effect_holds(function, &effect, path) {
                        candidates.insert(effect);
                    }
                }
            }
            for (parameter, formal) in function
                .contract_interface()
                .parameters()
                .iter()
                .enumerate()
            {
                let Some(CValue::Pointer(input)) = path.entry_state.locals().get(formal.name())
                else {
                    continue;
                };
                let Some(input_designation) = input.designation() else {
                    continue;
                };
                let child_path = if designation == input_designation {
                    Vec::new()
                } else if let (
                    PointerDesignation::Object {
                        root,
                        path: result_path,
                        ..
                    },
                    PointerDesignation::Object {
                        root: input_root,
                        path: input_path,
                        ..
                    },
                ) = (designation, input_designation)
                {
                    if root != input_root || !result_path.starts_with(input_path) {
                        continue;
                    }
                    let Some(members) = result_path[input_path.len()..]
                        .iter()
                        .map(|selection| match selection {
                            PointerDomainSelection::Member(name) => Some(name.clone()),
                            PointerDomainSelection::Element(_) => None,
                        })
                        .collect::<Option<Vec<_>>>()
                    else {
                        continue;
                    };
                    members
                } else if let (
                    PointerDesignation::InputSelected {
                        input: result_input,
                        origin: result_origin,
                        path: result_path,
                        ..
                    },
                    PointerDesignation::InputSelected {
                        input: input_id,
                        origin: input_origin,
                        path: input_path,
                        ..
                    },
                ) = (designation, input_designation)
                {
                    if result_input != input_id
                        || result_origin != input_origin
                        || !result_path.starts_with(input_path)
                    {
                        continue;
                    }
                    let Some(members) = result_path[input_path.len()..]
                        .iter()
                        .map(|selection| match selection {
                            PointerDomainSelection::Member(name) => Some(name.clone()),
                            PointerDomainSelection::Element(_) => None,
                        })
                        .collect::<Option<Vec<_>>>()
                    else {
                        continue;
                    };
                    members
                } else {
                    continue;
                };
                let child_path: Arc<[String]> = child_path.into();
                for effect in [
                    CPointerResultEffect::FromParameter {
                        parameter,
                        child_path: child_path.clone(),
                    },
                    CPointerResultEffect::ExactFromParameter {
                        parameter,
                        child_path,
                    },
                ] {
                    if pointer_result_effect_holds(function, &effect, path) {
                        candidates.insert(effect);
                    }
                }
            }
        }
    }
    candidates
        .into_iter()
        .filter(|effect| {
            cases.iter().all(|alternatives| {
                alternatives.iter().any(|view| {
                    view.prepared(function).as_ref().is_ok_and(|paths| {
                        !paths.is_empty()
                            && paths.iter().all(|path| {
                                (matches!(effect, CPointerResultEffect::Opaque)
                                    || pointer_effect_entry_has_independent_binders(function, path))
                                    && pointer_result_effect_holds(function, effect, path)
                            })
                    })
                })
            })
        })
        .collect::<Vec<_>>()
}

fn pointer_effect_entry_has_independent_binders(
    function: &CFunction,
    path: &CertifiedFunctionClaimPath,
) -> bool {
    // The declaration-only reconstruction checks fresh, distinct scalar and
    // aggregate input binders, their qualifiers and their exact permitted
    // metadata. A second scalar-local check would reject private by-value
    // parameter objects despite their independently checked entry recipe.
    *path.independent_entry.get_or_init(|| {
        crate::kernel::functions::independent_entry::matches(
            function,
            &path.arguments,
            &path.caller_state,
            &path.entry_assumptions,
            path.checked_resource_guard_case.as_deref(),
        )
    })
}

fn pointer_result_effect_holds(
    function: &CFunction,
    effect: &CPointerResultEffect,
    path: &CertifiedFunctionClaimPath,
) -> bool {
    let CFunctionOutcome::Return { value, .. } = &path.outcome else {
        return matches!(
            path.outcome,
            CFunctionOutcome::Throw { .. } | CFunctionOutcome::VerificationDiverges
        );
    };
    let CValue::Pointer(result) = value else {
        return false;
    };
    if let CPointerResultEffect::ExactFromPointerField { source } = effect {
        let Some(arguments) = pointer_store_arguments(function, path) else {
            return false;
        };
        return crate::kernel::functions::pointer_store_effects::field_source(
            &path.entry_state,
            function.contract_interface(),
            &arguments,
            source,
            result.c_type(),
            &path.assumptions,
        )
        .is_some_and(|input| input == *result);
    }
    let (parameter, child_path, exact) = match effect {
        CPointerResultEffect::FromParameter {
            parameter,
            child_path,
        } => (parameter, child_path, false),
        CPointerResultEffect::ExactFromParameter {
            parameter,
            child_path,
        } => (parameter, child_path, true),
        // This marker only prevents erasure and promises no object or access.
        CPointerResultEffect::Opaque => return true,
        CPointerResultEffect::ExactFromPointerField { .. } => return false,
    };
    let Some(CValue::Pointer(input)) = path
        .entry_state
        .locals()
        .get(function.contract_interface().parameters()[*parameter].name())
    else {
        return false;
    };
    let selected = if child_path.is_empty() {
        input.clone()
    } else {
        let Some(selected) = path
            .entry_state
            .memory()
            .checked_member_pointer_by_path(input, child_path)
        else {
            return false;
        };
        selected
    };
    selected.designation().is_some()
        && selected.same_designation(result)
        && (!exact || selected.pointer() == result.pointer())
}

/// One complete path set, prepared once and reused across claim checks.
struct ContractPathSetView<'a> {
    set: &'a CContractPathSet,
    capture_failure: bool,
    prepared: std::cell::OnceCell<
        Result<Vec<CertifiedFunctionClaimPath>, ContractPathPreparationFailure>,
    >,
}

impl ContractPathSetView<'_> {
    fn prepared(
        &self,
        function: &CFunction,
    ) -> &Result<Vec<CertifiedFunctionClaimPath>, ContractPathPreparationFailure> {
        self.prepared.get_or_init(|| {
            crate::instrumentation::measure_operation(
                function.name(),
                "contract certification",
                "contract path preparation",
                || {
                    self.set
                        .paths
                        .iter()
                        .enumerate()
                        .map(|(index, path)| {
                            let checked_resource_claims = self
                                .set
                                .checked_resource_claims
                                .get(index)
                                .cloned()
                                .unwrap_or_default();
                            let checked_resource_transition = self
                                .set
                                .checked_resource_transitions
                                .get(index)
                                .copied()
                                .unwrap_or(false);
                            prepare_function_claim_path(
                                function,
                                path,
                                checked_resource_claims,
                                checked_resource_transition,
                                self.set
                                    .deferred_contract_exits
                                    .get(index)
                                    .copied()
                                    .unwrap_or(false),
                                self.set
                                    .deferred_contract_exit_errors
                                    .get(index)
                                    .cloned()
                                    .unwrap_or(None),
                                self.set
                                    .checked_returned_resources
                                    .get(index)
                                    .cloned()
                                    .unwrap_or_else(crate::kernel::ResourceContext::new),
                                self.capture_failure,
                                self.set
                                    .boundary_transfers
                                    .get(index)
                                    .and_then(Option::as_deref),
                                self.set.checked_resource_guard_cases.get(index).cloned(),
                            )
                            .map_err(|mut failure| {
                                failure.reason = format!(
                                    "execution path {index} is invalid: {}",
                                    failure.reason
                                );
                                failure
                            })
                        })
                        .collect()
                },
            )
        })
    }
}

fn contract_path_set_views(
    contract_execution: &CFunctionContractExecution,
    capture_failure: bool,
) -> Vec<Vec<ContractPathSetView<'_>>> {
    contract_execution
        .cases()
        .iter()
        .map(|alternatives| {
            alternatives
                .iter()
                .map(|set| ContractPathSetView {
                    set,
                    capture_failure,
                    prepared: std::cell::OnceCell::new(),
                })
                .collect()
        })
        .collect()
}

/// A claim holds when every resource-guard case has one path set on all of
/// whose paths it holds. Each set is a complete execution of the function
/// under its case, so one certifying set is authority for the case.
fn claim_holds_on_some_path_set_of_every_case(
    function: &CFunction,
    claim: &CFunctionContractClaim,
    cases: &[Vec<ContractPathSetView<'_>>],
    checked_propositions: &CheckedPropositionIndex<'_>,
) -> bool {
    cases.iter().all(|alternatives| {
        alternatives.iter().any(|view| {
            if let CFunctionContractClaimTarget::EnsureResource(index) = claim.target()
                && function.resource_ensures().get(*index).is_some_and(|spec| {
                    spec.native_record_places().is_empty()
                        && spec.native_span_requirements().is_empty()
                })
                && view.set.checked_resource_claims.len() == view.set.paths.len()
                && view.set.checked_resource_transitions.len() == view.set.paths.len()
                && view
                    .set
                    .checked_resource_transitions
                    .iter()
                    .all(|checked| *checked)
                && view
                    .set
                    .checked_resource_claims
                    .iter()
                    .all(|claims| claims.contains(&CFunctionContractClaimKey::Ensure(*index)))
            {
                // This claim was checked against the completed proof outcome
                // on every path, including allocation lifetime. It is already
                // the exact contract claim; preparing the raw path would
                // repeat the contract exit transition and can lose the proof's
                // checked post-return resource exchange.
                return true;
            }
            view.prepared(function).as_ref().is_ok_and(|paths| {
                paths.iter().all(|path| {
                    function_claim_holds_on_prepared_path(
                        function,
                        claim,
                        path,
                        checked_propositions,
                        view.set.completion_origin_state.as_ref(),
                    )
                })
            })
        })
    })
}

/// Reports the exact contract claims that the checked execution frontier does
/// not establish. This is diagnostic information only: unlike the companion
/// certification API, it cannot mint proof objects.
///
/// `None` means the frontier itself is incomplete or could not be prepared for
/// claim checking. An empty vector means every claim holds.
pub fn c_unverified_function_contract_claims(
    function: &CFunction,
    contract_execution: &CFunctionContractExecution,
) -> Result<Vec<CFunctionContractClaimKey>, String> {
    c_unverified_function_contract_claims_with_checked_propositions(
        function,
        contract_execution,
        &[],
    )
}

/// Diagnostic counterpart to checked-proposition-aware finalization. Keeping
/// the same evidence here ensures a later failing claim does not make an
/// already checked proposition look unproved in the reported claim list.
pub(crate) fn c_unverified_function_contract_claims_with_checked_propositions(
    function: &CFunction,
    contract_execution: &CFunctionContractExecution,
    checked_propositions: &[CCheckedFunctionProposition],
) -> Result<Vec<CFunctionContractClaimKey>, String> {
    c_unverified_function_contract_claims_diagnostic(
        function,
        contract_execution,
        checked_propositions,
    )
    .map_err(|failure| failure.reason)
}

pub(crate) fn c_unverified_function_contract_claims_diagnostic(
    function: &CFunction,
    contract_execution: &CFunctionContractExecution,
    checked_propositions: &[CCheckedFunctionProposition],
) -> Result<Vec<CFunctionContractClaimKey>, ContractPathPreparationFailure> {
    if !contract_execution.is_complete() {
        return Err("certification produced no paths".to_string().into());
    }
    let cases = contract_path_set_views(contract_execution, true);
    let checked_propositions = checked_proposition_index(checked_propositions);
    let mut unverified = missing_function_contract_claim_keys(function);
    let claim_unverified = function
        .contract_claims()
        .iter()
        .filter(|claim| {
            !claim_holds_on_some_path_set_of_every_case(
                function,
                claim,
                &cases,
                &checked_propositions,
            )
        })
        .map(|claim| claim.key().clone())
        .collect::<Vec<_>>();
    for key in claim_unverified {
        if !unverified.contains(&key) {
            unverified.push(key);
        }
    }
    // A case none of whose path sets could be prepared names the first
    // reason.
    for alternatives in &cases {
        let failures = alternatives
            .iter()
            .filter_map(|view| view.prepared.get())
            .filter_map(|prepared| prepared.as_ref().err())
            .collect::<Vec<_>>();
        if !failures.is_empty() && failures.len() == alternatives.len() {
            return Err((*failures[0]).clone());
        }
    }
    Ok(unverified)
}

/// Certifies one contract claim only after a kernel-produced complete
/// execution frontier establishes that exact claim for the exact function.
pub fn c_verified_function_contract_claim(
    function: &CFunction,
    key: CFunctionContractClaimKey,
    execution: &CFunctionContractExecution,
) -> Option<CVerifiedFunctionContractClaim> {
    c_verified_function_contract_claims(function, execution)?
        .into_iter()
        .find(|proof| proof.key == key)
}

/// Packages an opaque rule only after every recorded contract claim has a
/// certificate for this exact function.
/// This checks claim coverage and function identity; it does not reconstruct
/// the symbolic entry chosen by the caller of contract certification. Reusable
/// rules require certification at an entry representing the declared input
/// domain. See `docs/internals/kernel.md`, "Source obligations and checked
/// evidence".
pub fn c_verified_function_rule(
    function: CFunction,
    proofs: &[CVerifiedFunctionContractClaim],
) -> Option<CVerifiedFunctionRule> {
    if function.is_program_entry()
        || !function.verified_direct_contract_supported()
        || function.contract_claims().is_empty()
        || !function_contract_claims_are_complete(&function)
        || proofs.iter().any(|proof| proof.function != function)
        || function
            .contract_claims()
            .iter()
            .any(|claim| !proofs.iter().any(|proof| proof.key == *claim.key()))
    {
        return None;
    }
    // The weakest semantics any claim saw: a loop summarized for one claim
    // was not shown to exit for that claim.
    let loop_semantics = if proofs
        .iter()
        .all(|proof| proof.loop_semantics == CLoopSemantics::ApplyVerifiedRules)
    {
        CLoopSemantics::ApplyVerifiedRules
    } else {
        CLoopSemantics::Verify
    };
    Some(CVerifiedFunctionRule {
        source_declaration: None,
        native_output_places_certified: proofs
            .iter()
            .any(|proof| proof.native_output_places_certified),
        pointer_store_effects: proofs
            .iter()
            .flat_map(|proof| proof.pointer_store_effects.iter().cloned())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>()
            .into(),
        pointer_result_effects: proofs
            .iter()
            .flat_map(|proof| proof.pointer_result_effects.iter().cloned())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>()
            .into(),
        function,
        loop_semantics,
        checked_callees: crate::kernel::termination::merge_checked_callees(
            proofs.iter().map(|proof| proof.checked_callees.as_ref()),
        ),
        applied_tactics: proofs
            .iter()
            .flat_map(|proof| proof.applied_tactics.iter().cloned())
            .collect(),
    })
}

/// Packages a body-less external contract as an opaque assumption. The
/// contract still has to be structurally complete and representable by the
/// kernel, but no body-safety or postcondition proof is claimed for it.
/// A construction return assumes completion into the checked caller-owned
/// destination, including its initialized value fields. Ordinary writable
/// buffers and void construction parameters receive no such guarantee.
pub fn c_external_function_rule(function: CFunction) -> Option<CExternalFunctionRule> {
    (!function.is_program_entry()
        && function
            .contract_interface()
            .construction_parameter()
            .is_none()
        && function.opaque_contract_supported()
        && function
            .contract_interface()
            .initialization_output_selectors()
            .is_some_and(|outputs| outputs.is_empty())
        && !function.contract_claims().is_empty()
        && function_contract_claims_are_complete(&function))
    .then_some(CExternalFunctionRule {
        function,
        scoped_unselected: false,
        representation_copy: None,
    })
}

/// Builds an untrusted ranking plan. Supplying a plan is not evidence; the
/// kernel validates it together with the exact verified C functions in
/// [`c_verified_function_termination_rules`].
pub fn c_function_termination_plan(
    function_name: impl Into<String>,
    recursive_measure: Option<CFunctionTerminationMeasure>,
    loop_measures: impl IntoIterator<Item = (usize, CLoopTerminationMeasure)>,
) -> CFunctionTerminationPlan {
    CFunctionTerminationPlan {
        function_name: function_name.into(),
        recursive_measure,
        loop_measures: loop_measures.into_iter().collect(),
    }
}

/// Creates a scoped hypothesis used only while the language layer verifies one
/// closed set of mutually dependent C contracts. The verification transaction
/// returns no rules if any hypothesized contract fails independent kernel
/// certification, which is the standard partial-correctness recursion rule.
///
/// This is crate-private so an external caller cannot install an unverified
/// recursive contract into a kernel execution environment.
pub(crate) fn c_recursive_function_contract_hypothesis(
    function: CFunction,
) -> Option<CVerifiedFunctionRule> {
    (!function.is_program_entry()
        && function.verified_direct_contract_supported()
        && !function.contract_claims().is_empty()
        && function_contract_claims_are_complete(&function))
    .then_some(CVerifiedFunctionRule {
        source_declaration: None,
        pointer_result_effects: Default::default(),
        pointer_store_effects: Default::default(),
        native_output_places_certified: false,
        function,
        // A hypothesis certified nothing, so it says nothing about loops.
        loop_semantics: CLoopSemantics::Verify,
        checked_callees: None,
        applied_tactics: Default::default(),
    })
}

/// Creates a scoped body-independent assumption for a concrete function whose
/// proof is outside the current CLI selection. The interface is checked for
/// complete, representable direct claims, including the narrow exceptional
/// channel that public `extern` declarations do not support. The caller must
/// remove this rule before publishing the selected result's environment.
/// This is the kernel boundary for conditional partial verification; it never
/// certifies the unselected body.
pub(crate) fn c_unselected_function_contract_assumption(
    function: CFunction,
) -> Option<CExternalFunctionRule> {
    (!function.is_program_entry()
        && function.verified_direct_contract_supported()
        && !function.contract_claims().is_empty()
        && function_contract_claims_are_complete(&function))
    .then_some(CExternalFunctionRule {
        function,
        scoped_unselected: true,
        representation_copy: None,
    })
}

/// Structural contract coverage is part of the rule boundary, not merely a
/// convention of the surface lowering. A body-safety claim cannot stand in
/// for an omitted postcondition. An explicitly declared mutable frame needs
/// an effect claim even when the frame is empty on a particular execution
/// path; a resource-derived frame is covered by its resource transition.
fn function_contract_claims_are_complete(function: &CFunction) -> bool {
    let claims = function.contract_claims();
    (0..function.contract_ensures().len()).all(|index| {
        claims.iter().any(|claim| {
            matches!(
                claim.target(),
                CFunctionContractClaimTarget::EnsureProposition(claim_index)
                    if *claim_index == index
            )
        })
    }) && (0..function.exceptional_ensures().len()).all(|index| {
        claims.iter().any(|claim| {
            matches!(
                claim.target(),
                CFunctionContractClaimTarget::ExceptionalEnsureProposition(claim_index)
                    if *claim_index == index
            )
        })
    }) && (0..function.resource_ensures().len()).all(|index| {
        claims.iter().any(|claim| {
            matches!(
                claim.target(),
                CFunctionContractClaimTarget::EnsureResource(claim_index)
                    if *claim_index == index
            )
        })
    }) && (!function.contract_effect_claim_required()
        || function.contract_mutable().is_empty()
        || claims
            .iter()
            .any(|claim| matches!(claim.target(), CFunctionContractClaimTarget::Effect)))
}

/// Returns diagnostic keys for obligations that have no corresponding claim.
/// The public key type predates separate proposition/resource vectors, so the
/// target index is used for an unclaimed diagnostic entry.
fn missing_function_contract_claim_keys(function: &CFunction) -> Vec<CFunctionContractClaimKey> {
    let claims = function.contract_claims();
    let mut missing = Vec::new();
    for index in 0..function.contract_ensures().len() {
        if !claims.iter().any(|claim| {
            matches!(
                claim.target(),
                CFunctionContractClaimTarget::EnsureProposition(claim_index)
                    if *claim_index == index
            )
        }) {
            missing.push(CFunctionContractClaimKey::Ensure(index));
        }
    }
    for index in 0..function.exceptional_ensures().len() {
        if !claims.iter().any(|claim| {
            matches!(
                claim.target(),
                CFunctionContractClaimTarget::ExceptionalEnsureProposition(claim_index)
                    if *claim_index == index
            )
        }) {
            missing.push(CFunctionContractClaimKey::ExceptionalEnsure(index));
        }
    }
    for index in 0..function.resource_ensures().len() {
        if !claims.iter().any(|claim| {
            matches!(
                claim.target(),
                CFunctionContractClaimTarget::EnsureResource(claim_index)
                    if *claim_index == index
            )
        }) {
            let key = CFunctionContractClaimKey::Ensure(index);
            if !missing.contains(&key) {
                missing.push(key);
            }
        }
    }
    if function.contract_effect_claim_required()
        && !function.contract_mutable().is_empty()
        && !claims
            .iter()
            .any(|claim| matches!(claim.target(), CFunctionContractClaimTarget::Effect))
    {
        missing.push(CFunctionContractClaimKey::Effect(0));
    }
    missing
}

#[cfg(test)]
mod checked_proposition_index_tests {
    use super::*;

    fn route(variable: u64, value: bool) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(Variable(variable))),
                Box::new(Bitvector32Term::Constant(1)),
            ),
            value,
        )
    }

    fn lowering_candidate(marker: bool, facts: Vec<Proposition>) -> SpecPropositionPath {
        SpecPropositionPath {
            proposition: Proposition::ConditionIs(ConditionTerm::Constant(marker), true),
            facts: facts.into_iter().map(ExecutionPureFact::new).collect(),
            obligations: Vec::new(),
            introductions: LoweringIntroductions::new(),
        }
    }

    #[test]
    fn outcome_facts_select_exactly_one_lowering_candidate() {
        let selected_route = route(71_000, true);
        let paths = vec![
            lowering_candidate(false, vec![route(71_001, true)]),
            lowering_candidate(true, vec![selected_route.clone()]),
        ];
        let assumptions = PureFactContext::new().assume_proposition(selected_route);

        let selected = exactly_selected_spec_proposition_path(&paths, &assumptions)
            .expect("the exact second candidate should be selected");
        assert_eq!(selected.proposition, paths[1].proposition);
    }

    #[test]
    fn read_equations_follow_a_selected_route_without_selecting_one() {
        let route = route(71_030, true);
        let context = PureFactContext::new().assume_proposition(route.clone());
        let pointer = Pointer::symbolic(Variable(71_031));
        let equation = ExecutionPureFact::logical_read_equation(
            pointer.clone(),
            Pointer::loaded_value(&intern_c_memory(CMemory::new()), &pointer),
        );
        let mut paths = vec![
            lowering_candidate(false, vec![]),
            lowering_candidate(true, vec![route]),
        ];
        for path in &mut paths {
            path.facts.push(equation.clone());
        }
        assert_eq!(
            exactly_selected_spec_proposition_path(&paths, &context)
                .unwrap()
                .proposition,
            paths[1].proposition
        );
        assert!(exactly_selected_spec_proposition_path(&paths, &PureFactContext::new()).is_none());
        let mut forged = equation.clone();
        forged.certified = false;
        paths[1].facts = vec![forged].into();
        assert!(exactly_selected_spec_proposition_path(&paths, &context).is_none());
    }

    #[test]
    fn outcome_selection_rejects_ambiguous_or_unrouted_candidates() {
        let shared = route(71_010, true);
        let assumptions = PureFactContext::new().assume_proposition(shared.clone());
        let ambiguous = vec![
            lowering_candidate(false, vec![shared.clone()]),
            lowering_candidate(true, vec![shared]),
        ];
        assert!(exactly_selected_spec_proposition_path(&ambiguous, &assumptions).is_none());

        let unrouted = vec![
            lowering_candidate(false, Vec::new()),
            lowering_candidate(true, Vec::new()),
        ];
        assert!(exactly_selected_spec_proposition_path(&unrouted, &assumptions).is_none());
    }

    #[test]
    fn outcome_selection_work_is_independent_of_ambient_fact_count() {
        let selected_route = route(71_020, true);
        let paths = vec![
            lowering_candidate(false, vec![route(71_021, true)]),
            lowering_candidate(true, vec![selected_route.clone()]),
            lowering_candidate(false, vec![route(71_022, true)]),
        ];
        let context = |unrelated: u64| {
            (0..unrelated).fold(
                PureFactContext::new().assume_proposition(selected_route.clone()),
                |context, offset| context.assume_proposition(route(72_000 + offset, true)),
            )
        };
        let small = context(8);
        let large = context(2_048);
        // The index keys the facts once, on first use; the selection itself
        // must not depend on how many there were.
        small.build_stated_proposition_index();
        large.build_stated_proposition_index();
        let (_, small_work) = crate::instrumentation::measure_deterministic_work(|| {
            exactly_selected_spec_proposition_path(&paths, &small)
        });
        let (_, large_work) = crate::instrumentation::measure_deterministic_work(|| {
            exactly_selected_spec_proposition_path(&paths, &large)
        });
        assert_eq!(small_work, large_work);
    }

    #[test]
    fn completions_are_indexed_by_the_claim_they_closed() {
        let truth = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
        let checked = |claim: Option<CFunctionContractClaimTarget>| {
            let function = CFunction::new(CType::Void, "indexed", Vec::new(), CStatement::Skip);
            let specification = CFunctionSpecification::new(
                CState::new(),
                Vec::new(),
                Vec::new(),
                CFunctionOutcome::Return {
                    value: CValue::Void,
                    state: Box::new(CState::new()),
                },
            );
            CCheckedFunctionProposition {
                function,
                specification,
                proposition: truth.clone(),
                claim,
            }
        };
        let first = CFunctionContractClaimTarget::EnsureProposition(0);
        let second = CFunctionContractClaimTarget::EnsureProposition(1);
        let completions = vec![
            checked(Some(first.clone())),
            checked(None),
            checked(Some(first.clone())),
        ];
        let index = checked_proposition_index(&completions);
        assert_eq!(index.by_claim.get(&first).map(Vec::len), Some(2));
        // The same proposition closes no claim it was not opened for.
        assert!(!index.by_claim.contains_key(&second));
        assert_eq!(index.by_claim.len(), 1);
    }

    #[test]
    fn certification_does_not_promote_body_facts_to_entry_premises() {
        let function = CFunction::new(
            CType::Int32,
            "entry_resource_fact_boundary",
            Vec::new(),
            c_return(c_int32_literal(0)),
        );
        // This is deliberately a fact recorded by execution after entry.  It
        // must not make an entry-dependent resource term evaluable during
        // certification setup.
        let body_fact = Proposition::ConditionIs(
            ConditionTerm::signed_less_than(
                Bitvector32Term::Variable(Variable(93_001)),
                Bitvector32Term::Constant(8),
            ),
            true,
        );
        let state = CState::new();
        let proposition = Proposition::CFunctionExecutes {
            state: Box::new(state.clone()),
            function: Box::new(function.clone()),
            arguments: Vec::new(),
            outcome: CFunctionOutcome::Return {
                value: CValue::Int32(Bitvector32Term::Constant(0)),
                state: Box::new(state),
            },
        };
        let fact = ExecutionPureFact::new(body_fact.clone());
        let path = SymbolicCExecutionPath {
            completion_origin: None,
            assumptions: PureFactContext::new(),
            post_assumptions: Some(PureFactContext::new().assume_proposition(body_fact.clone())),
            facts: vec![fact.clone()].into(),
            effect_facts: Vec::new().into(),
            obligations: Vec::new(),
            theorem: Theorem::new(wrap_proof_facts(
                proposition,
                &PureFactContext::new(),
                &[fact],
                &[],
            )),

            loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
        };
        let (_, _, _, entry_assumptions) =
            super::super::certified_function_path_parts(&function, &path)
                .expect("the exact function path should be accepted");
        assert!(!entry_assumptions.contains_proposition_fact(&body_fact));
    }
}

#[cfg(test)]
mod heap_status_equality_tests {
    use super::*;

    /// Outcome and effect equality share the same heap-status check, because
    /// initialization state changes what a later load can return.
    #[test]
    fn outcome_equality_distinguishes_heap_statuses() {
        let block = Pointer {
            block: PointerBlock::Heap(424_242),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut base = CMemory::new().with_block(block.block.clone(), 4);
        std::sync::Arc::make_mut(&mut base.heap)
            .live_allocations
            .insert(block.clone(), Bitvector32Term::Constant(4));
        std::sync::Arc::make_mut(&mut base.heap)
            .zeroed_allocations
            .insert(block.clone());
        let mut other = base.clone();
        std::sync::Arc::make_mut(&mut other.heap)
            .zeroed_allocations
            .remove(&block);
        std::sync::Arc::make_mut(&mut other.heap)
            .uninitialized_allocations
            .insert(block.clone());
        assert_ne!(base.heap, other.heap, "setup: the heap statuses differ");
        let assumptions = PureFactContext::new();
        assert!(!c_memories_definitionally_equal(
            &base,
            &other,
            &assumptions
        ));
        assert!(!c_effect_memories_definitionally_equal(
            &base,
            &other,
            &assumptions,
        ));

        let left = CFunctionOutcome::Return {
            value: CValue::Int32(Bitvector32Term::Constant(0)),
            state: Box::new(CState::new().with_memory(base)),
        };
        let right = CFunctionOutcome::Return {
            value: CValue::Int32(Bitvector32Term::Constant(0)),
            state: Box::new(CState::new().with_memory(other)),
        };
        assert!(!c_function_outcomes_program_state_definitionally_equal(
            &left,
            &right,
            &assumptions,
        ));
    }
}

#[cfg(test)]
mod unproved_path_obligation_message_tests {
    use super::*;

    /// A certification refusal names the condition by the sentence its
    /// lowering wrote, never as a kernel term dump.
    #[test]
    fn names_the_obligation_by_its_context_without_a_term_dump() {
        let condition = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(Bitvector32Term::Variable(Variable(7))),
                Box::new(Bitvector32Term::Constant(3)),
            ),
            true,
        );
        let with_context = ProofObligation::verification_condition(condition.clone())
            .with_context("loop ranking component `n` is nonnegative at the back edge");
        assert_eq!(
            unproved_path_obligation_message(&with_context),
            "loop ranking component `n` is nonnegative at the back edge"
        );
        let without_context = ProofObligation::verification_condition(condition);
        let message = unproved_path_obligation_message(&without_context);
        assert!(!message.contains("ConditionIs"), "{message}");
        assert!(!message.contains("Variable"), "{message}");
    }
}

#[cfg(test)]
mod wide_range_reader_tests {
    use super::*;
    // Claim framing compares the declared domain as well as endpoint bits.
    #[test]
    fn wide_claim_range_lists_do_not_use_signed_equalities() {
        let base = Pointer::symbolic(Variable(984_400));
        let wide = CMemoryRange::new_wide(
            base.clone(),
            Bitvector32Term::UInt64Constant(0),
            Bitvector32Term::UInt64Constant(1 << 33),
            1,
        );
        let narrow = CMemoryRange::new_with_element_width(base, 0u32.into(), 1u32.into(), 1);
        let facts = PureFactContext::new();
        assert!(memory_range_lists_definitionally_equal(
            std::slice::from_ref(&wide),
            std::slice::from_ref(&wide),
            &facts
        ));
        assert!(!memory_range_lists_definitionally_equal(
            &[wide],
            &[narrow],
            &facts
        ));
    }
}
