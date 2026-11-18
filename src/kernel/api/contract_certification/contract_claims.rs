use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

mod publication;
pub(crate) use publication::PublishedFunctionOutcome;

mod completion;
pub(crate) use completion::{
    CompletedContractExecution, ContractBodyProof, ContractCompletionGoal, ContractExecutionOwner,
    ContractProofProgress, WholeContractRoot,
};

mod retained_context;
use retained_context::expand_certification_exit;
pub(crate) use retained_context::{RetainedClosingEntry, RetainedClosingFootprint};

mod closing;
#[cfg(test)]
pub(crate) use closing::check_empty_footprint as check_empty_contract_write_footprint;
pub(crate) use closing::{
    ClosedContractExit, ContractClosingContext, ContractClosingRefusal, ContractExitObligations,
};

/// A specification made from this path's own entry premises. Generic
/// specifications can add arbitrary premises and carry no such authority.
#[cfg(test)]
pub(crate) struct CheckedPathSpecification {
    function: ProgramFunction,
    specification: FunctionSpecification,
    theorem: Theorem,
    path_origin: Theorem,
}

#[cfg(test)]
impl CheckedPathSpecification {
    pub(crate) fn new(function: &ProgramFunction, path: &SymbolicExecutionPath) -> Option<Self> {
        let mut conclusion = path.theorem.proposition();
        while let Proposition::Implies(_, body) = conclusion {
            conclusion = body;
        }
        let Proposition::ProgramFunctionVerifies {
            state,
            function: proved_function,
            arguments,
            outcome,
        } = conclusion
        else {
            return None;
        };
        if proved_function.as_ref() != function {
            return None;
        }
        let specification = FunctionSpecification::new(
            state.as_ref().clone(),
            arguments.clone(),
            path.assumptions.pure_facts(),
            outcome.clone(),
        );
        let theorem = prove_program_function_satisfies_specification_from_symbolic_path(
            function.clone(),
            specification.clone(),
            path,
        )?;
        Some(Self {
            function: function.clone(),
            specification,
            theorem,
            path_origin: path.theorem.clone(),
        })
    }

    pub(crate) fn specification(&self) -> &FunctionSpecification {
        &self.specification
    }

    pub(crate) fn complete(
        &self,
        completion: &crate::kernel::proof::CheckedProposition,
        path: &SymbolicExecutionPath,
    ) -> Result<CheckedFunctionProposition, String> {
        if !std::sync::Arc::ptr_eq(&self.path_origin.proposition, &path.theorem.proposition) {
            return Err("the specification belongs to a different checked path".to_string());
        }
        let mut checked = program_checked_function_proposition_with_reason(
            &self.function,
            &self.specification,
            &self.theorem,
            completion,
            path,
        )?;
        checked.path_origin = Some(self.path_origin.clone());
        Ok(checked)
    }
}

#[cfg(test)]
pub(crate) fn program_checked_function_proposition_with_reason(
    function: &ProgramFunction,
    specification: &FunctionSpecification,
    theorem: &Theorem,
    completion: &crate::kernel::proof::CheckedProposition,
    path: &SymbolicExecutionPath,
) -> Result<CheckedFunctionProposition, String> {
    fn conclusion(theorem: &Theorem) -> &Proposition {
        let mut proposition = theorem.proposition();
        while let Proposition::Implies(_, body) = proposition {
            proposition = body;
        }
        proposition
    }
    match conclusion(theorem) {
        Proposition::ProgramFunctionPartiallySatisfiesSpecification {
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
    // caller-supplied state. Its producer checked the body against its
    // retained trace and applied the contract exit rule to that same trace.
    match conclusion(path.theorem()) {
        Proposition::ProgramFunctionVerifies {
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
        FunctionOutcome::Return { .. } => false,
        FunctionOutcome::Throw { .. } => true,
        FunctionOutcome::VerificationDiverges => {
            return Err("the checked path outcome is verification divergence".to_string());
        }
        FunctionOutcome::UndefinedBehavior(_) => {
            return Err("the checked path outcome is undefined behavior".to_string());
        }
        FunctionOutcome::RuntimeError(
            RuntimeError::FunctionContract(message)
            | RuntimeError::UnsuppliedResourceValue(message),
        ) => {
            return Err(format!(
                "the checked path outcome is a function-contract runtime error: {message}"
            ));
        }
        FunctionOutcome::RuntimeError(error) => {
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
    let matches_program_state = |outcome: &FunctionOutcome| {
        let (value, state, exceptional) = match outcome {
            FunctionOutcome::Return { value, state } => (value, state, false),
            FunctionOutcome::Throw { value, state } => (value, state, true),
            _ => return false,
        };
        completed.is_exceptional == exceptional
            && value == &completed.result
            && memories_match_up_to_cached_reads(completed.state.memory(), state.memory())
            && completed.state.locals() == state.locals()
            && completed.state.aggregate_destination == state.aggregate_destination
    };
    // Resource/population representation can change at exit. Aggregate return
    // completion can also retain the body's sparse block layout, while the
    // exit rule restores the caller's layout. Only the producer's checked
    // correspondence admits that difference; memory contents are never erased
    // or matched by source spelling. The completion remains tied to this
    // checked program outcome when its claim judgment is consumed.
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
    Ok(CheckedFunctionProposition {
        path_origin: None,
        function: function.clone(),
        specification: specification.clone(),
        proposition: completion.proposition().clone(),
        claim: completion.claim().cloned(),
    })
}

/// Compare exact states while allowing only producer-recorded caching of
/// their own typed reads. Each hop descends the newer state's derivation;
/// unrelated cells, facts, and execution history are never visited. Read
/// identity alone is insufficient: forgotten knowledge, havoc, stores, and
/// allocation changes remain barriers even when some reads are unchanged.
pub(in crate::kernel) fn memories_match_up_to_cached_reads(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
) -> bool {
    let mut left = intern_memory_ref(left);
    let mut right = intern_memory_ref(right);
    while left != right {
        crate::instrumentation::record_deterministic_work(1);
        if left.arena_id().0 != right.arena_id().0 {
            return false;
        }
        let newer = if left.arena_id().1 > right.arena_id().1 {
            &mut left
        } else {
            &mut right
        };
        let Some(derivation) = newer.derivation() else {
            return false;
        };
        let MemoryDerivation::CellsSeeded { base, run } = derivation.as_ref() else {
            return false;
        };
        if !matches!(
            run.value_mode(),
            crate::kernel::primitives::RunValueMode::Load
        ) || run.element_width() != run.value_width()
            || base.read_identity() != run.source().read_identity()
        {
            return false;
        }
        *newer = base.clone();
    }
    true
}

#[cfg(test)]
fn checked_proposition_index(
    checked_propositions: &[CheckedFunctionProposition],
) -> CheckedPropositionIndex<'_> {
    let mut index = CheckedPropositionIndex::default();
    for checked in checked_propositions {
        if let Some(claim) = &checked.claim {
            if let Some(origin) = &checked.path_origin {
                index
                    .by_path
                    .entry(claim.clone())
                    .or_default()
                    .insert(std::sync::Arc::as_ptr(&origin.proposition) as usize);
            }
            if let Some(key) = literal_completion_key(checked.specification.outcome()) {
                index
                    .by_literal_outcome
                    .entry(claim.clone())
                    .or_default()
                    .entry(key)
                    .or_default()
                    .push(checked);
            }
            index
                .by_claim
                .entry(claim.clone())
                .or_default()
                .push(checked);
        }
    }
    index
}

#[cfg(test)]
mod cached_read_completion_tests {
    use super::*;
    use crate::kernel::proof::ProofObligation;
    use crate::kernel::proof::*;

    fn pointer(block: &str, offset: i32) -> Address {
        Address {
            base: block.into(),
            offset: AddressOffset::Constant(i64::from(offset)),
        }
    }

    fn cache(
        memory: &SymbolicMemory,
        source: &SymbolicMemory,
        count: u32,
        width: u32,
    ) -> SymbolicMemory {
        memory.clone().with_seeded_cells(
            pointer("cache", 0),
            width,
            ProgramType::Int32,
            0,
            count,
            intern_memory_ref(source),
        )
    }

    fn check_completion(
        memory: SymbolicMemory,
        published: SymbolicMemory,
    ) -> Result<CheckedFunctionProposition, String> {
        let proposition = Proposition::condition_is(ConditionTerm::Constant(true), true);
        let state = ExecutionState::new().with_memory(published);
        let function = program_function(
            ProgramType::Int32,
            "cached_read_completion",
            vec![],
            program_return(crate::kernel::program_expression::int32_literal(0)),
        );
        let outcome = FunctionOutcome::Return {
            value: int32(0).into(),
            state: Box::new(state.clone()),
        };
        let specification =
            program_function_specification(state.clone(), vec![], vec![], outcome.clone());
        let path = SymbolicExecutionPath {
            call_parameters: None,
            descent_step: None,
            completion_origin: Some(outcome.clone()),
            call_result: None,
            assumptions: PureFactContext::new(),
            post_assumptions: None,
            facts: ExecutionFacts::new(),
            effect_facts: ExecutionFacts::new(),
            obligations: vec![],
            theorem: Theorem::new(Proposition::ProgramFunctionVerifies {
                state: Box::new(state),
                function: Box::new(function.clone()),
                arguments: vec![],
                outcome,
            }),
            loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
        };
        let theorem = Theorem::new(
            Proposition::ProgramFunctionPartiallySatisfiesSpecification {
                function: Box::new(function.clone()),
                specification: Box::new(specification.clone()),
            },
        );
        let proof: ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()> =
            ProofObject::root(
                (),
                ProofBranch::new(
                    ProofObligation::Proposition(PropositionObligation::at_outcome(
                        proposition.clone(),
                        (),
                        Arc::new(OutcomeProofState::new(
                            OutcomeProofCore {
                                publication: None,
                                identity: OutcomeIdentity::fresh(),
                                result: int32(0).into(),
                                state: ExecutionState::new().with_memory(memory).into(),
                                store_consequences_available: false,
                                is_exceptional: false,
                                effect_facts: ExecutionFacts::new().into(),
                            },
                            (),
                        )),
                    )),
                    ProofBranchState {
                        facts: PureFactStore::from_ordered(&[proposition]),
                        execution: None,
                    },
                ),
            );
        let closed = proof
            .apply_known(PropositionKnownContext::Exact)
            .unwrap_or_else(|_| panic!("the stated proposition must close"));
        let completion = closed.completed_proposition().unwrap();
        let checked = program_checked_function_proposition_with_reason(
            &function,
            &specification,
            &theorem,
            &completion,
            &path,
        )?;
        assert!(
            checked.path_origin.is_none(),
            "generic specifications retain premise checks"
        );
        let strengthened = FunctionSpecification::new(
            specification.state().clone(),
            specification.arguments().to_vec(),
            vec![Proposition::condition_is(
                ConditionTerm::Constant(false),
                true,
            )],
            specification.outcome().clone(),
        );
        let conditional = prove_program_function_satisfies_specification_from_symbolic_path(
            function.clone(),
            strengthened.clone(),
            &path,
        )
        .unwrap();
        let conditional_completion = program_checked_function_proposition_with_reason(
            &function,
            &strengthened,
            &conditional,
            &completion,
            &path,
        )?;
        assert!(
            conditional_completion.path_origin.is_none(),
            "extra specification premises must never acquire direct path authority"
        );
        let owned = CheckedPathSpecification::new(&function, &path).unwrap();
        assert!(owned.complete(&completion, &path)?.path_origin.is_some());
        let mut reconstructed = path.clone();
        reconstructed.theorem = Theorem::new(path.theorem.proposition().clone());
        assert_eq!(reconstructed.theorem, path.theorem);
        assert!(
            owned.complete(&completion, &reconstructed).is_err(),
            "equal propositions from independent producers are not the same path receipt"
        );
        Ok(checked)
    }

    #[test]
    fn proposition_completion_accepts_own_read_cache_but_not_program_changes() {
        let before = SymbolicMemory::new();
        let cached = cache(&before, &before, 8, 4);
        assert_ne!(before, cached);
        assert!(check_completion(cached.clone(), before.clone()).is_ok());
        assert!(check_completion(before.clone(), cached).is_ok());
        let written = before.clone().store(pointer("cache", 0), int32(7));
        assert!(check_completion(written.clone(), before.clone()).is_err());
        assert!(check_completion(cache(&before, &written, 8, 4), before.clone()).is_err());
        assert!(check_completion(cache(&before, &before, 8, 8), before.clone()).is_err());
        assert!(check_completion(before.clone().with_block("extra", 4), before).is_err());
    }

    #[test]
    fn proposition_completion_does_not_cross_call_havoc_for_cached_reads() {
        let before = SymbolicMemory::new();
        let after = before.clone().with_call_memory_havoc(
            Variable(91_001),
            &[],
            &PureFactContext::new(),
            None,
        );
        assert!(check_completion(cache(&after, &before, 8, 4), after.clone()).is_err());
        assert!(check_completion(cache(&after, &after, 8, 4), before).is_err());
        assert!(check_completion(cache(&after, &after, 8, 4), after).is_ok());
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../../scaling_tests/kernel/api/contract_certification/contract_claims/cached_read_completion_tests.rs"
        );
    }
}

pub fn program_function_outcomes_definitionally_equal(
    function: &ProgramFunction,
    left: &FunctionOutcome,
    right: &FunctionOutcome,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (
            FunctionOutcome::Return {
                value: _,
                state: left_state,
            },
            FunctionOutcome::Return {
                value: _,
                state: right_state,
            },
        ) => {
            if !program_function_outcomes_program_state_definitionally_equal(
                left,
                right,
                assumptions,
            ) {
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
pub fn program_function_outcomes_program_state_definitionally_equal(
    left: &FunctionOutcome,
    right: &FunctionOutcome,
    assumptions: &PureFactContext,
) -> bool {
    match (left, right) {
        (
            FunctionOutcome::Return {
                value: left_value,
                state: left_state,
            },
            FunctionOutcome::Return {
                value: right_value,
                state: right_state,
            },
        ) => {
            program_values_proven_equal_for_memory_resolution(
                &left_value.native(),
                &right_value.native(),
                assumptions,
            ) && memories_definitionally_equal(
                left_state.memory(),
                right_state.memory(),
                assumptions,
            )
        }
        _ => left == right,
    }
}

/// Compares the observable program state of two return paths by matching their
/// certified execution histories. Resource representation remains the
/// responsibility of the separate resource certificate.
#[cfg(test)]
pub fn program_function_outcomes_program_state_equal_by_derivation(
    left: &FunctionOutcome,
    left_facts: &(impl ExecutionFactSource + ?Sized),
    right: &FunctionOutcome,
    right_facts: &(impl ExecutionFactSource + ?Sized),
    assumptions: &PureFactContext,
) -> bool {
    let (
        FunctionOutcome::Return {
            value: left_value,
            state: left_state,
        },
        FunctionOutcome::Return {
            value: right_value,
            state: right_state,
        },
    ) = (left, right)
    else {
        return false;
    };
    memories_equal_by_derivation(
        left_state.memory(),
        left_facts,
        right_state.memory(),
        right_facts,
        assumptions,
    ) && program_values_proven_equal_for_memory_resolution(
        &left_value.native(),
        &right_value.native(),
        assumptions,
    )
}

#[cfg(test)]
fn memories_equal_by_derivation(
    left_final: &SymbolicMemory,
    left_facts: &(impl ExecutionFactSource + ?Sized),
    right_final: &SymbolicMemory,
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
    let chain_reaches_final = |stores: &[&CertifiedMemoryStore], final_memory: &SymbolicMemory| {
        stores
            .windows(2)
            .all(|pair| memories_definitionally_equal(&pair[0].after, &pair[1].before, assumptions))
            && memories_definitionally_equal(
                &stores.last().expect("store chain is nonempty").after,
                final_memory,
                assumptions,
            )
    };
    memories_definitionally_equal(&left_stores[0].before, &right_stores[0].before, assumptions)
        && chain_reaches_final(&left_stores, left_final)
        && chain_reaches_final(&right_stores, right_final)
        && left_stores.iter().zip(&right_stores).all(|(left, right)| {
            (pointers_proven_equal_for_memory_resolution(
                &left.pointer,
                &right.pointer,
                assumptions,
            ) || (left.pointer.base == right.pointer.base
                && program_pointer_offsets_proven_equal_for_effect(
                    &left.pointer.offset,
                    &right.pointer.offset,
                    assumptions,
                )))
                && program_values_proven_equal_for_memory_resolution(
                    left.value.native(),
                    right.value.native(),
                    assumptions,
                )
        })
}

/// Two memories are equal when their derivation chains match edge by
/// edge down to a definitionally equal pair. Each step descends one side's
/// `base`, whose id is strictly smaller, so the recursion is finite with
/// no depth cut.
#[cfg(test)]
fn memories_equal_by_matching_derivations(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    assumptions: &PureFactContext,
) -> bool {
    matching_recomputed_call_havoc_views(left, right, assumptions).is_some()
}

/// Matches two recomputed memory histories and returns the exact pairs of call
/// result states encountered on the successful path. Execution-proof
/// construction uses these pairs to register another concrete view of an
/// already checked call event; the pairs themselves are never authority.
pub(crate) fn matching_recomputed_call_havoc_views(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    assumptions: &PureFactContext,
) -> Option<Vec<(SharedMemory, SharedMemory)>> {
    fn transparent_base(derivation: &MemoryDerivation) -> Option<&SharedMemory> {
        match derivation {
            MemoryDerivation::Store {
                base,
                pointer,
                value,
                ..
            } if pointer.base.is_local_block()
                || store_is_self_materialization(base, pointer, value.native()) =>
            {
                Some(base)
            }
            MemoryDerivation::BlockDeclared { base, block } if block.is_local_block() => Some(base),
            MemoryDerivation::ContractAllocationClaimsChanged { base } => Some(base),
            MemoryDerivation::CellsForgotten { base } => Some(base),
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
        base: &SharedMemory,
        pointer: &Address,
        value: &ProgramValue,
    ) -> bool {
        let (ProgramValue::Int8(MachineTerm::MemoryLoad(load_memory, load_pointer, kind))
        | ProgramValue::Int16(MachineTerm::MemoryLoad(load_memory, load_pointer, kind))
        | ProgramValue::Int32(MachineTerm::MemoryLoad(load_memory, load_pointer, kind))
        | ProgramValue::UInt8(MachineTerm::MemoryLoad(load_memory, load_pointer, kind))
        | ProgramValue::UInt16(MachineTerm::MemoryLoad(load_memory, load_pointer, kind))
        | ProgramValue::UInt32(MachineTerm::MemoryLoad(load_memory, load_pointer, kind))
        | ProgramValue::Int64(MachineTerm::MemoryLoad(load_memory, load_pointer, kind))
        | ProgramValue::UInt64(MachineTerm::MemoryLoad(load_memory, load_pointer, kind))) = value
        else {
            return false;
        };
        // Storing a read back is a no-op only when it is the cell's own read:
        // a narrower or differently signed read changes the cell.
        load_pointer.as_ref() == pointer
            && kind.reads_value(value)
            && intern_memory_ref(load_memory.memory()).arena_id() == base.arena_id()
    }
    fn match_inner(
        left: &SymbolicMemory,
        right: &SymbolicMemory,
        assumptions: &PureFactContext,
        views: &mut Vec<(SharedMemory, SharedMemory)>,
    ) -> bool {
        if memories_definitionally_equal(left, right, assumptions) {
            return true;
        }
        let left = intern_memory_ref(left);
        let right = intern_memory_ref(right);
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
                Some(MemoryDerivation::CallHavoc {
                    base: left_base,
                    mutable_ranges: left_ranges,
                    ..
                }),
                Some(MemoryDerivation::CallHavoc {
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
                Some(MemoryDerivation::LoopHavoc {
                    base: left_base,
                    mutable_ranges: left_ranges,
                    ..
                }),
                Some(MemoryDerivation::LoopHavoc {
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
                Some(MemoryDerivation::Store {
                    base: left_base,
                    pointer: left_pointer,
                    value: left_value,
                    ..
                }),
                Some(MemoryDerivation::Store {
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
                ) && program_values_proven_equal_for_memory_resolution(
                    left_value.native(),
                    right_value.native(),
                    assumptions,
                ) && match_inner(left_base, right_base, assumptions, views)
            }
            // Two seeded runs are two sequences of stores, matched store for
            // store as above.
            (
                Some(
                    left_seeded @ MemoryDerivation::CellsSeeded {
                        base: left_base, ..
                    },
                ),
                Some(
                    right_seeded @ MemoryDerivation::CellsSeeded {
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
                            ) && program_values_proven_equal_for_memory_resolution(
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
    left: &[MemoryRange],
    right: &[MemoryRange],
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

    fn var(id: u64) -> MachineTerm {
        MachineTerm::Variable(Variable(id))
    }

    #[test]
    fn certified_range_list_endpoints_use_graph_with_state_scope() {
        let _session = crate::kernel::VerificationSession::enter();
        let before =
            crate::kernel::intern_memory(SymbolicMemory::new().with_block("range-list", 8));
        let pointer = |index| Address {
            base: "range-list".into(),
            offset: AddressOffset::scale_int32(index, 4),
        };
        let load = |memory: &SharedMemory, index| {
            MachineTerm::Variable(crate::kernel::load_variable_for_cell_with_origin(
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
            ProgramValue::Int32(MachineTerm::constant(9)),
        ));
        let base = Address::symbolic(Variable(9100));
        let sum = |value| MachineTerm::add(value, MachineTerm::constant(1));
        let range = |start| MemoryRange::new(base.clone(), start, MachineTerm::constant(16));
        let left = range(sum(load(&before, a.clone())));
        let right = range(sum(load(&before, b.clone())));
        let later = range(sum(load(&after, b.clone())));
        let premise = ConditionTerm::equal(a, b);
        let parent = PureFactContext::new();
        let branch = parent.clone().assume_condition(premise.clone(), true);
        let matches = |context: &PureFactContext, right: &MemoryRange| {
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
        assert!(!matches(
            &branch,
            &MemoryRange::new_with_element_width(
                base,
                right.start().clone(),
                right.end().clone(),
                1,
            ),
        ));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../../scaling_tests/kernel/api/contract_certification/contract_claims/range_list_equality_graph_tests.rs"
        );
    }
}

/// Whether two memory states have the same heap status and are the same
/// program state, up to definitional equality of the terms in their cells.
///
/// The `local:` blocks this skips are the ones
/// [`local_block_no_pointer_can_reach`] allows a pointerless comparison to
/// skip, and that function carries the argument. This is the certification
/// side of one rule, so it must select cells and blocks with exactly that
/// filter and nothing wider.
pub(in crate::kernel) fn memories_definitionally_equal(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
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
    source: &SymbolicMemory,
    target: &SymbolicMemory,
    assumptions: &PureFactContext,
) -> bool {
    for (source_pointer, source_value) in source
        .cells
        .iter()
        .filter(|(pointer, _)| !local_block_no_pointer_can_reach(&pointer.base))
    {
        // A cell the target holds under the same spelling is the match. One
        // it does not hold is most often a read of the target that only the
        // source has cached, which is the target's own value there whatever
        // else the target caches. Only then is the cell looked for under
        // another spelling, which asks an equality of every target cell.
        let equal = if let Some(target_value) = target.cells.get(source_pointer) {
            program_values_proven_equal_for_memory_resolution(
                source_value,
                &target_value,
                assumptions,
            )
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
                    program_values_proven_equal_for_memory_resolution(
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
        .filter(|((pointer, _), _)| !local_block_no_pointer_can_reach(&pointer.base))
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
            program_values_proven_equal_for_memory_resolution(
                source_value.native(),
                target_value.native(),
                assumptions,
            )
        } else {
            materialized_load_is_unchanged(
                source_value.native(),
                target,
                source_pointer,
                assumptions,
            )
        };
        if !equal {
            return false;
        }
    }
    true
}

fn materialized_load_is_unchanged(
    value: &ProgramValue,
    symbolic_memory: &SymbolicMemory,
    pointer: &Address,
    assumptions: &PureFactContext,
) -> bool {
    // Materialized cells retain their structural read. Legacy scalar names
    // remain input adapters for older producer families.
    let load_of = |bits: &MachineTerm| match bits {
        MachineTerm::MemoryLoad(_, _, _) => Some(bits.clone()),
        MachineTerm::Variable(variable) if crate::kernel::eval::is_load_variable(variable) => {
            crate::kernel::eval::registered_load_term_for_variable(variable)
        }
        _ => None,
    };
    let load = match value {
        crate::kernel::integer64_c_value!(bits) => load_of(bits),
        // Object and function pointers share the exact structural descriptor;
        // the remaining branches adapt legacy registered names and offsets.
        ProgramValue::Pointer(pointer_value)
            if pointer_value.address().as_loaded_value().is_some() =>
        {
            crate::kernel::equality_graph::logical_pointer_read_term(pointer_value.address())
        }
        ProgramValue::Pointer(pointer_value) => match pointer_value.address() {
            Address {
                base: AddressBase::FunctionSymbolic(variable),
                offset: AddressOffset::Constant(0),
            } if matches!(
                pointer_value.program_type(),
                ProgramType::FunctionPointer(_)
            ) =>
            {
                load_of(&MachineTerm::Variable(*variable))
            }
            Address {
                offset: AddressOffset::Int32Scaled { value: bits, .. },
                ..
            } => bits
                .operand_view()
                .read_source()
                .and_then(|leaf| load_of(&leaf)),
            _ => return false,
        },
        _ => return false,
    };
    // The cell is the read only when it is a read of the cell's own kind: a
    // narrower or differently signed load stored in it holds another value
    // than a read of the cell returns.
    let Some(left) = load else {
        return false;
    };
    let MachineTerm::MemoryLoad(_, load_pointer, kind) = &left else {
        return false;
    };
    let kind = *kind;
    if !kind.reads_value(value) {
        return false;
    }
    let right = MachineTerm::MemoryLoad(
        ProgramPoint::at(&(crate::kernel::intern_memory(symbolic_memory.clone()))),
        Box::new(pointer.clone()),
        kind,
    );
    pointers_proven_equal_for_memory_resolution(load_pointer, pointer, assumptions)
        && crate::kernel::checked_atomic_load_equality(&left, &right, assumptions)
}

struct CertifiedFunctionClaimPath {
    completion_path_origin: Option<Theorem>,
    caller_state: ExecutionState,
    arguments: Vec<ProgramExpression>,
    outcome: FunctionOutcome,
    exit_state: Option<ExecutionState>,
    entry_state: ExecutionState,
    required_resources: ResourceContext,
    checked_required_resources: Arc<[crate::kernel::functions::CheckedResourceFact]>,
    entry_resources: ResourceContext,
    post_state: Option<ExecutionState>,
    post_resources: Option<ResourceContext>,
    assumptions: PureFactContext,
    effect_facts: ExecutionFacts,
    checked_resource_claims: Vec<FunctionContractClaimKey>,
    checked_resource_transition: bool,
    effect_projection: Option<Arc<Result<FunctionMemoryEffectProjection, String>>>,
}

/// A failed contract path's reason. Tests also retain a bounded fact sample
/// to inspect the context at the exact failed check.
#[derive(Clone, Debug)]
pub(crate) struct ContractPathPreparationFailure {
    pub reason: String,
    #[cfg(test)]
    pub available: Vec<Proposition>,
    #[cfg(test)]
    pub available_count: usize,
}

impl From<String> for ContractPathPreparationFailure {
    fn from(reason: String) -> Self {
        Self {
            reason,
            #[cfg(test)]
            available: Vec::new(),
            #[cfg(test)]
            available_count: 0,
        }
    }
}

fn unproved_contract_path_condition(
    reason: String,
    _assumptions: &PureFactContext,
) -> ContractPathPreparationFailure {
    // Sample both ends of the fact index without retaining the whole context.
    // Its order is index order, not execution order. These are the facts
    // consulted by certification, including resource population facts,
    // rather than a second execution or a speculative proof search.
    #[cfg(test)]
    let (available, available_count) = _assumptions.diagnostic_fact_sample(8, 24);
    ContractPathPreparationFailure {
        reason,
        #[cfg(test)]
        available,
        #[cfg(test)]
        available_count,
    }
}

fn prepare_function_claim_path(
    function: &ProgramFunction,
    path: &SymbolicExecutionPath,
    checked_resource_claims: Vec<FunctionContractClaimKey>,
    checked_resource_transition: bool,
    deferred_contract_exit: bool,
    deferred_contract_exit_error: Option<RuntimeError>,
    capture_failure: bool,
    checked_transfer: Option<&crate::kernel::functions::CheckedBoundaryResourceTransfer>,
    checked_outcome: Option<&FunctionOutcome>,
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
    let Some(entry_state) = program_function_entry_state(caller_state, function, arguments) else {
        return Err("the function entry state cannot be reconstructed"
            .to_string()
            .into());
    };
    let mut entry_state = contract_view_of_entry(entry_state, function, arguments);
    let mut budget = ExecutionBudget::beside_live_state();
    let (required_resources, checked_required_resources) =
        match evaluate_function_resource_context_with_metadata(
            &entry_state,
            function.resource_requires(),
            function.composite_resource_definitions(),
            &assumptions.clone().assume_entry_clause_spans(),
            &mut budget,
        ) {
            Ok(Ok(resources)) => resources,
            Ok(Err(error)) => {
                return Err(
                    format!("the required resource context cannot be evaluated: {error}").into(),
                );
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
    for fact in &population_facts {
        assumptions = assumptions.assume_proposition(fact.clone());
    }
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
    let resource_facts = entry_resources.observable_facts_assuming_valid(&assumptions);
    entry_state = entry_state.with_resource_context(entry_resources.clone());
    let facts = definition_facts
        .into_iter()
        .chain(population_facts)
        .chain(resource_facts)
        .collect::<Vec<_>>();
    let entry = RetainedClosingEntry {
        caller: caller_state.clone(),
        arguments: arguments.to_vec(),
        state: entry_state,
        required: required_resources,
        checked: checked_required_resources.into(),
        assumptions,
        facts: facts.into(),
        projection: None,
        exit: Default::default(),
    };
    prepare_closing_path(
        function,
        path,
        &entry,
        checked_outcome.unwrap_or(outcome),
        checked_resource_claims,
        checked_resource_transition,
        deferred_contract_exit,
        deferred_contract_exit_error,
        capture_failure,
        checked_transfer,
    )
}

/// Complete the selected outcome against its retained entry input. Resource
/// and effect checks remain ordinary goals; no entry clause is evaluated here.
fn prepare_closing_path(
    function: &ProgramFunction,
    path: &SymbolicExecutionPath,
    entry: &RetainedClosingEntry,
    outcome: &FunctionOutcome,
    checked_resource_claims: Vec<FunctionContractClaimKey>,
    checked_resource_transition: bool,
    deferred_contract_exit: bool,
    deferred_contract_exit_error: Option<RuntimeError>,
    capture_failure: bool,
    checked_transfer: Option<&crate::kernel::functions::CheckedBoundaryResourceTransfer>,
) -> Result<CertifiedFunctionClaimPath, ContractPathPreparationFailure> {
    let caller_state = &entry.caller;
    let arguments = entry.arguments.as_slice();
    let entry_state = entry.state.clone();
    let required_resources = entry.required.clone();
    let checked_required_resources = entry.checked.clone();
    let entry_resources = entry.state.resources().clone();
    let assumptions = entry.assumptions.clone();
    let mut budget = ExecutionBudget::beside_live_state();
    let adopted_outcome = crate::kernel::functions::exit_with_unheld_produced_binders_adopted(
        function,
        outcome.clone(),
        &assumptions,
    );
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
            // The boundary consumes its selected output units jointly from
            // this retained body partition. Individual claim receipts do
            // not mint another owner or replace the body's occurrences.
            outcome,
            checked_transfer,
            &assumptions,
            &mut budget,
        ) {
            Ok(Ok(outcome)) => Some(outcome),
            Ok(Err(error)) => {
                return Err(format!(
                    "the deferred conditional contract exit cannot be resolved: {error}"
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
    #[cfg(test)]
    let context_entries_before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
    // A verification condition may be local to one symbolic path. Branch
    // guards and independently certified callee postconditions are evidence
    // on that path, just as assumable definedness obligations are; omitting
    // them here incorrectly rejects safe guarded calls after certification.
    // Non-assumable obligations are deliberately excluded by
    // `assumptions_with_path_context`, so this cannot prove a verification
    // condition by assuming the condition itself.
    let assumptions = if let Some(post_assumptions) = &path.post_assumptions {
        // Entry resources were evaluated above under entry premises only.
        // The completion producer retained this persistent body context,
        // built as the path advanced; extend it by what the entry resources
        // state and the assumable obligations, never the conditions whose
        // truth certification still needs to establish. Rebuilding it from
        // the path's facts would cost each path its whole history.
        let post_assumptions = assumptions_with_propositions(post_assumptions, &entry.facts);
        assumptions_with_path_context(&post_assumptions, &[], path.obligations())
    } else {
        // Keep the established resource-fact/path-fact precedence for legacy
        // producers and paths with observable entry-resource propositions.
        let execution_facts = path.execution_facts();
        let assumptions = assumptions_with_propositions(&assumptions, &entry.facts);
        assumptions_with_path_context(&assumptions, &execution_facts, path.obligations())
    };
    #[cfg(test)]
    crate::kernel::reasoning::path_facts::record_contract_path_context_entries(
        crate::kernel::reasoning::path_facts::context_rebuild_entries() - context_entries_before,
    );
    let effect_facts = path.effect_facts.clone();
    if matches!(outcome, FunctionOutcome::VerificationDiverges) {
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
                unproved_contract_path_condition(reason, &assumptions)
            } else {
                reason.into()
            });
        }
        return Ok(CertifiedFunctionClaimPath {
            completion_path_origin: None,
            caller_state: caller_state.clone(),
            arguments: arguments.to_vec(),
            outcome: outcome.clone(),
            exit_state: None,
            entry_state,
            required_resources,
            checked_required_resources,
            entry_resources,
            post_state: None,
            post_resources: None,
            assumptions,
            effect_facts,
            checked_resource_claims,
            checked_resource_transition,
            effect_projection: entry.projection.clone(),
        });
    }
    let (value, raw_exit_state, exceptional) = match &adopted_outcome {
        FunctionOutcome::Return { value, state } => (value, state, false),
        FunctionOutcome::Throw { value, state }
            if function.exceptional_signature().permits(&value.native()) =>
        {
            (value, state, true)
        }
        FunctionOutcome::UndefinedBehavior(undefined_behavior) => {
            return Err(format!(
                "the certified path is not safe: undefined behavior: {}",
                undefined_behavior.description()
            )
            .into());
        }
        FunctionOutcome::RuntimeError(error) => {
            return Err(format!(
                "the certified path is not safe: {}",
                super::describe_certification_runtime_error(error)
            )
            .into());
        }
        FunctionOutcome::Throw { .. } => {
            return Err(
                "the certified path is not safe: it throws an exception the function's signature does not permit"
                    .to_string()
                    .into(),
            );
        }
        FunctionOutcome::VerificationDiverges => {
            return Err("the certified path is not safe: it does not return"
                .to_string()
                .into());
        }
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
                Ok(Err(error)) => return Err(format!("{error}").into()),
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
            Ok(Err(error)) => return Err(format!("{error}").into()),
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
        .map_err(|error| error.to_string())?
    };
    let mut claim_exit_state = (**raw_exit_state).clone().with_memory(exit_memory.clone());
    let post_resources = entry
        .prepare_exit_projection(
            function,
            raw_exit_state,
            &mut claim_exit_state,
            &assumptions,
        )
        .ok_or_else(|| "the exit resource context cannot be expanded".to_string())?;
    let post_resources = with_unmatched_instance_body_views(
        post_resources,
        claim_exit_state.resources().facts(),
        function,
        &claim_exit_state,
        &assumptions,
    );
    let post_resource_facts = post_resources.observable_facts_assuming_valid(&assumptions);
    let mut assumptions = assumptions_with_propositions(&assumptions, &post_resource_facts);
    // The exit memory came from the exit state, so the post state stands
    // after the exit state's point, with the entry's locals.
    let mut post_state = entry_state
        .clone()
        .with_memory_continuing(raw_exit_state, exit_memory);
    post_state = post_state.with_resource_context(post_resources.clone());
    post_state.observed_population_families = raw_exit_state.observed_population_families.clone();
    // Population counts live in the creation ledger, and observed families
    // beside it. Both must describe the checked exit, not the reconstructed
    // entry used to bind locals.
    post_state.population_effects = raw_exit_state.population_effects.clone();
    if exceptional {
        bind_contract_exit_value(
            &mut post_state,
            CONTRACT_EXCEPTION,
            value,
            value.native().program_type(),
        );
    } else if function.return_type() != ProgramType::Void {
        bind_contract_exit_value(
            &mut post_state,
            CONTRACT_RESULT,
            value,
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
            unproved_contract_path_condition(reason, &assumptions)
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
        completion_path_origin: None,
        caller_state: caller_state.clone(),
        arguments: arguments.to_vec(),
        outcome: outcome.clone(),
        exit_state: Some(claim_exit_state),
        entry_state,
        required_resources,
        checked_required_resources,
        entry_resources,
        post_state: Some(post_state),
        post_resources: Some(post_resources),
        assumptions,
        effect_facts,
        checked_resource_claims,
        checked_resource_transition,
        effect_projection: entry.projection.clone(),
    })
}

/// `resources` with the read views the unmatched bodies of the field-bearing
/// instances among `instances` publish at `state`. The instances are the
/// contract's own entry clauses or the function's own exit frame, which the
/// composite expansion beside this call already visits.
fn with_unmatched_instance_body_views(
    resources: crate::kernel::ResourceContext,
    instances: &[ResourceFact],
    function: &ProgramFunction,
    state: &ExecutionState,
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

// An unconditional condition also discharges any implication guarding it.
// Ask only the existing indexed leaf rules; do not search the antecedents
// or add them to the execution context.
fn obligation_has_known_condition_consequent(
    assumptions: &PureFactContext,
    mut obligation: &Proposition,
) -> bool {
    while let Proposition::Implies(_, consequent) = obligation {
        crate::instrumentation::record_deterministic_work(1);
        obligation = consequent;
    }
    match obligation {
        Proposition::ConditionIs(condition, value) => {
            assumptions.difference_decision(condition.native_compat(), &[]) == Some(*value)
        }
        _ => false,
    }
}

fn function_claim_holds_on_prepared_path(
    function: &ProgramFunction,
    claim: &FunctionContractClaim,
    path: &CertifiedFunctionClaimPath,
    checked_propositions: &CheckedPropositionIndex<'_>,
    completion_origin_state: Option<&ExecutionState>,
    checking_assumptions: Option<&PureFactContext>,
) -> bool {
    let CertifiedFunctionClaimPath {
        completion_path_origin,
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
        effect_projection,
    } = path;
    let assumptions = checking_assumptions.unwrap_or(assumptions);
    let mut budget = ExecutionBudget::beside_live_state();
    match claim.target() {
        FunctionContractClaimTarget::BodySafety => true,
        FunctionContractClaimTarget::EnsureProposition(_index)
        | FunctionContractClaimTarget::ExceptionalEnsureProposition(_index) => {
            let (Some(post_state), Some(post_resources)) = (post_state, post_resources) else {
                return true;
            };
            let ensure = match (claim.target(), outcome) {
                (
                    FunctionContractClaimTarget::EnsureProposition(index),
                    FunctionOutcome::Return { .. },
                ) => function.contract_ensures().get(*index),
                (
                    FunctionContractClaimTarget::ExceptionalEnsureProposition(index),
                    FunctionOutcome::Throw { .. },
                ) => function.exceptional_ensures().get(*index),
                (FunctionContractClaimTarget::EnsureProposition(_), _)
                | (FunctionContractClaimTarget::ExceptionalEnsureProposition(_), _) => {
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
                    || obligation_has_known_condition_consequent(assumptions, obligation)
                    || crate::kernel::api::checked_int32_reassociated_add_domain(
                        assumptions,
                        obligation,
                    )
            };
            let certifies = |proof: &&CheckedFunctionProposition| {
                // Cheapest checks first: a completion from another
                // path or function is rejected before any proving.
                // A completion made at the state the artifact's
                // proof ran at certifies a path rebased from it.
                let completion_state = proof.specification.state();
                if proof.function != *function
                    || (!completion_state.equal_up_to_unused_creation_ledgers(caller_state)
                        && Some(completion_state) != completion_origin_state)
                    || proof.specification.arguments() != arguments
                    || !program_function_outcomes_definitionally_equal(
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
                        || (matches!(requirement, Proposition::MemoryLoadable { .. })
                            && load_obligation_holds(requirement))
                        || match requirement {
                            Proposition::ResourceComposition(required) => {
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
                // The path-set constructor authorized the artifact's entry
                // premises and retained this exact producer association, even
                // across entry rebasing. Index by identity so neither premises
                // nor other paths need scanning for each claim.
                if completion_path_origin.as_ref().is_some_and(|origin| {
                    checked_propositions
                        .by_path
                        .get(claim.target())
                        .is_some_and(|paths| {
                            paths.contains(&(std::sync::Arc::as_ptr(&origin.proposition) as usize))
                        })
                }) {
                    return true;
                }
                if let Some(key) = literal_completion_key(outcome)
                    && checked_propositions
                        .by_literal_outcome
                        .get(claim.target())
                        .and_then(|outcomes| outcomes.get(&key))
                        .is_some_and(|proofs| proofs.iter().any(certifies))
                {
                    return true;
                }
                // Different syntax can denote the same outcome. The index is
                // only a candidate accelerator, never evidence of inequality.
                checked_propositions
                    .by_claim
                    .get(claim.target())
                    .is_some_and(|proofs| proofs.iter().any(certifies))
            };
            // A completed kernel claim includes the evaluation requirements
            // discharged when its proof goal was opened. Consume that checked
            // judgment; do not lower and prove its requirements a second time
            // in a reconstructed C execution context.
            if claim_completion_certifies() {
                return true;
            }
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
                    }) && assumptions.proves_exact(&predicate)
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
            // Legacy execution-only callers have no completed claim proof.
            // Their lowered claim must evaluate to truth and its requirements
            // must hold directly; checked proof completions returned above.
            obligations_hold && lowered_goal_is_constant_true(&path.proposition)
        }
        FunctionContractClaimTarget::EnsureResource(index) => {
            if !matches!(outcome, FunctionOutcome::Return { .. })
                && !matches!(outcome, FunctionOutcome::Throw { .. }
                    if function.resource_ensures().get(*index).is_some_and(|resource|
                        resource.role() == ResourceTransferRole::Borrow))
            {
                return true;
            }
            // The proof already checked this exact resource claim, including
            // its returned context and allocation-lifetime obligation. Reuse
            // that kernel-owned evidence rather than rebuilding the resource
            // transition and its population invariant.
            if *checked_resource_transition
                && checked_resource_claims
                    .iter()
                    .any(|key| key == &FunctionContractClaimKey::Ensure(*index))
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
                    &exit_state.program_point(),
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
        FunctionContractClaimTarget::Effect => {
            let independent_projection;
            let projection = if let Some(retained) = effect_projection {
                let Ok(projection) = retained.as_ref() else {
                    return false;
                };
                projection
            } else {
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
                independent_projection = projection;
                &independent_projection
            };
            let mutable_ranges = projection.ranges().to_vec();
            // A footprint that reaches unnamed memory covers every write.
            let covers_everything = mutable_ranges
                .iter()
                .any(crate::kernel::MemoryRange::is_unnamed_footprint);
            let mut effect_memory = caller_state.memory().clone();
            let mut seen_transitions = Vec::<(SymbolicMemory, SymbolicMemory)>::new();
            let is_function_fresh_heap_pointer = |pointer: &Address, current: &SymbolicMemory| {
                let matches_allocation = |memory: &SymbolicMemory| {
                    memory.heap.live_allocations.keys().any(|base| {
                        // Freshness is a property of the allocation, not of
                        // the particular address selected within it. An
                        // interior pointer into a block live at entry must
                        // still be covered by the function's mutable frame.
                        base.base == pointer.base
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
                    && (matches!(pointer.base, AddressBase::Heap(_)) || matches_allocation(current))
            };
            let effects_are_bounded = effect_facts.iter().all(|fact| match fact.proposition() {
                Proposition::MemoryMutatesOnly {
                    before,
                    after,
                    writes,
                } => {
                    let repeats_transition =
                        seen_transitions.iter().any(|(seen_before, seen_after)| {
                            program_effect_memories_definitionally_equal(
                                seen_before,
                                before,
                                assumptions,
                            ) && program_effect_memories_definitionally_equal(
                                seen_after,
                                after,
                                assumptions,
                            )
                        });
                    if !repeats_transition
                        && !program_effect_memories_definitionally_equal(
                            &effect_memory,
                            before,
                            assumptions,
                        )
                        && !program_effect_memory_advances_over_internal_heap_state(
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
                        .filter(|(pointer, _)| !pointer.base.is_local_block())
                        .all(|(pointer, bytes)| {
                            covers_everything
                                || is_function_fresh_heap_pointer(pointer, before)
                                || mutable_ranges.iter().any(|range| {
                                    assumptions
                                        .pointer_access_in_memory_range(pointer, *bytes, range)
                                })
                        })
                }
                Proposition::MemoryEffectSummary {
                    before,
                    after,
                    mutable_ranges: nested_ranges,
                } => {
                    let repeats_transition =
                        seen_transitions.iter().any(|(seen_before, seen_after)| {
                            program_effect_memories_definitionally_equal(
                                seen_before,
                                before,
                                assumptions,
                            ) && program_effect_memories_definitionally_equal(
                                seen_after,
                                after,
                                assumptions,
                            )
                        });
                    if !repeats_transition
                        && !program_effect_memories_definitionally_equal(
                            &effect_memory,
                            before,
                            assumptions,
                        )
                        && !program_effect_memory_advances_over_internal_heap_state(
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
                Proposition::HeapAllocationFreed {
                    before,
                    after,
                    allocation_base,
                    bytes,
                } => {
                    let repeats_transition =
                        seen_transitions.iter().any(|(seen_before, seen_after)| {
                            program_effect_memories_definitionally_equal(
                                seen_before,
                                before,
                                assumptions,
                            ) && program_effect_memories_definitionally_equal(
                                seen_after,
                                after,
                                assumptions,
                            )
                        });
                    if !repeats_transition
                        && !program_effect_memories_definitionally_equal(
                            &effect_memory,
                            before,
                            assumptions,
                        )
                        && !program_effect_memory_advances_over_internal_heap_state(
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
                program_effect_memories_definitionally_equal(
                    &effect_memory,
                    exit_state.memory(),
                    assumptions,
                ) || program_effect_memory_advances_over_internal_heap_state(
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

pub(in crate::kernel) fn program_effect_memories_definitionally_equal(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    assumptions: &PureFactContext,
) -> bool {
    let without_locals = |memory: &SymbolicMemory| {
        let mut external = memory.clone();
        std::sync::Arc::make_mut(&mut external.blocks).retain(|block, _| !block.is_local_block());
        std::sync::Arc::make_mut(&mut external.cells)
            .retain(|pointer, _| !pointer.base.is_local_block());
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
    memories_definitionally_equal(&left, &right, assumptions)
}

/// Accepts internal heap bookkeeping between externally visible effects:
/// newly allocated trusted blocks and the registration of an already-owned
/// symbolic allocation before direct `free`. Removing only those additions
/// leaves a memory that must still match the preceding endpoint exactly.
pub(in crate::kernel) fn program_effect_memory_advances_over_internal_heap_state(
    before: &SymbolicMemory,
    after: &SymbolicMemory,
    function_entry: &SymbolicMemory,
    assumptions: &PureFactContext,
) -> bool {
    let fresh_blocks = after
        .blocks
        .keys()
        .filter(|block| {
            matches!(block, AddressBase::Heap(_))
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
        .retain(|pointer, _| !fresh_blocks.contains(&pointer.base));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .live_allocations
        .retain(|pointer, _| {
            !fresh_blocks.contains(&pointer.base) && !added_allocation_claims.contains(pointer)
        });
    std::sync::Arc::make_mut(&mut stripped.heap)
        .deallocated_allocations
        .retain(|pointer, _| !fresh_blocks.contains(&pointer.base));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .pending_allocations
        .retain(|pointer, _| !fresh_blocks.contains(&pointer.base));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .uninitialized_allocations
        .retain(|pointer| !fresh_blocks.contains(&pointer.base));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .zeroed_allocations
        .retain(|pointer| !fresh_blocks.contains(&pointer.base));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .zeroed_prefix_allocations
        .retain(|pointer, _| !fresh_blocks.contains(&pointer.base));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .zeroed_pending_allocations
        .retain(|pointer| !fresh_blocks.contains(&pointer.base));
    stripped.record_diagnostic_transform(
        "remove internal heap bookkeeping",
        vec![after.clone(), before.clone(), function_entry.clone()],
        Vec::new(),
    );
    program_effect_memories_definitionally_equal(before, &stripped, assumptions)
}

fn heap_free_effect_is_valid(
    before: &SymbolicMemory,
    after: &SymbolicMemory,
    allocation_base: &Address,
    bytes: &AllocationSize,
) -> bool {
    // The effect states the freed size with its format, so the claim it
    // reinstates is the block's own, 32-bit or 64-bit.
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
/// facts its loads introduced and its outstanding evaluation obligations.
///
/// Only the kernel builds one, so a proof obligation opened from it
/// (`crate::kernel::proof::PropositionObligation::for_claim_goal`) is known
/// to state that claim, and the proposition completed from that obligation
/// says which claim it closes without anything being lowered or compared
/// again.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContractClaimGoal {
    target: FunctionContractClaimTarget,
    proposition: Proposition,
    facts: Vec<Proposition>,
    obligations: Vec<ProofObligation>,
}

impl ContractClaimGoal {
    pub(crate) fn unproved_requirements(
        &self,
        assumptions: &PureFactContext,
    ) -> Vec<ProofObligation> {
        self.obligations
            .iter()
            .filter(|obligation| {
                !ProofObligation::evaluation_requirement_is_established(
                    assumptions,
                    obligation.proposition(),
                )
            })
            .cloned()
            .collect()
    }

    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    /// The facts the goal's loads introduced.
    pub fn facts(&self) -> &[Proposition] {
        &self.facts
    }

    pub(crate) fn target(&self) -> &FunctionContractClaimTarget {
        &self.target
    }
}

/// The entry state as a contract reads it. A by-value aggregate parameter
/// denotes the image of the caller's argument, which nothing writes; the
/// callee's copy of it is private storage the body may overwrite. A caller
/// applying the contract reads the same thing: `bind_contract_arguments`
/// copies the argument into a block of its own that no body runs against.
fn contract_view_of_entry(
    mut entry_state: ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
) -> ExecutionState {
    for (parameter, argument) in function.parameters().iter().zip(arguments) {
        if let (Some(layout), ProgramExpression::Value(ProgramValue::Pointer(argument))) =
            (parameter.aggregate_layout(), argument)
        {
            entry_state.locals.set_aggregate_object_at(
                parameter.name().to_string(),
                layout.clone(),
                argument.address().clone(),
            );
        }
    }
    entry_state
}

/// Bind the checked exit value without crossing a native representation.
/// These are the same unqualified local rules used by the contract view before.
fn bind_contract_exit_value(
    state: &mut ExecutionState,
    name: crate::kernel::BindingName,
    value: &StoredExecutionValue,
    ty: ProgramType,
) {
    state.locals.set_retained_typed_with_all_qualifiers(
        name,
        value.clone(),
        ty,
        false,
        false,
        false,
        false,
    );
}

/// Entry and exit views prepared for lowering return claims at one fixed
/// frontier. The producer owns the states and facts; callers discard the
/// context when the outcome, ambient facts, or resource representation changes.
/// Predicate unfold choices affect individual goals, not these prepared views.
pub(crate) struct FunctionEnsureGoalContext<'a> {
    function: &'a ProgramFunction,
    entry_state: ExecutionState,
    post_state: ExecutionState,
    assumptions: PureFactContext,
}

impl<'a> FunctionEnsureGoalContext<'a> {
    pub(crate) fn new(
        function: &'a ProgramFunction,
        caller_state: &ExecutionState,
        arguments: &[ProgramExpression],
        outcome: &FunctionOutcome,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        let mut entry_state = contract_view_of_entry(
            program_function_entry_state(caller_state, function, arguments)?,
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
        Self::at_entry(
            function,
            caller_state,
            entry_state,
            outcome,
            assumptions,
            None,
        )
    }

    pub(crate) fn from_retained_entry(
        function: &'a ProgramFunction,
        entry: &RetainedClosingEntry,
        outcome: &FunctionOutcome,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        Self::at_entry(
            function,
            &entry.caller,
            entry.state.clone(),
            outcome,
            assumptions,
            Some(entry),
        )
    }

    fn at_entry(
        function: &'a ProgramFunction,
        caller_state: &ExecutionState,
        entry_state: ExecutionState,
        outcome: &FunctionOutcome,
        assumptions: &PureFactContext,
        retained_entry: Option<&RetainedClosingEntry>,
    ) -> Option<Self> {
        let FunctionOutcome::Return {
            value,
            state: return_state,
        } = outcome
        else {
            return None;
        };
        let exit_memory = crate::kernel::functions::function_exit_memory(
            caller_state,
            return_state,
            value,
            function,
        )
        .ok()?;
        let mut claim_return_state = (**return_state).clone().with_memory(exit_memory.clone());
        let resources = match retained_entry {
            Some(entry) => entry.prepare_exit_projection(
                function,
                return_state,
                &mut claim_return_state,
                assumptions,
            )?,
            None => expand_certification_exit(function, &claim_return_state, assumptions)?,
        };
        // The exit memory came from the return state, so the post state
        // stands after the return state's point, with the entry's locals.
        let mut post_state = entry_state
            .clone()
            .with_memory_continuing(return_state, exit_memory);
        post_state = post_state.with_resource_context(resources);
        post_state.observed_population_families = return_state.observed_population_families.clone();
        // Preserve checked body consumption evidence when reconstructing the exit.
        post_state.population_effects = return_state.population_effects.clone();
        if function.return_type() != ProgramType::Void {
            bind_contract_exit_value(
                &mut post_state,
                CONTRACT_RESULT,
                value,
                function.return_type(),
            );
        }
        Some(Self {
            function,
            entry_state,
            post_state,
            assumptions: assumptions.clone(),
        })
    }

    pub(crate) fn goals(&self, contract_index: usize) -> Result<Vec<ContractClaimGoal>, String> {
        let function = self.function;
        let entry_state = &self.entry_state;
        let post_state = &self.post_state;
        let assumptions = &self.assumptions;
        let ensure = function
            .contract_ensures()
            .get(contract_index)
            .ok_or_else(|| format!("no postcondition at contract index {contract_index}"))?;
        let ensure = function
            .predicate_unfoldings()
            .iter()
            .find(|unfolding| unfolding.body() == ensure)
            .map_or(ensure, PredicateUnfolding::predicate);
        let lowering_assumptions = assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .defer_non_exact_loadability_obligations();
        let mut budget = ExecutionBudget::beside_live_state();
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            post_state,
            ensure,
            Some(entry_state),
            &lowering_assumptions,
            &mut budget,
        )
        .map_err(|limit| format!("postcondition evaluation stopped at {}", limit.describe()))?;
        if paths.is_empty() {
            return Err(no_single_path_message("lowering", &paths, &budget));
        }
        let selected = exactly_selected_spec_proposition_path(&paths, assumptions);
        let paths = match selected {
            Some(path) if paths.len() > 1 => std::slice::from_ref(path),
            _ => paths.as_slice(),
        };
        Ok(paths
            .iter()
            .map(|path| ContractClaimGoal {
                target: FunctionContractClaimTarget::EnsureProposition(contract_index),
                proposition: path.proposition.clone(),
                obligations: path.obligations.clone(),
                facts: path
                    .facts
                    .iter()
                    .map(|fact| fact.proposition().clone())
                    .collect(),
            })
            .collect())
    }
}

/// Lowers one exceptional postcondition at a checked throwing outcome. The
/// exceptional family observes the thrown `int32` through the kernel's
/// reserved payload binding and observes the state at the throw boundary.
/// Returning outcomes do not owe an exceptional postcondition.
pub(crate) fn program_function_exceptional_ensure_goals(
    function: &ProgramFunction,
    contract_index: usize,
    caller_state: &ExecutionState,
    arguments: &[ProgramExpression],
    outcome: &FunctionOutcome,
    assumptions: &PureFactContext,
) -> Option<Vec<ContractClaimGoal>> {
    let mut entry_state = contract_view_of_entry(
        program_function_entry_state(caller_state, function, arguments)?,
        function,
        arguments,
    );
    let expanded_entry_resources = expand_all_composite_resource_facts(
        entry_state.resources(),
        function.composite_resource_definitions(),
        &entry_state.program_point(),
        assumptions,
    )?;
    entry_state = entry_state.with_resource_context(expanded_entry_resources);
    exceptional_goals_at_entry(function, contract_index, entry_state, outcome, assumptions)
}

pub(crate) fn program_function_exceptional_ensure_goals_from_entry(
    function: &ProgramFunction,
    contract_index: usize,
    entry: &RetainedClosingEntry,
    outcome: &FunctionOutcome,
    assumptions: &PureFactContext,
) -> Option<Vec<ContractClaimGoal>> {
    exceptional_goals_at_entry(
        function,
        contract_index,
        entry.state.clone(),
        outcome,
        assumptions,
    )
}

fn exceptional_goals_at_entry(
    function: &ProgramFunction,
    contract_index: usize,
    entry_state: ExecutionState,
    outcome: &FunctionOutcome,
    assumptions: &PureFactContext,
) -> Option<Vec<ContractClaimGoal>> {
    let ensure = function.exceptional_ensures().get(contract_index)?;
    let FunctionOutcome::Throw {
        value,
        state: throw_state,
    } = outcome
    else {
        return None;
    };
    let mut post_state = entry_state
        .clone()
        .with_memory(throw_state.memory().clone());
    post_state.observed_population_families = throw_state.observed_population_families.clone();
    bind_contract_exit_value(
        &mut post_state,
        CONTRACT_EXCEPTION,
        value,
        value.native().program_type(),
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
            super::program_loadability_obligation_impossible_with_assumptions(
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
            .map(|path| ContractClaimGoal {
                target: FunctionContractClaimTarget::ExceptionalEnsureProposition(contract_index),
                proposition: path.proposition.clone(),
                obligations: path.obligations.clone(),
                facts: path
                    .facts
                    .iter()
                    .map(|fact| fact.proposition().clone())
                    .collect(),
            })
            .collect(),
    )
}

/// Whether a lowered ensure folded to a constant truth: the kernel's own
/// evaluation at the outcome decided it, so it needs no completion.
fn lowered_goal_is_constant_true(proposition: &Proposition) -> bool {
    let constant_true = |proposition: &Proposition| matches!(&completion_key(proposition), condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Constant(true), _))));
    // Evaluation includes the read-over-write authority: a read of a
    // stored cell is the value stored there.
    constant_true(proposition)
        || crate::kernel::eval::comparison_form(proposition)
            .is_some_and(|resolved| constant_true(&resolved))
}

/// The form in which a completed proposition is matched against a lowered
/// ensure. The two are lowerings of one claim by different code: the proof
/// folds trivial conditions as it lowers (a term compared with itself, a
/// constant premise), the contract lowering keeps them. This folds both to
/// one form by exact structural rules: no fact is consulted.
pub(crate) fn completion_key(proposition: &Proposition) -> Proposition {
    fn truth(value: bool) -> Proposition {
        Proposition::condition_is(ConditionTerm::Constant(value), true)
    }
    fn as_truth(proposition: &Proposition) -> Option<bool> {
        match proposition {
            condition_source_0 @ Proposition::ConditionIs(_, value)
                if let Some((ConditionTerm::Constant(constant), _)) =
                    condition_source_0.condition_native() =>
            {
                Some(constant == value)
            }
            _ => None,
        }
    }
    fn reflexive(condition: &ConditionTerm) -> bool {
        match condition {
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            } => left == right,
            ConditionTerm::AddressEqual(left, right) => left == right,
            ConditionTerm::PointerEqual(left, right) => left == right,
            ConditionTerm::AddressOffsetEqual(left, right) => left == right,
            _ => false,
        }
    }
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            if let ConditionTerm::Constant(constant) = condition.native_compat() {
                truth(constant == value)
            } else if reflexive(condition.native_compat()) {
                truth(*value)
            } else {
                proposition.clone()
            }
        }
        // A predicate identity carries a resource-state state only when
        // its definition observes resource counts; the proof's lowering
        // leaves it empty otherwise. The outcome the completion was made
        // at fixes that state, so the key compares predicates without it.
        Proposition::Predicate { name, arguments } => {
            let mut arguments = arguments.clone();
            if let Some(Term::ExecutionState(state)) = arguments.first_mut() {
                **state = ExecutionState::new();
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
                    Proposition::condition_is(condition, !value)
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

/// The proof's completed propositions, by the contract claim each closed.
#[derive(Default)]
struct CheckedPropositionIndex<'a> {
    // The borrowed completions retain each Arc throughout this index's life;
    // addresses cannot be recycled while they serve as producer identity keys.
    by_path: BTreeMap<FunctionContractClaimTarget, BTreeSet<usize>>,
    by_claim: BTreeMap<FunctionContractClaimTarget, Vec<&'a CheckedFunctionProposition>>,
    by_literal_outcome: BTreeMap<
        FunctionContractClaimTarget,
        BTreeMap<(bool, ProgramValue), Vec<&'a CheckedFunctionProposition>>,
    >,
}

/// Index only bounded scalar payloads; hashing an arbitrary symbolic value or
/// an outcome's state would traverse the execution history on every lookup.
fn literal_completion_key(outcome: &FunctionOutcome) -> Option<(bool, ProgramValue)> {
    let (exceptional, value) = match outcome {
        FunctionOutcome::Return { value, .. } => (false, value),
        FunctionOutcome::Throw { value, .. } => (true, value),
        _ => return None,
    };
    // Only a literal root can export as a native constant. Inspect that root
    // before the compatibility boundary; compound results are not index keys.
    if let Some(root) = value.shared() {
        return match root.node() {
            KernelTermNode::MachineLiteral(literal) => Some((
                exceptional,
                MachineIntegerType::from_program_type(value.program_type())?
                    .value_from_term(literal.legacy_term()),
            )),
            KernelTermNode::Legacy(payload) => {
                let PureFunctionArgument::Value(native) = payload.value() else {
                    return None;
                };
                native_literal_completion_key(exceptional, native)
            }
            _ => None,
        };
    }
    native_literal_completion_key(exceptional, value.native_payload()?)
}

fn native_literal_completion_key(
    exceptional: bool,
    value: &ProgramValue,
) -> Option<(bool, ProgramValue)> {
    let term = match value.numeric_value() {
        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
        ProgramValue::Void => return Some((exceptional, ProgramValue::Void)),
        ProgramValue::Bool(term)
        | ProgramValue::Int8(term)
        | ProgramValue::Int16(term)
        | ProgramValue::Int32(term)
        | ProgramValue::UInt8(term)
        | ProgramValue::UInt16(term)
        | ProgramValue::UInt32(term)
        | ProgramValue::Int64(term)
        | ProgramValue::UInt64(term)
        | ProgramValue::Int128(term)
        | ProgramValue::UInt128(term)
        | ProgramValue::Float32(term)
        | ProgramValue::Float64(term) => term,
        ProgramValue::Pointer(_) | ProgramValue::Parameter(_) => return None,
    };
    match term {
        MachineTerm::Constant { .. } => Some((exceptional, value.clone())),
        _ => None,
    }
}

fn closing_path_is_unreachable(path: &SymbolicExecutionPath) -> bool {
    path.post_assumptions
        .as_ref()
        .unwrap_or(&path.assumptions)
        .has_retained_contradiction()
        || matches!(
            path.completion_origin,
            Some(FunctionOutcome::VerificationDiverges)
        )
}

/// Packages a body-less external contract as an opaque assumption. The
/// contract still has to be structurally complete and representable by the
/// kernel, but no body-safety or postcondition proof is claimed for it.
/// A construction return assumes completion into the checked caller-owned
/// destination, including its initialized value fields. Ordinary writable
/// buffers and void construction parameters receive no such guarantee.
pub fn program_external_function_rule(function: ProgramFunction) -> Option<ExternalFunctionRule> {
    (!function.is_program_entry()
        && function
            .contract_interface()
            .construction_parameter()
            .is_none()
        && function.verified_direct_contract_supported()
        && !function.contract_claims().is_empty()
        && function_contract_claims_are_complete(&function))
    .then_some(ExternalFunctionRule {
        function,
        scoped_unselected: false,
        representation_copy: None,
    })
}

/// Builds an untrusted ranking plan. Supplying a plan is not evidence; the
/// kernel validates it together with the exact verified C functions when it
/// checks the program's termination obligations.
pub fn program_function_termination_plan(
    function_name: impl Into<String>,
    recursive_measure: Option<FunctionTerminationMeasure>,
    loop_measures: impl IntoIterator<Item = (usize, LoopTerminationMeasure)>,
) -> FunctionTerminationPlan {
    FunctionTerminationPlan {
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
pub(crate) fn program_recursive_function_contract_hypothesis(
    function: ProgramFunction,
) -> Option<VerifiedFunctionRule> {
    (!function.is_program_entry()
        && function.verified_direct_contract_supported()
        && !function.contract_claims().is_empty()
        && function_contract_claims_are_complete(&function))
    .then(|| {
        VerifiedFunctionRule {
            pointer_result: None,
            function,
            // A hypothesis certified nothing, so it says nothing about loops.
            descent_completion: None,
            concrete_loop_exits: None,
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        }
    })
}

/// Creates a scoped body-independent assumption for a concrete function whose
/// proof is outside the current CLI selection. The interface is checked for
/// complete, representable direct claims, including the narrow exceptional
/// channel that public `extern` declarations do not support. The caller must
/// remove this rule before publishing the selected result's environment.
/// This is the kernel boundary for conditional partial verification; it never
/// certifies the unselected body.
pub(crate) fn program_unselected_function_contract_assumption(
    function: ProgramFunction,
) -> Option<ExternalFunctionRule> {
    (!function.is_program_entry()
        && function.verified_direct_contract_supported()
        && !function.contract_claims().is_empty()
        && function_contract_claims_are_complete(&function))
    .then_some(ExternalFunctionRule {
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
fn function_contract_claims_are_complete(function: &ProgramFunction) -> bool {
    let targets = function
        .contract_claims()
        .iter()
        .map(|claim| claim.target())
        .collect::<BTreeSet<_>>();
    (0..function.contract_ensures().len())
        .all(|index| targets.contains(&FunctionContractClaimTarget::EnsureProposition(index)))
        && (0..function.exceptional_ensures().len()).all(|index| {
            targets.contains(&FunctionContractClaimTarget::ExceptionalEnsureProposition(
                index,
            ))
        })
        && (0..function.resource_ensures().len())
            .all(|index| targets.contains(&FunctionContractClaimTarget::EnsureResource(index)))
        && (!function.contract_effect_claim_required()
            || function.contract_mutable().is_empty()
            || targets.contains(&FunctionContractClaimTarget::Effect))
}

#[cfg(test)]
mod heap_free_effect_tests {
    use super::*;

    /// A free effect reinstates the freed block's claim in the size's own
    /// format: a 64-bit block whose claim was not live before the free (a
    /// contract-imported allocation) is matched by its `uint64` size, and
    /// a 32-bit reading of the same byte term is not that block's free.
    #[test]
    fn a_free_effect_reinstates_a_64_bit_claim_in_its_format() {
        let base = Address {
            base: AddressBase::Heap(940_100),
            offset: AddressOffset::Constant(0),
        };
        let bytes = MachineTerm::uint64_multiply(
            MachineTerm::Variable(Variable(940_101)),
            MachineTerm::uint64_constant(4),
        );
        let wide = AllocationSize::new(bytes.clone(), AllocationSizeKind::UInt64);
        let before = SymbolicMemory::new();
        let after = before
            .clone()
            .with_heap_allocation_claim(base.clone(), wide.clone())
            .expect("a fresh claim")
            .free_heap_block(&base, &PureFactContext::new())
            .expect("a free of the claimed block");
        assert!(heap_free_effect_is_valid(&before, &after, &base, &wide));
        assert!(!heap_free_effect_is_valid(
            &before,
            &after,
            &base,
            &AllocationSize::int32(bytes),
        ));
    }
}

#[cfg(test)]
mod checked_proposition_index_tests {
    use super::*;

    fn route(variable: u64, value: bool) -> Proposition {
        Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(Variable(variable))),
                right: Box::new(MachineTerm::constant(1)),
            },
            value,
        )
    }

    fn lowering_candidate(marker: bool, facts: Vec<Proposition>) -> SpecPropositionPath {
        SpecPropositionPath {
            proposition: Proposition::condition_is(ConditionTerm::Constant(marker), true),
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
        let pointer = Address::symbolic(Variable(71_031));
        let equation = ExecutionPureFact::logical_read_equation(
            Pointer::new(pointer.clone(), ProgramType::Int32Pointer),
            Address::loaded_value(&intern_memory(SymbolicMemory::new()), &pointer),
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
        let truth = Proposition::condition_is(ConditionTerm::Constant(true), true);
        let checked = |claim: Option<FunctionContractClaimTarget>| {
            let function = ProgramFunction::new(
                ProgramType::Void,
                "indexed",
                Vec::new(),
                ProgramStatement::Skip,
            );
            let specification = FunctionSpecification::new(
                ExecutionState::new(),
                Vec::new(),
                Vec::new(),
                FunctionOutcome::Return {
                    value: ProgramValue::Void.into(),
                    state: Box::new(ExecutionState::new()),
                },
            );
            CheckedFunctionProposition {
                path_origin: None,
                function,
                specification,
                proposition: truth.clone(),
                claim,
            }
        };
        let first = FunctionContractClaimTarget::EnsureProposition(0);
        let second = FunctionContractClaimTarget::EnsureProposition(1);
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
        let function = ProgramFunction::new(
            ProgramType::Int32,
            "entry_resource_fact_boundary",
            Vec::new(),
            program_return(crate::kernel::program_expression::int32_literal(0)),
        );
        // This is deliberately a fact recorded by execution after entry.  It
        // must not make an entry-dependent resource term evaluable during
        // certification setup.
        let body_fact = Proposition::condition_is(
            ConditionTerm::signed_less_than(
                MachineTerm::Variable(Variable(93_001)),
                MachineTerm::constant(8),
            ),
            true,
        );
        let state = ExecutionState::new();
        let proposition = Proposition::ProgramFunctionVerifies {
            state: Box::new(state.clone()),
            function: Box::new(function.clone()),
            arguments: Vec::new(),
            outcome: FunctionOutcome::Return {
                value: ProgramValue::Int32(MachineTerm::constant(0)).into(),
                state: Box::new(state),
            },
        };
        let fact = ExecutionPureFact::new(body_fact.clone());
        let path = SymbolicExecutionPath {
            call_parameters: None,
            descent_step: None,
            completion_origin: None,
            call_result: None,
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
        let block = Address {
            base: AddressBase::Heap(424_242),
            offset: AddressOffset::Constant(0),
        };
        let mut base = SymbolicMemory::new().with_block(block.base.clone(), 4);
        std::sync::Arc::make_mut(&mut base.heap)
            .live_allocations
            .insert(block.clone(), AllocationSize::int32(4));
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
        assert!(!memories_definitionally_equal(&base, &other, &assumptions));
        assert!(!program_effect_memories_definitionally_equal(
            &base,
            &other,
            &assumptions,
        ));

        let left = FunctionOutcome::Return {
            value: ProgramValue::Int32(MachineTerm::constant(0)).into(),
            state: Box::new(ExecutionState::new().with_memory(base)),
        };
        let right = FunctionOutcome::Return {
            value: ProgramValue::Int32(MachineTerm::constant(0)).into(),
            state: Box::new(ExecutionState::new().with_memory(other)),
        };
        assert!(
            !program_function_outcomes_program_state_definitionally_equal(
                &left,
                &right,
                &assumptions,
            )
        );
    }
}

#[cfg(test)]
mod unproved_path_obligation_message_tests {
    use super::*;

    /// A certification refusal names the condition by the sentence its
    /// lowering wrote, never as a kernel term dump.
    #[test]
    fn names_the_obligation_by_its_context_without_a_term_dump() {
        let condition = Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: Box::new(MachineTerm::Variable(Variable(7))),
                right: Box::new(MachineTerm::constant(3)),
            },
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
        let base = Address::symbolic(Variable(984_400));
        let wide = MemoryRange::new_wide(
            base.clone(),
            MachineTerm::uint64_constant(0),
            MachineTerm::uint64_constant(1 << 33),
            1,
        );
        let narrow = MemoryRange::new_with_element_width(base, 0u32.into(), 1u32.into(), 1);
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

#[cfg(test)]
mod materialized_function_load_tests {
    use super::*;

    fn callback_load(memory: &SymbolicMemory, address: &Address, kind: LoadKind) -> ProgramValue {
        let load = MachineTerm::MemoryLoad(
            ProgramPoint::at(&(crate::kernel::intern_memory(memory.clone()))),
            Box::new(address.clone()),
            kind,
        );
        let (variable, _) = crate::kernel::load_variable_for_term(&load).unwrap();
        ProgramValue::typed_pointer(
            Address::symbolic_function(variable),
            ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
        )
    }

    #[test]
    fn canonical_function_pointer_cache_preserves_memory() {
        let address = Address {
            base: "callback-cache".into(),
            offset: AddressOffset::Constant(0),
        };
        let memory = SymbolicMemory::new().with_block("callback-cache", 16);
        let value = callback_load(
            &memory,
            &address,
            LoadKind::of_type(ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED))
                .unwrap(),
        );
        let facts = PureFactContext::new();
        assert!(materialized_load_is_unchanged(
            &value, &memory, &address, &facts
        ));
        let cached = memory.clone().store(address.clone(), value);
        assert!(memories_definitionally_equal(&memory, &cached, &facts));
        assert!(memories_definitionally_equal(&cached, &memory, &facts));
    }

    #[test]
    fn function_pointer_cache_requires_the_exact_cell_and_pointer_load() {
        let address = Address {
            base: "callback-cache-controls".into(),
            offset: AddressOffset::Constant(0),
        };
        let memory = SymbolicMemory::new().with_block("callback-cache-controls", 16);
        let facts = PureFactContext::new();
        let value = callback_load(
            &memory,
            &address,
            LoadKind::of_type(ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED))
                .unwrap(),
        );
        assert!(!materialized_load_is_unchanged(
            &value,
            &memory,
            &address.offset_by_bytes(8),
            &facts
        ));
        let narrow = callback_load(&memory, &address, LoadKind::UInt8);
        assert!(!materialized_load_is_unchanged(
            &narrow, &memory, &address, &facts
        ));
        let arbitrary = ProgramValue::typed_pointer(
            Address::symbolic_function(Variable(97_555_001)),
            ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
        );
        assert!(!materialized_load_is_unchanged(
            &arbitrary, &memory, &address, &facts
        ));
        let ProgramValue::Pointer(pointer_value) = value else {
            unreachable!()
        };
        let displaced = ProgramValue::typed_pointer(
            pointer_value.address().offset_by_bytes(1),
            pointer_value.program_type(),
        );
        assert!(!materialized_load_is_unchanged(
            &displaced, &memory, &address, &facts
        ));
        let changed = memory.clone().store(address.clone(), arbitrary);
        let original = callback_load(
            &memory,
            &address,
            LoadKind::of_type(ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED))
                .unwrap(),
        );
        assert!(!materialized_load_is_unchanged(
            &original, &changed, &address, &facts
        ));
    }
}

#[cfg(test)]
mod diagnostic_scaling_tests {
    use super::*;
    include!(
        "../../../scaling_tests/kernel/api/contract_certification/contract_claims/diagnostic_sample_tests.rs"
    );
}

#[cfg(test)]
mod claim_requirement_tests {
    use super::*;

    use crate::kernel::proof::{
        FunctionOutcomeObligation, OutcomeIdentity, OutcomeProofCore, OutcomeProofState,
        ProofBranch, ProofBranchState, ProofObject, ProofObligation as BranchObligation,
        PropositionKnownContext, PureFactStore,
    };

    type ClaimProof = ProofObject<(), BranchObligation<(), Arc<OutcomeProofState<()>>>, ()>;
    fn root(facts: PureFactStore, outcome: &Arc<OutcomeProofState<()>>) -> ClaimProof {
        ClaimProof::root(
            (),
            ProofBranch::new(
                BranchObligation::FunctionOutcome(FunctionOutcomeObligation::new(
                    0,
                    outcome.clone(),
                )),
                ProofBranchState {
                    facts,
                    execution: None,
                },
            ),
        )
    }

    #[test]
    fn claim_identity_requires_its_evaluation_obligations_in_this_context() {
        let domain = Proposition::condition_is(
            ConditionTerm::equal(
                MachineTerm::Variable(Variable(991_001)),
                MachineTerm::constant(1),
            ),
            true,
        );
        let truth = Proposition::condition_is(ConditionTerm::Constant(true), true);
        let empty = PureFactStore::from_ordered(std::slice::from_ref(&truth));
        let established = empty.with_kernel_checked_fact(domain.clone());
        for (target, is_exceptional) in [
            (FunctionContractClaimTarget::EnsureProposition(0), false),
            (
                FunctionContractClaimTarget::ExceptionalEnsureProposition(0),
                true,
            ),
        ] {
            let goal = ContractClaimGoal {
                target,
                proposition: truth.clone(),
                facts: vec![],
                obligations: vec![ProofObligation::verification_condition(domain.clone())],
            };
            let outcome = Arc::new(OutcomeProofState::new(
                OutcomeProofCore {
                    publication: None,
                    identity: OutcomeIdentity::fresh(),
                    result: int32(0).into(),
                    state: ExecutionState::new().into(),
                    store_consequences_available: false,
                    is_exceptional,
                    effect_facts: ExecutionFacts::new().into(),
                },
                (),
            ));
            assert!(
                root(empty.clone(), &outcome)
                    .focus_contract_claim(&goal, ())
                    .is_err(),
                "a true claim still owes its evaluation domain"
            );
            let mut assumable = goal.clone();
            assumable.obligations = vec![ProofObligation::new(domain.clone())];
            assert!(
                root(empty.clone(), &outcome)
                    .focus_contract_claim(&assumable, ())
                    .is_err(),
                "an assumable execution condition is not a proved claim requirement"
            );
            let checked = root(established.clone(), &outcome)
                .focus_contract_claim(&goal, ())
                .expect("the ordinary proof context establishes the domain")
                .apply_known(PropositionKnownContext::Exact)
                .unwrap_or_else(|_| panic!("the stated claim must close"));
            let completion = checked.completed_proposition().unwrap();
            assert_eq!(completion.claim(), Some(goal.target()));
            assert!(
                completion
                    .outcome()
                    .unwrap()
                    .identity
                    .same_as(&outcome.core.identity)
            );
            assert_eq!(completion.outcome().unwrap().is_exceptional, is_exceptional);
            assert!(
                root(empty.clone(), &outcome)
                    .focus_contract_claim(&goal, ())
                    .is_err(),
                "a sibling context acquires no authority from the completed proof"
            );
        }
    }
}

#[cfg(test)]
mod claim_requirement_scaling_tests {
    use super::*;
    use crate::kernel::proof::PureFactStore;
    include!(
        "../../../scaling_tests/kernel/api/contract_certification/contract_claims/requirements_tests.rs"
    );
}

#[cfg(test)]
mod retained_literal_completion_scaling_tests {
    include!(
        "../../../scaling_tests/kernel/api/contract_certification/contract_claims/retained_literals.rs"
    );
}

#[cfg(test)]
mod contract_closing_tests {
    use super::*;

    pub(super) fn fixture() -> ProgramFunction {
        program_function(
            ProgramType::Int32,
            "closed",
            vec![],
            program_return(crate::kernel::program_expression::int32_literal(0)),
        )
        .with_contract(
            vec![],
            vec![SpecProposition::Comparison {
                left: SpecExpression::ProgramExpression(
                    crate::kernel::program_expression::int32_literal(0),
                ),
                operator: ComparisonOperator::Equal,
                right: SpecExpression::ProgramExpression(
                    crate::kernel::program_expression::int32_literal(0),
                ),
            }],
            vec![],
            vec![FunctionContractClaim::ensure_proposition(0, 0)],
            true,
        )
    }
}

#[cfg(test)]
mod retained_contract_input_tests {
    use super::*;
    use crate::kernel::{
        AlgebraicType, ExecutionValue, KernelTermExport, KernelTermImport, KernelType,
        LocalBinding, SharedPointer, StoredExecutionValue,
    };

    fn prepared_input(value: StoredExecutionValue) -> StoredExecutionValue {
        let state = ExecutionState::new();
        let function = ProgramFunction::new(
            value.program_type(),
            "retained_input",
            vec![],
            ProgramStatement::Skip,
        );
        let outcome = FunctionOutcome::Return {
            value,
            state: Box::new(state.clone()),
        };
        let context = FunctionEnsureGoalContext::at_entry(
            &function,
            &state,
            state.clone(),
            &outcome,
            &PureFactContext::new(),
            None,
        )
        .unwrap();
        assert!(
            context
                .entry_state
                .locals
                .binding(CONTRACT_RESULT)
                .is_none()
        );
        let LocalBinding::Object { value, .. } =
            context.post_state.locals.binding(CONTRACT_RESULT).unwrap()
        else {
            panic!("contract result binding")
        };
        value.clone()
    }

    #[test]
    fn contract_input_preparation_preserves_roots_and_native_binding_rules() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::new(
            Address::symbolic(Variable(996801)),
            ProgramType::Int32Pointer,
        );
        let roots = vec![
            KernelTerm::variable(KernelType::Program(ProgramType::UInt64), Variable(996802)),
            KernelTerm::variable(KernelType::Program(ProgramType::Float64), Variable(996803)),
            KernelTermImport::default().condition(&ConditionTerm::Variable(Variable(996804))),
            KernelTerm::variable(
                KernelType::Algebraic(AlgebraicType::parameter("T".into())),
                Variable(996805),
            ),
            KernelTerm::shared_pointer_value(SharedPointer::import(&pointer)),
            KernelTerm::shared_pointer_value(SharedPointer::import(
                &pointer.with_pointee_constant(true),
            )),
        ];
        for root in roots {
            let input = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
            let actual = prepared_input(input.clone());
            assert!(actual.shared().is_some());
            let mut old = ExecutionState::new();
            old.locals.set_typed(
                CONTRACT_RESULT,
                input.clone().into_native(),
                input.program_type(),
            );
            let LocalBinding::Object {
                value: expected, ..
            } = old.locals.binding(CONTRACT_RESULT).unwrap()
            else {
                panic!()
            };
            let expected = expected.clone().into_native();
            if let ProgramValue::Pointer(pointer) = &expected {
                assert!(
                    actual
                        .shared()
                        .unwrap()
                        .pointer_payload()
                        .unwrap()
                        .same_source_payload(&SharedPointer::import(pointer))
                );
            } else {
                assert_eq!(actual.shared(), Some(&root));
            }
            assert_eq!(actual.into_native(), expected);
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        use super::*;
        include!(
            "../../../scaling_tests/kernel/api/contract_certification/contract_claims/retained_inputs.rs"
        );
    }
}
