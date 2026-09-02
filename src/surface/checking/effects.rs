use super::*;

pub(in crate::surface) fn prove_effect_clause(
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &[crate::kernel::ExecutionPureFact],
    available_pure_facts: &[Proposition],
    effect: &Effect,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
) -> Result<(), ClickError> {
    let CFunctionOutcome::Return { .. } = outcome else {
        return Err(ClickError::new(format!(
            "`{claim_label}` failed on path {path_index}: {}\n{}",
            describe_function_outcome(outcome, parameters, arguments),
            describe_proof_context(
                available_pure_facts,
                pre_state.resources().facts(),
                parameters,
                arguments,
                execution_pure_facts
            )
        )));
    };
    prove_mutation_footprint_with_policy(
        claim_label,
        path_index,
        execution_pure_facts,
        available_pure_facts,
        parameters,
        arguments,
        pre_state,
        effect,
        FootprintProofPolicy::Contextual,
    )
}

pub(in crate::surface) fn prove_effect_clause_exact(
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &[crate::kernel::ExecutionPureFact],
    available_pure_facts: &[Proposition],
    effect: &Effect,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
) -> Result<(), ClickError> {
    let CFunctionOutcome::Return { .. } = outcome else {
        return Err(ClickError::new(format!(
            "`{claim_label}` failed on path {path_index}: {}",
            describe_function_outcome(outcome, parameters, arguments)
        )));
    };
    prove_mutation_footprint_with_policy(
        claim_label,
        path_index,
        execution_pure_facts,
        available_pure_facts,
        parameters,
        arguments,
        pre_state,
        effect,
        FootprintProofPolicy::Exact,
    )
}

fn check_effect_planning_deadline() -> Result<(), ClickError> {
    if crate::instrumentation::deadline_exceeded() {
        Err(ClickError::new(format!(
            "verification budget exhausted inside {}",
            crate::instrumentation::deadline_context()
        )))
    } else {
        Ok(())
    }
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn plan_effect_clause_derivations(
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &[crate::kernel::ExecutionPureFact],
    available_pure_facts: &[Proposition],
    implicit_pure_facts: &[Proposition],
    effect: &Effect,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
) -> Result<Vec<PropositionDerivation>, ClickError> {
    check_effect_planning_deadline()?;
    let CFunctionOutcome::Return { .. } = outcome else {
        return Err(ClickError::new(format!(
            "`{claim_label}` failed on path {path_index}: {}",
            describe_function_outcome(outcome, parameters, arguments)
        )));
    };
    let segments = match effect {
        Effect::Immutable => Vec::new(),
        Effect::Mutable(segments) => segments
            .iter()
            .map(|segment| {
                evaluate_effect_segment(
                    parameters,
                    arguments,
                    pre_state,
                    available_pure_facts,
                    segment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` failed on path {path_index}: could not evaluate mutable segment `{}`: {message}",
                        describe_contract_segment(segment)
                    ))
                })
            })
            .collect::<Result<Vec<_>, _>>()?,
    };
    let mut effect_facts = execution_pure_facts.to_vec();
    effect_facts.extend(
        available_pure_facts
            .iter()
            .filter(|proposition| {
                matches!(
                    proposition,
                    Proposition::CMemoryMutatesOnly { .. }
                        | Proposition::CMemoryEffectSummary { .. }
                        | Proposition::CHeapAllocationFreed { .. }
                )
            })
            .cloned()
            .map(ExecutionPureFact::new),
    );
    let mut reasoning_facts = available_pure_facts.to_vec();
    reasoning_facts.extend(effect_facts.iter().map(|fact| fact.proposition().clone()));
    let mut direct_facts = available_pure_facts.to_vec();
    for fact in execution_pure_facts {
        if fact.transport_theorem().is_some() && !direct_facts.contains(fact.proposition()) {
            direct_facts.push(fact.proposition().clone());
        }
    }
    let mut assumptions = None;
    let mut derivations = Vec::new();
    let mut writes = memory_effect_write_pointers(&effect_facts);
    writes.retain(|pointer| is_preexisting_effect_pointer(pointer, pre_state));

    for pointer in &writes {
        check_effect_planning_deadline()?;
        // Most concrete writes already sit at a constant offset inside a
        // declared mutable object. Match the exact check rule first; building
        // a contextual assumptions index over a long execution history is
        // unnecessary in that overwhelmingly common case.
        if segments
            .iter()
            .any(|segment| segment_contains_pointer_exact(segment, pointer, implicit_pure_facts))
        {
            continue;
        }
        if let Some(selected) = segments.iter().find_map(|segment| {
            let goals =
                pointer_containment_goals_with_exact_base(segment, pointer, implicit_pure_facts)?;
            derive_goals_from_individual_facts(goals, &direct_facts)
        }) {
            append_unique_derivations(&mut derivations, selected);
            continue;
        }
        check_effect_planning_deadline()?;
        let assumptions =
            assumptions.get_or_insert_with(|| assumptions_from_propositions(&reasoning_facts));
        let selected = segments.iter().find_map(|segment| {
            if crate::instrumentation::deadline_exceeded() {
                return None;
            }
            let goals = pointer_containment_goals(segment, pointer, assumptions)?;
            derive_goals_from_individual_facts(goals.clone(), &direct_facts).or_else(|| {
                goals
                    .into_iter()
                    .map(|goal| assumptions.derive_proposition(&goal))
                    .collect::<Option<Vec<_>>>()
            })
        });
        check_effect_planning_deadline()?;
        let Some(selected) = selected else {
            return prove_effect_clause(
                claim_label,
                path_index,
                execution_pure_facts,
                available_pure_facts,
                effect,
                parameters,
                arguments,
                pre_state,
                outcome,
            )
            .and_then(|()| {
                Err(ClickError::new(format!(
                    "`{claim_label}` failed on path {path_index}: contextual footprint proof did not produce checkable derivations"
                )))
            });
        };
        append_unique_derivations(&mut derivations, selected);
    }

    for range in effect_facts
        .iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::CMemoryEffectSummary {
                before,
                mutable_ranges,
                ..
            } => Some(mutable_ranges.iter().map(move |range| (before, range))),
            _ => None,
        })
        .flatten()
        .filter(|(before, range)| {
            is_preexisting_effect_pointer(range.base(), pre_state)
                // Same fresh-allocation exemption as the footprint proof:
                // a range keyed to an allocation the summary's own entry
                // memory holds live, with no matching allocation at function
                // entry, is not governed by the entry footprint.
                && !(crate::kernel::c_memory_holds_live_heap_allocation_at(before, range.base())
                    && !crate::kernel::c_memory_holds_live_heap_allocation_at(
                        pre_state.memory(),
                        range.base(),
                    ))
        })
        .map(|(_, range)| range)
    {
        check_effect_planning_deadline()?;
        if segments
            .iter()
            .any(|segment| segment_contains_range_exact(segment, range, implicit_pure_facts))
        {
            continue;
        }
        if let Some(selected) = segments.iter().find_map(|segment| {
            let goals =
                range_containment_goals_with_exact_base(segment, range, implicit_pure_facts)?;
            derive_goals_from_individual_facts(goals, &direct_facts)
        }) {
            append_unique_derivations(&mut derivations, selected);
            continue;
        }
        check_effect_planning_deadline()?;
        let assumptions =
            assumptions.get_or_insert_with(|| assumptions_from_propositions(&reasoning_facts));
        let selected = segments.iter().find_map(|segment| {
            if crate::instrumentation::deadline_exceeded() {
                return None;
            }
            let goals = range_containment_goals(segment, range, assumptions)?;
            derive_goals_from_individual_facts(goals.clone(), &direct_facts).or_else(|| {
                goals
                    .into_iter()
                    .map(|goal| assumptions.derive_proposition(&goal))
                    .collect::<Option<Vec<_>>>()
            })
        });
        check_effect_planning_deadline()?;
        let Some(selected) = selected else {
            return prove_effect_clause(
                claim_label,
                path_index,
                execution_pure_facts,
                available_pure_facts,
                effect,
                parameters,
                arguments,
                pre_state,
                outcome,
            )
            .and_then(|()| {
                Err(ClickError::new(format!(
                    "`{claim_label}` failed on path {path_index}: contextual footprint proof did not produce checkable derivations"
                )))
            });
        };
        append_unique_derivations(&mut derivations, selected);
    }

    Ok(derivations)
}

fn append_unique_derivations(
    derivations: &mut Vec<PropositionDerivation>,
    additional: Vec<PropositionDerivation>,
) {
    for derivation in additional {
        if !derivations
            .iter()
            .any(|existing| existing.conclusion() == derivation.conclusion())
        {
            derivations.push(derivation);
        }
    }
}

#[derive(Clone, Copy)]
enum FootprintProofPolicy {
    Exact,
    Contextual,
}

#[allow(clippy::too_many_arguments)]
fn prove_mutation_footprint_with_policy(
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &[crate::kernel::ExecutionPureFact],
    available_pure_facts: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    effect: &Effect,
    policy: FootprintProofPolicy,
) -> Result<(), ClickError> {
    let segments = match effect {
        Effect::Immutable => Vec::new(),
        Effect::Mutable(segments) => segments
            .iter()
            .map(|segment| {
                if segment.state != ContractSegmentState::Current {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` failed on path {path_index}: `mutable` expects current-state segments"
                    )));
                }
                evaluate_effect_segment(
                    parameters,
                    arguments,
                    pre_state,
                    available_pure_facts,
                    segment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` failed on path {path_index}: could not evaluate mutable segment `{}`: {message}",
                        describe_contract_segment(segment)
                    ))
                })
            })
            .collect::<Result<Vec<_>, _>>()?,
    };
    let mut effect_facts = execution_pure_facts.to_vec();
    effect_facts.extend(
        available_pure_facts
            .iter()
            .filter(|proposition| {
                matches!(
                    proposition,
                    Proposition::CMemoryMutatesOnly { .. }
                        | Proposition::CMemoryEffectSummary { .. }
                        | Proposition::CHeapAllocationFreed { .. }
                )
            })
            .cloned()
            .map(ExecutionPureFact::new),
    );
    // Exact certificate validation uses only propositions named by the
    // certificate. Building a contextual assumptions database here is both
    // unnecessary and pathological after a long execution has accumulated
    // many memory snapshots.
    let contextual_assumptions = if matches!(policy, FootprintProofPolicy::Contextual) {
        let mut effect_reasoning_facts = available_pure_facts.to_vec();
        effect_reasoning_facts.extend(effect_facts.iter().map(|fact| fact.proposition().clone()));
        Some(assumptions_from_propositions(&effect_reasoning_facts))
    } else {
        None
    };
    let mut writes = memory_effect_write_pointers(&effect_facts);
    writes.retain(|pointer| is_preexisting_effect_pointer(pointer, pre_state));

    for pointer in &writes {
        if !segments.iter().any(|segment| match policy {
            FootprintProofPolicy::Exact => {
                segment_contains_pointer_exact(segment, pointer, available_pure_facts)
            }
            FootprintProofPolicy::Contextual => segment_contains_pointer(
                segment,
                pointer,
                contextual_assumptions
                    .as_ref()
                    .expect("contextual footprint proof has assumptions"),
            ),
        }) {
            return Err(ClickError::new(format!(
                "`{claim_label}` failed on path {path_index}: write to `{}` is outside the mutable footprint\n  mutable segments: {}\n  evaluated segments: {}\n  execution pure facts: {}",
                describe_pointer(pointer, parameters, arguments),
                describe_contract_segments(&segments),
                describe_evaluated_segments(&segments),
                describe_execution_pure_facts(execution_pure_facts)
            )));
        }
    }

    let effect_summary_ranges = effect_facts
        .iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::CMemoryEffectSummary {
                before,
                mutable_ranges,
                ..
            } => Some(mutable_ranges.iter().map(move |range| (before, range))),
            _ => None,
        })
        .flatten()
        .filter(|(before, range)| {
            is_preexisting_effect_pointer(range.base(), pre_state)
                // A range keyed to a heap allocation the summary's own entry
                // memory holds live, with no matching live allocation at
                // function entry, writes memory the caller could not have
                // held when the footprint was declared (a callee reallocated
                // it mid-execution); the entry footprint does not govern it.
                // Forms are kernel-minted, so an entry allocation always
                // matches its own entry key up to exact materialization.
                && !(crate::kernel::c_memory_holds_live_heap_allocation_at(
                    before,
                    range.base(),
                ) && !crate::kernel::c_memory_holds_live_heap_allocation_at(
                    pre_state.memory(),
                    range.base(),
                ))
        })
        .map(|(_, range)| range);

    for range in effect_summary_ranges {
        if !segments.iter().any(|segment| match policy {
            FootprintProofPolicy::Exact => {
                segment_contains_range_exact(segment, range, available_pure_facts)
            }
            FootprintProofPolicy::Contextual => segment_contains_range(
                segment,
                range,
                contextual_assumptions
                    .as_ref()
                    .expect("contextual footprint proof has assumptions"),
            ),
        }) {
            return Err(ClickError::new(format!(
                "`{claim_label}` failed on path {path_index}: effect summary range `{}` is outside the mutable footprint\n  mutable segments: {}\n  evaluated segments: {}\n  execution pure facts: {}",
                describe_memory_range(range, parameters, arguments),
                describe_contract_segments(&segments),
                describe_evaluated_segments(&segments),
                describe_execution_pure_facts(execution_pure_facts)
            )));
        }
    }

    Ok(())
}

fn exact_proposition_is_available_or_true(
    required: &Proposition,
    available: &[Proposition],
) -> bool {
    // Comparison is by canonical form: a load term and the load variable
    // for the same load are one fact. The canonical form is
    // deterministic and assumption-free, so the exact policy stays
    // check-identical.
    let required = crate::kernel::canonical_condition_fact(required);
    fn contains(fact: &Proposition, required: &Proposition) -> bool {
        crate::kernel::canonical_condition_fact(fact) == *required
            || matches!(fact, Proposition::And(left, right)
                if contains(left, required) || contains(right, required))
    }

    available.iter().any(|fact| contains(fact, &required))
        || matches!(normalize_proposition(&required), SimpProposition::True)
}

fn segment_contains_pointer_exact(
    segment: &EvaluatedContractSegment,
    pointer: &Pointer,
    available: &[Proposition],
) -> bool {
    let Some(index) = pointer_element_index_from_base_exact(pointer, &segment.base, available)
    else {
        return false;
    };
    exact_proposition_is_available_or_true(
        &Proposition::ConditionIs(
            signed_less_equal(segment.start.clone(), index.clone()),
            true,
        ),
        available,
    ) && exact_proposition_is_available_or_true(
        &Proposition::ConditionIs(signed_less_than(index, segment.end.clone()), true),
        available,
    )
}

fn pointer_containment_goals(
    segment: &EvaluatedContractSegment,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> Option<Vec<Proposition>> {
    let (index, mut goals) =
        pointer_element_index_from_base_with_alignment(pointer, &segment.base, assumptions)?;
    goals.extend([
        Proposition::ConditionIs(
            signed_less_equal(segment.start.clone(), index.clone()),
            true,
        ),
        Proposition::ConditionIs(signed_less_than(index, segment.end.clone()), true),
    ]);
    Some(goals)
}

fn pointer_containment_goals_with_exact_base(
    segment: &EvaluatedContractSegment,
    pointer: &Pointer,
    available: &[Proposition],
) -> Option<Vec<Proposition>> {
    let index = pointer_element_index_from_base_exact(pointer, &segment.base, available)?;
    Some(vec![
        Proposition::ConditionIs(
            signed_less_equal(segment.start.clone(), index.clone()),
            true,
        ),
        Proposition::ConditionIs(signed_less_than(index, segment.end.clone()), true),
    ])
}

fn segment_contains_range_exact(
    segment: &EvaluatedContractSegment,
    range: &CMemoryRange,
    available: &[Proposition],
) -> bool {
    let Some(base_index) =
        pointer_element_index_from_base_exact(range.base(), &segment.base, available)
    else {
        return false;
    };
    let range_start = bitvector32_add(base_index.clone(), range.start().clone());
    let range_end = bitvector32_add(base_index, range.end().clone());
    exact_proposition_is_available_or_true(
        &Proposition::ConditionIs(signed_less_equal(segment.start.clone(), range_start), true),
        available,
    ) && exact_proposition_is_available_or_true(
        &Proposition::ConditionIs(signed_less_equal(range_end, segment.end.clone()), true),
        available,
    )
}

fn range_containment_goals(
    segment: &EvaluatedContractSegment,
    range: &CMemoryRange,
    assumptions: &PureFactContext,
) -> Option<Vec<Proposition>> {
    let (base_index, mut goals) =
        pointer_element_index_from_base_with_alignment(range.base(), &segment.base, assumptions)?;
    let range_start = bitvector32_add(base_index.clone(), range.start().clone());
    let range_end = bitvector32_add(base_index, range.end().clone());
    goals.extend([
        Proposition::ConditionIs(signed_less_equal(segment.start.clone(), range_start), true),
        Proposition::ConditionIs(signed_less_equal(range_end, segment.end.clone()), true),
    ]);
    Some(goals)
}

fn range_containment_goals_with_exact_base(
    segment: &EvaluatedContractSegment,
    range: &CMemoryRange,
    available: &[Proposition],
) -> Option<Vec<Proposition>> {
    let base_index = pointer_element_index_from_base_exact(range.base(), &segment.base, available)?;
    let range_start = bitvector32_add(base_index.clone(), range.start().clone());
    let range_end = bitvector32_add(base_index, range.end().clone());
    Some(vec![
        Proposition::ConditionIs(signed_less_equal(segment.start.clone(), range_start), true),
        Proposition::ConditionIs(signed_less_equal(range_end, segment.end.clone()), true),
    ])
}

fn derive_goals_from_individual_facts(
    goals: Vec<Proposition>,
    available: &[Proposition],
) -> Option<Vec<PropositionDerivation>> {
    goals
        .into_iter()
        .map(|goal| {
            available.iter().find_map(|fact| {
                if crate::instrumentation::deadline_exceeded() {
                    return None;
                }
                PureFactContext::new()
                    .assume_proposition(fact.clone())
                    .derive_proposition_without_premise_minimization(&goal)
            })
        })
        .collect()
}

#[cfg(test)]
mod effect_planning_tests {
    use super::*;

    #[test]
    fn a_single_strict_bound_certifies_the_adjacent_range_end() {
        let index = Bitvector32Term::Variable(Variable(920));
        let capacity = Bitvector32Term::Variable(Variable(921));
        let available =
            Proposition::ConditionIs(signed_less_than(index.clone(), capacity.clone()), true);
        let goal = Proposition::ConditionIs(
            signed_less_equal(
                bitvector32_add(index, Bitvector32Term::Constant(1)),
                capacity,
            ),
            true,
        );

        let derivations = derive_goals_from_individual_facts(vec![goal.clone()], &[available])
            .expect("one strict bound should certify the adjacent range end");
        assert_eq!(derivations.len(), 1);
        assert_eq!(derivations[0].conclusion(), &goal);
    }
}

fn pointer_offset_alignment_goal(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
) -> Proposition {
    Proposition::ConditionIs(
        ConditionTerm::PointerOffsetEqual(Box::new(left.clone()), Box::new(right.clone())),
        true,
    )
}

fn pointer_offsets_align_exact(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    available: &[Proposition],
) -> bool {
    crate::kernel::offsets_have_same_canonical_form(left, right)
        || exact_proposition_is_available_or_true(
            &pointer_offset_alignment_goal(left, right),
            available,
        )
}

fn pointer_element_index_from_base_exact(
    pointer: &Pointer,
    base: &Pointer,
    available: &[Proposition],
) -> Option<Bitvector32Term> {
    if pointer.block != base.block {
        return None;
    }
    if pointer.offset == base.offset
        || pointer_offsets_align_exact(&pointer.offset, &base.offset, available)
    {
        return Some(Bitvector32Term::Constant(0));
    }
    if base.offset == PointerOffsetTerm::Constant(0) {
        return int32_element_index_from_pointer_offset(&pointer.offset);
    }
    match &pointer.offset {
        PointerOffsetTerm::Add(left, right)
            if left.as_ref() == &base.offset
                || pointer_offsets_align_exact(left, &base.offset, available) =>
        {
            int32_element_index_from_pointer_offset(right)
        }
        PointerOffsetTerm::Add(left, right)
            if right.as_ref() == &base.offset
                || pointer_offsets_align_exact(right, &base.offset, available) =>
        {
            int32_element_index_from_pointer_offset(left)
        }
        _ => {
            let pointer_index = int32_element_index_from_pointer_offset(&pointer.offset)?;
            let base_index = int32_element_index_from_pointer_offset(&base.offset)?;
            Some(bitvector_index_relative_to_base(pointer_index, base_index))
        }
    }
}

fn bitvector_index_relative_to_base(
    pointer_index: Bitvector32Term,
    base_index: Bitvector32Term,
) -> Bitvector32Term {
    if pointer_index == base_index {
        return Bitvector32Term::Constant(0);
    }
    if let Bitvector32Term::Add(left, right) = &pointer_index {
        if left.as_ref() == &base_index {
            return right.as_ref().clone();
        }
        if right.as_ref() == &base_index {
            return left.as_ref().clone();
        }
    }
    bitvector32_subtract(pointer_index, base_index)
}

fn pointer_element_index_from_base_with_alignment(
    pointer: &Pointer,
    base: &Pointer,
    assumptions: &PureFactContext,
) -> Option<(Bitvector32Term, Vec<Proposition>)> {
    if pointer.block != base.block {
        return None;
    }
    if pointer.offset == base.offset {
        return Some((Bitvector32Term::Constant(0), Vec::new()));
    }
    if pointer_offsets_equal_for_effect(&pointer.offset, &base.offset, assumptions) {
        return Some((
            Bitvector32Term::Constant(0),
            vec![pointer_offset_alignment_goal(&pointer.offset, &base.offset)],
        ));
    }
    if base.offset == PointerOffsetTerm::Constant(0) {
        return Some((
            int32_element_index_from_pointer_offset(&pointer.offset)?,
            Vec::new(),
        ));
    }
    match &pointer.offset {
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &base.offset => {
            Some((int32_element_index_from_pointer_offset(right)?, Vec::new()))
        }
        PointerOffsetTerm::Add(left, right)
            if pointer_offsets_equal_for_effect(left, &base.offset, assumptions) =>
        {
            Some((
                int32_element_index_from_pointer_offset(right)?,
                vec![pointer_offset_alignment_goal(left, &base.offset)],
            ))
        }
        PointerOffsetTerm::Add(left, right) if right.as_ref() == &base.offset => {
            Some((int32_element_index_from_pointer_offset(left)?, Vec::new()))
        }
        PointerOffsetTerm::Add(left, right)
            if pointer_offsets_equal_for_effect(right, &base.offset, assumptions) =>
        {
            Some((
                int32_element_index_from_pointer_offset(left)?,
                vec![pointer_offset_alignment_goal(right, &base.offset)],
            ))
        }
        _ => {
            let pointer_index = int32_element_index_from_pointer_offset(&pointer.offset)?;
            let base_index = int32_element_index_from_pointer_offset(&base.offset)?;
            Some((
                bitvector_index_relative_to_base(pointer_index, base_index),
                Vec::new(),
            ))
        }
    }
}

pub(in crate::surface) fn is_effect_relevant_pointer(pointer: &Pointer) -> bool {
    !pointer.block.starts_with("local:") && !pointer.block.starts_with("havoc:")
}

fn is_preexisting_effect_pointer(pointer: &Pointer, pre_state: &CState) -> bool {
    is_effect_relevant_pointer(pointer)
        && (!matches!(
            pointer.block,
            PointerBlock::Heap(_) | PointerBlock::Symbolic(_)
        ) || pre_state.memory().has_block(&pointer.block)
            || pre_state.memory().is_live_heap_address(pointer))
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct EvaluatedContractSegment {
    pub(in crate::surface) source: ContractSegment,
    pub(in crate::surface) base: Pointer,
    pub(in crate::surface) start: Bitvector32Term,
    pub(in crate::surface) end: Bitvector32Term,
    pub(in crate::surface) element_width: u32,
}

pub(in crate::surface) fn evaluate_effect_segment(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    entry_state: &CState,
    available_pure_facts: &[Proposition],
    segment: &ContractSegment,
) -> Result<EvaluatedContractSegment, String> {
    if segment.state != ContractSegmentState::Current {
        return Err(
            "effect segments are already entry-state references; `old(...)` is not supported here"
                .to_string(),
        );
    }
    let parameter_values =
        parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let evaluate = |assumptions: &PureFactContext| {
        let base = evaluate_c_contract_expression(
            &parameter_values,
            entry_state,
            None,
            assumptions,
            &segment.base,
        )?;
        let CValue::Pointer(base) = base else {
            return Err("segment base did not evaluate to a pointer".to_string());
        };
        let start = evaluate_c_contract_expression(
            &parameter_values,
            entry_state,
            None,
            assumptions,
            &segment.start,
        )?;
        let CValue::Int32(start) = start else {
            return Err("segment start did not evaluate to int32".to_string());
        };
        let end = evaluate_c_contract_expression(
            &parameter_values,
            entry_state,
            None,
            assumptions,
            &segment.end,
        )?;
        let CValue::Int32(end) = end else {
            return Err("segment end did not evaluate to int32".to_string());
        };

        Ok(EvaluatedContractSegment {
            source: segment.clone(),
            base,
            start,
            end,
            element_width: contract_segment_element_width(parameters, segment),
        })
    };

    // Most effect clauses are direct entry-state places. Evaluate those
    // without indexing the proof's accumulated snapshot facts; fall back to
    // contextual equality reasoning only when the expression actually needs
    // it.
    evaluate(&PureFactContext::new())
        .or_else(|_| {
            let assumptions = assumptions_from_propositions(available_pure_facts);
            evaluate(&assumptions)
        })
        .or_else(|_| {
            // A footprint may name a place inside a composite the contract
            // owns but the entry state keeps folded (a field of a contained
            // unit, say). Its loads are contract loads: name them
            // symbolically, as requirement lowering does; certification
            // re-evaluates the footprint against the expanded entry
            // resources and is the authority on their loadability.
            let assumptions = assumptions_from_propositions(available_pure_facts)
                .allow_symbolic_contract_loads()
                .prefer_symbolic_external_loads();
            evaluate(&assumptions)
        })
}

pub(in crate::surface) fn evaluate_requirement_segment(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    entry_state: &CState,
    segment: &ContractSegment,
) -> Result<EvaluatedContractSegment, String> {
    if segment.state != ContractSegmentState::Current {
        return Err(
            "requirement segments are entry-state references; `old(...)` is not supported here"
                .to_string(),
        );
    }
    let parameter_values =
        parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let assumptions = PureFactContext::new();
    let base = evaluate_c_contract_expression(
        &parameter_values,
        entry_state,
        None,
        &assumptions,
        &segment.base,
    )?;
    let CValue::Pointer(base) = base else {
        return Err("segment base did not evaluate to a pointer".to_string());
    };
    let start = evaluate_c_contract_expression(
        &parameter_values,
        entry_state,
        None,
        &assumptions,
        &segment.start,
    )?;
    let CValue::Int32(start) = start else {
        return Err("segment start did not evaluate to int32".to_string());
    };
    let end = evaluate_c_contract_expression(
        &parameter_values,
        entry_state,
        None,
        &assumptions,
        &segment.end,
    )?;
    let CValue::Int32(end) = end else {
        return Err("segment end did not evaluate to int32".to_string());
    };

    Ok(EvaluatedContractSegment {
        source: segment.clone(),
        base,
        start,
        end,
        element_width: contract_segment_element_width(parameters, segment),
    })
}

pub(in crate::surface) fn segment_contains_pointer(
    segment: &EvaluatedContractSegment,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    let Some(index) = pointer_element_index_from_base(pointer, &segment.base, assumptions) else {
        return false;
    };
    assumptions.proves(&Proposition::ConditionIs(
        signed_less_equal(segment.start.clone(), index.clone()),
        true,
    )) && assumptions.proves(&Proposition::ConditionIs(
        signed_less_than(index, segment.end.clone()),
        true,
    ))
}

pub(in crate::surface) fn segment_contains_range(
    segment: &EvaluatedContractSegment,
    range: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    let Some(base_index) =
        pointer_element_index_from_base(range.base(), &segment.base, assumptions)
    else {
        return false;
    };
    let range_start = bitvector32_add(base_index.clone(), range.start().clone());
    let range_end = bitvector32_add(base_index, range.end().clone());

    assumptions.proves(&Proposition::ConditionIs(
        signed_less_equal(segment.start.clone(), range_start),
        true,
    )) && assumptions.proves(&Proposition::ConditionIs(
        signed_less_equal(range_end, segment.end.clone()),
        true,
    ))
}

pub(in crate::surface) fn pointer_element_index_from_base(
    pointer: &Pointer,
    base: &Pointer,
    assumptions: &PureFactContext,
) -> Option<Bitvector32Term> {
    if pointer.block != base.block {
        return None;
    }

    if pointer.offset == base.offset
        || pointer_offsets_equal_for_effect(&pointer.offset, &base.offset, assumptions)
    {
        return Some(Bitvector32Term::Constant(0));
    }

    if base.offset == PointerOffsetTerm::Constant(0) {
        return int32_element_index_from_pointer_offset(&pointer.offset);
    }

    match &pointer.offset {
        PointerOffsetTerm::Add(left, right)
            if left.as_ref() == &base.offset
                || pointer_offsets_equal_for_effect(left, &base.offset, assumptions) =>
        {
            int32_element_index_from_pointer_offset(right)
        }
        PointerOffsetTerm::Add(left, right)
            if right.as_ref() == &base.offset
                || pointer_offsets_equal_for_effect(right, &base.offset, assumptions) =>
        {
            int32_element_index_from_pointer_offset(left)
        }
        _ => {
            if let (Some(pointer_index), Some(base_index)) = (
                int32_element_index_from_pointer_offset(&pointer.offset),
                int32_element_index_from_pointer_offset(&base.offset),
            ) {
                Some(bitvector_index_relative_to_base(pointer_index, base_index))
            } else {
                None
            }
        }
    }
}

fn pointer_offsets_equal_for_effect(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> bool {
    c_pointer_offsets_proven_equal_for_effect(left, right, assumptions)
}

pub(in crate::surface) fn int32_element_index_from_pointer_offset(
    offset: &PointerOffsetTerm,
) -> Option<Bitvector32Term> {
    match offset {
        PointerOffsetTerm::Constant(offset) if offset % 4 == 0 => {
            let index = offset / 4;
            (i32::MIN as i64..=i32::MAX as i64)
                .contains(&index)
                .then_some(Bitvector32Term::Constant((index as i32) as u32))
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width } if *byte_width == 4 => {
            Some(value.as_ref().clone())
        }
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &PointerOffsetTerm::Constant(0) => {
            int32_element_index_from_pointer_offset(right)
        }
        PointerOffsetTerm::Add(left, right)
            if right.as_ref() == &PointerOffsetTerm::Constant(0) =>
        {
            int32_element_index_from_pointer_offset(left)
        }
        PointerOffsetTerm::Add(left, right) => Some(bitvector32_add(
            int32_element_index_from_pointer_offset(left)?,
            int32_element_index_from_pointer_offset(right)?,
        )),
        _ => None,
    }
}
