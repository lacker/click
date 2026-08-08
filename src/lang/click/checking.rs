use super::diagnostics::*;
use super::proof::FunctionClaimRef;
use super::*;

mod contract_evaluation;
mod predicates;
mod simp;
use crate::kernel::memory_effect_write_pointers;
pub(super) use contract_evaluation::*;
pub(super) use predicates::*;
pub(super) use simp::*;

fn negate_lowered_proposition(proposition: Proposition) -> Proposition {
    match proposition {
        Proposition::ConditionIs(condition, value) => Proposition::ConditionIs(condition, !value),
        proposition => Proposition::Not(Box::new(proposition)),
    }
}

pub(super) fn check_function_claim(
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &[crate::kernel::ExecutionPureFact],
    available_pure_facts: &[Proposition],
    claim: &FunctionClaimRef<'_>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    unfolded_predicates: &[String],
) -> Result<(), ClickError> {
    if matches!(outcome, CFunctionOutcome::VerificationDiverges) {
        return Ok(());
    }
    match claim {
        FunctionClaimRef::Ensure(_, ensure_clause) => match ensure_clause.ensure() {
            Ensure::Proposition(proposition) => prove_ensure_proposition(
                claim_label,
                path_index,
                execution_pure_facts,
                available_pure_facts,
                proposition,
                parameters,
                arguments,
                pre_state,
                outcome,
                predicate_environment,
                click_function_environment,
                program_point_states,
                unfolded_predicates,
            )?,
            Ensure::Resource(resource) => prove_ensure_resource(
                claim_label,
                path_index,
                execution_pure_facts,
                available_pure_facts,
                resource,
                parameters,
                arguments,
                pre_state,
                outcome,
            )?,
        },
        FunctionClaimRef::Effect(_, effect_clause) => prove_effect_clause(
            claim_label,
            path_index,
            execution_pure_facts,
            available_pure_facts,
            effect_clause.effect(),
            parameters,
            arguments,
            pre_state,
            outcome,
        )?,
    }

    Ok(())
}

pub(super) fn check_function_claim_by_simp(
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &[crate::kernel::ExecutionPureFact],
    available_pure_facts: &[Proposition],
    claim: &FunctionClaimRef<'_>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    unfolded_predicates: &[String],
) -> Result<(), ClickError> {
    if matches!(outcome, CFunctionOutcome::VerificationDiverges) {
        return Ok(());
    }
    match claim {
        FunctionClaimRef::Ensure(_, ensure_clause) => match ensure_clause.ensure() {
            Ensure::Proposition(proposition) => prove_ensure_proposition_by_simp(
                claim_label,
                path_index,
                execution_pure_facts,
                available_pure_facts,
                proposition,
                parameters,
                arguments,
                pre_state,
                outcome,
                predicate_environment,
                click_function_environment,
                program_point_states,
                unfolded_predicates,
            ),
            Ensure::Resource(resource) => prove_ensure_resource(
                claim_label,
                path_index,
                execution_pure_facts,
                available_pure_facts,
                resource,
                parameters,
                arguments,
                pre_state,
                outcome,
            ),
        },
        FunctionClaimRef::Effect(_, _) => Err(ClickError::new(format!(
            "`simp` does not prove effect clauses for `{claim_label}`; use `by frame;` or `by auto;`"
        ))),
    }
}

pub(super) fn prove_ensure_resource(
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &[crate::kernel::ExecutionPureFact],
    available_pure_facts: &[Proposition],
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
) -> Result<(), ClickError> {
    if matches!(outcome, CFunctionOutcome::VerificationDiverges) {
        return Ok(());
    }
    let CFunctionOutcome::Return {
        value: result,
        state: post_state,
    } = outcome
    else {
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
    let expected = lower_resource_clause_at_state_with_result(
        resource, parameters, arguments, post_state, result,
    )?;
    let assumptions = assumptions_from_propositions(available_pure_facts);
    if post_state
        .resources()
        .satisfies_fact(&expected, &assumptions)
    {
        return Ok(());
    }
    Err(ClickError::new(format!(
        "`{claim_label}` failed on path {path_index}: {}",
        describe_missing_resource_fact(
            &expected,
            available_pure_facts,
            post_state.resources().facts(),
            parameters,
            arguments,
            execution_pure_facts
        )
    )))
}

pub(super) fn check_function_claim_with_existence_tactics(
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &[crate::kernel::ExecutionPureFact],
    available_pure_facts: &mut Vec<Proposition>,
    claim: &FunctionClaimRef<'_>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    proof_tactics: &[ProofTactic],
    original_requirements: &[Requirement],
    program_point_states: &ProgramPointStates,
    use_simp: bool,
) -> Result<(), ClickError> {
    if matches!(outcome, CFunctionOutcome::VerificationDiverges) {
        return Ok(());
    }
    let FunctionClaimRef::Ensure(_, ensure_clause) = claim else {
        return Err(ClickError::new(format!(
            "`witness` and `choose` tactics currently prove proposition `ensures` clauses for `{claim_label}`; use `frame` for effect clauses"
        )));
    };
    let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
        return Err(ClickError::new(format!(
            "`witness` and `choose` tactics currently prove proposition `ensures` clauses for `{claim_label}`; resource `ensures` are checked directly"
        )));
    };
    let CFunctionOutcome::Return {
        value: result,
        state: post_state,
    } = outcome
    else {
        return Err(ClickError::new(format!(
            "`witness`/`choose` failed for `{claim_label}` path {path_index}: {}\n{}",
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

    let mut values = parameter_values(parameters, arguments).map_err(|error| {
        ClickError::new(format!(
            "`witness`/`choose` failed for `{claim_label}` path {path_index}: {}",
            error.message
        ))
    })?;
    let array_refs = array_refs_for_parameters(parameters, &values, post_state.memory());
    let mut assumptions = assumptions_from_propositions(available_pure_facts);
    let mut next_lowering_variable = 2_000_000;
    let mut active_functions = BTreeSet::new();
    let mut goal = lower_outcome_proposition_with_environment(
        &mut values,
        &array_refs,
        pre_state,
        post_state,
        Some(result),
        &assumptions,
        surface_goal,
        &mut next_lowering_variable,
        predicate_environment,
        click_function_environment,
        program_point_states,
        &mut active_functions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`witness`/`choose` failed for `{claim_label}` path {path_index}: could not lower goal: {message}"
        ))
    })?;

    let mut next_choice_variable = 3_000_000;
    for (tactic_index, tactic) in proof_tactics.iter().enumerate() {
        match tactic {
            ProofTactic::Choose(choice) => {
                apply_choose_tactic(
                    choice,
                    claim_label,
                    path_index,
                    tactic_index,
                    available_pure_facts,
                    &mut values,
                    original_requirements,
                    &mut next_choice_variable,
                    predicate_environment,
                    click_function_environment,
                    unfolded_predicates,
                )?;
                *available_pure_facts = unfold_available_predicate_facts(
                    predicate_environment,
                    click_function_environment,
                    unfolded_predicates,
                    available_pure_facts,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`choose` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: {message}"
                    ))
                })?;
            }
            ProofTactic::Witness(witness) => {
                assumptions = assumptions_from_propositions(available_pure_facts);
                goal = unfold_predicates_in_proposition(
                    predicate_environment,
                    click_function_environment,
                    unfolded_predicates,
                    &goal,
                    &assumptions,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: {message}"
                    ))
                })?;
                let witness_value = evaluate_witness_tactic_value(
                    witness,
                    claim_label,
                    path_index,
                    tactic_index,
                    &values,
                    &array_refs,
                    pre_state,
                    post_state,
                    Some(result),
                    &assumptions,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                )?;
                goal = apply_witness_tactic(
                    witness,
                    witness_value,
                    goal,
                    claim_label,
                    path_index,
                    tactic_index,
                )?;
            }
            _ => {}
        }
    }

    assumptions = assumptions_from_propositions(available_pure_facts);
    goal = unfold_predicates_in_proposition(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        &goal,
        &assumptions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`witness`/`choose` failed for `{claim_label}` path {path_index}: {message}"
        ))
    })?;

    if use_simp {
        match simp_proposition(&goal, &assumptions) {
            SimpProposition::True => Ok(()),
            simplified => Err(ClickError::new(format!(
                "`witness`/`choose` failed for `{claim_label}` path {path_index}: simplified proposition was not true: {simplified:?}\n  {}",
                describe_missing_pure_fact(
                    &goal,
                    available_pure_facts,
                    post_state.resources().facts(),
                    parameters,
                    arguments,
                    execution_pure_facts
                )
            ))),
        }
    } else if assumptions.proves(&goal) {
        Ok(())
    } else {
        Err(ClickError::new(format!(
            "`witness`/`choose` failed for `{claim_label}` path {path_index}: {}",
            describe_missing_pure_fact(
                &goal,
                available_pure_facts,
                post_state.resources().facts(),
                parameters,
                arguments,
                execution_pure_facts
            )
        )))
    }
}

pub(super) fn apply_choose_tactic(
    choice: &ProofChoice,
    claim_label: &str,
    path_index: usize,
    tactic_index: usize,
    available_pure_facts: &mut Vec<Proposition>,
    values: &mut BTreeMap<String, CValue>,
    original_requirements: &[Requirement],
    next_choice_variable: &mut u64,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<(), ClickError> {
    if choice.name == "result" || values.contains_key(&choice.name) {
        return Err(ClickError::new(format!(
            "`choose` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: `{}` is already in scope",
            choice.name
        )));
    }

    let source_index = match &choice.source {
        ProofFactSource::Requirement(index) => {
            if *index >= original_requirements.len() {
                return Err(ClickError::new(format!(
                    "`choose` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: requirement {index} is out of range; function has {} requirement(s)",
                    original_requirements.len()
                )));
            }
            *index
        }
        ProofFactSource::RequirementLabel(label) => original_requirements
            .iter()
            .position(|requirement| requirement.label() == Some(label.as_str()))
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`choose` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: unknown requirement label `{label}`"
                ))
            })?,
    };
    let mut source = available_pure_facts
        .get(source_index)
        .cloned()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`choose` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: requirement {source_index} was not available"
            ))
        })?;
    if !matches!(source, Proposition::Exists { .. }) && !unfolded_predicates.is_empty() {
        let assumptions = assumptions_from_propositions(available_pure_facts);
        source = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            &source,
            &assumptions,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`choose` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: {message}"
            ))
        })?;
    }

    let Proposition::Exists {
        var, sort, body, ..
    } = source
    else {
        return Err(ClickError::new(format!(
            "`choose` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: source is not an existential proposition"
        )));
    };
    if sort != Sort::CInt32 {
        return Err(ClickError::new(format!(
            "`choose` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: only int32 existential choices are supported"
        )));
    }

    let chosen = Bitvector32Term::Variable(Variable(*next_choice_variable));
    *next_choice_variable += 1;
    values.insert(choice.name.clone(), CValue::Int32(chosen.clone()));
    available_pure_facts.push(substitute_int32_variable_in_proposition(&body, var, chosen));
    Ok(())
}

pub(super) fn evaluate_witness_tactic_value(
    witness: &ProofWitness,
    claim_label: &str,
    path_index: usize,
    tactic_index: usize,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
) -> Result<Bitvector32Term, ClickError> {
    let mut active_functions = BTreeSet::new();
    let value = evaluate_contract_expression_with_environment(
        values,
        array_refs,
        pre_state,
        post_state,
        result,
        assumptions,
        &witness.value,
        predicate_environment,
        click_function_environment,
        program_point_states,
        &mut active_functions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: could not evaluate witness value for `{}`: {message}",
            witness.name
        ))
    })?;
    let CValue::Int32(value) = value else {
        return Err(ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: witness `{}` did not evaluate to int32",
            witness.name
        )));
    };
    Ok(value)
}

pub(super) fn apply_witness_tactic(
    witness: &ProofWitness,
    witness_value: Bitvector32Term,
    goal: Proposition,
    claim_label: &str,
    path_index: usize,
    tactic_index: usize,
) -> Result<Proposition, ClickError> {
    let Proposition::Exists {
        name,
        var,
        sort,
        body,
    } = goal
    else {
        return Err(ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: goal is not an existential proposition"
        )));
    };
    if sort != Sort::CInt32 {
        return Err(ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: only int32 existential witnesses are supported"
        )));
    }
    if name != witness.name {
        return Err(ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: goal binds `{name}`, but proof provided witness `{}`",
            witness.name
        )));
    }

    Ok(substitute_int32_variable_in_proposition(
        &body,
        var,
        witness_value,
    ))
}

pub(super) fn prove_ensure_proposition_by_simp(
    ensure_label: &str,
    path_index: usize,
    execution_pure_facts: &[crate::kernel::ExecutionPureFact],
    available_pure_facts: &[Proposition],
    proposition: &ClickProposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    unfolded_predicates: &[String],
) -> Result<(), ClickError> {
    let surface_goal = proposition;
    let CFunctionOutcome::Return { state, .. } = outcome else {
        return Err(ClickError::new(format!(
            "`simp` failed for `{ensure_label}` path {path_index}: {}\n{}",
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
    let proposition = lower_ensure_proposition_goal(
        available_pure_facts,
        proposition,
        parameters,
        arguments,
        pre_state,
        outcome,
        predicate_environment,
        click_function_environment,
        program_point_states,
        unfolded_predicates,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`simp` failed for `{ensure_label}` path {path_index}: could not lower proposition: {message}\n{}",
            describe_proof_context(
                available_pure_facts,
                state.resources().facts(),
                parameters,
                arguments,
                execution_pure_facts
            )
        ))
    })?;
    if available_pure_facts.contains(&proposition) {
        return Ok(());
    }
    let mut reasoning_facts = available_pure_facts.to_vec();
    reasoning_facts.extend(
        execution_pure_facts
            .iter()
            .filter(|fact| {
                matches!(
                    fact.proposition(),
                    Proposition::CMemoryMutatesOnly { .. }
                        | Proposition::CMemoryEffectSummary { .. }
                        | Proposition::CHeapLifetimeRetired { .. }
                )
            })
            .map(|fact| fact.proposition().clone()),
    );
    let assumptions = assumptions_from_propositions(&reasoning_facts);
    match simp_proposition(&proposition, &assumptions) {
        SimpProposition::True => Ok(()),
        _ => Err(ClickError::new(format!(
            "`simp` failed for `{ensure_label}` path {path_index}: {}",
            describe_unclosed_surface_goal(
                surface_goal,
                available_pure_facts,
                state.resources().facts(),
                parameters,
                arguments,
                execution_pure_facts
            )
        ))),
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_ensure_proposition_goal(
    available_pure_facts: &[Proposition],
    proposition: &ClickProposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    unfolded_predicates: &[String],
) -> Result<Proposition, String> {
    let CFunctionOutcome::Return { value, state } = outcome else {
        return Err("the execution path does not return".to_string());
    };
    let proposition = lower_outcome_proposition_with_program_points(
        parameters,
        arguments,
        pre_state,
        state,
        value,
        available_pure_facts,
        proposition,
        predicate_environment,
        click_function_environment,
        program_point_states,
    );
    if crate::instrumentation::deadline_exceeded() {
        return Err(format!(
            "verification time limit exceeded inside {}",
            crate::instrumentation::deadline_context()
        ));
    }
    let proposition = proposition?;
    let assumptions = assumptions_from_propositions(available_pure_facts);
    unfold_predicates_in_proposition(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        &proposition,
        &assumptions,
    )
}

pub(super) fn prove_effect_clause(
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

pub(super) fn prove_effect_clause_exact(
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
            "verification time limit exceeded inside {}",
            crate::instrumentation::deadline_context()
        )))
    } else {
        Ok(())
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn plan_effect_clause_derivations(
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &[crate::kernel::ExecutionPureFact],
    available_pure_facts: &[Proposition],
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
                        | Proposition::CHeapLifetimeRetired { .. }
                )
            })
            .cloned()
            .map(ExecutionPureFact::new),
    );
    let mut reasoning_facts = available_pure_facts.to_vec();
    reasoning_facts.extend(effect_facts.iter().map(|fact| fact.proposition().clone()));
    let mut assumptions = None;
    let mut derivations = Vec::new();
    let mut writes = memory_effect_write_pointers(&effect_facts);
    writes.retain(|pointer| is_preexisting_effect_pointer(pointer, pre_state));

    for pointer in &writes {
        check_effect_planning_deadline()?;
        // Most concrete writes already sit at a constant offset inside a
        // declared mutable object. Match the exact replay rule first; building
        // a contextual assumptions index over a long execution history is
        // unnecessary in that overwhelmingly common case.
        if segments
            .iter()
            .any(|segment| segment_contains_pointer_exact(segment, pointer, available_pure_facts))
        {
            continue;
        }
        if let Some(selected) = segments.iter().find_map(|segment| {
            let goals =
                pointer_containment_goals_with_exact_base(segment, pointer, available_pure_facts)?;
            derive_goals_from_individual_facts(goals, available_pure_facts)
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
            goals
                .into_iter()
                .map(|goal| assumptions.derive_proposition(&goal))
                .collect::<Option<Vec<_>>>()
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
                    "`{claim_label}` failed on path {path_index}: contextual footprint proof did not produce replayable derivations"
                )))
            });
        };
        append_unique_derivations(&mut derivations, selected);
    }

    for range in effect_facts
        .iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::CMemoryEffectSummary { mutable_ranges, .. } => {
                Some(mutable_ranges.as_slice())
            }
            _ => None,
        })
        .flatten()
        .filter(|range| is_preexisting_effect_pointer(range.base(), pre_state))
    {
        check_effect_planning_deadline()?;
        if segments
            .iter()
            .any(|segment| segment_contains_range_exact(segment, range, available_pure_facts))
        {
            continue;
        }
        if let Some(selected) = segments.iter().find_map(|segment| {
            let goals =
                range_containment_goals_with_exact_base(segment, range, available_pure_facts)?;
            derive_goals_from_individual_facts(goals, available_pure_facts)
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
            goals
                .into_iter()
                .map(|goal| assumptions.derive_proposition(&goal))
                .collect::<Option<Vec<_>>>()
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
                    "`{claim_label}` failed on path {path_index}: contextual footprint proof did not produce replayable derivations"
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

pub(super) fn prove_ensure_proposition(
    ensure_label: &str,
    path_index: usize,
    execution_pure_facts: &[crate::kernel::ExecutionPureFact],
    available_pure_facts: &[Proposition],
    proposition: &ClickProposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    unfolded_predicates: &[String],
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let comparison = format!(
                "{} {operator} {}",
                describe_contract_expression(left),
                describe_contract_expression(right)
            );
            match outcome {
                CFunctionOutcome::Return { value, state } => {
                    let left_value = evaluate_contract_expression_with_program_points(
                        parameters,
                        arguments,
                        pre_state,
                        state,
                        value,
                        available_pure_facts,
                        left,
                        predicate_environment,
                        click_function_environment,
                        program_point_states,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`ensures {comparison}` failed for `{ensure_label}` path {path_index}: could not evaluate left side: {message}\n{}",
                            describe_proof_context(
                                available_pure_facts,
                                state.resources().facts(),
                                parameters,
                                arguments,
                                execution_pure_facts
                            )
                        ))
                    })?;
                    let right_value = evaluate_contract_expression_with_program_points(
                        parameters,
                        arguments,
                        pre_state,
                        state,
                        value,
                        available_pure_facts,
                        right,
                        predicate_environment,
                        click_function_environment,
                        program_point_states,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`ensures {comparison}` failed for `{ensure_label}` path {path_index}: could not evaluate right side: {message}\n{}",
                            describe_proof_context(
                                available_pure_facts,
                                state.resources().facts(),
                                parameters,
                                arguments,
                                execution_pure_facts
                            )
                        ))
                    })?;
                    prove_value_comparison(&left_value, *operator, &right_value, available_pure_facts)
                        .ok_or_else(|| {
                            let required = comparison_proposition(
                                left_value.clone(),
                                *operator,
                                right_value.clone(),
                            );
                            match required {
                                Ok(_) => ClickError::new(format!(
                                    "`ensures {comparison}` failed for `{ensure_label}` path {path_index}: left side evaluated to {}, right side evaluated to {}\n  {}",
                                    describe_c_value(&left_value, parameters, arguments),
                                    describe_c_value(&right_value, parameters, arguments),
                                    describe_unclosed_surface_goal(
                                        proposition,
                                        available_pure_facts,
                                        state.resources().facts(),
                                        parameters,
                                        arguments,
                                        execution_pure_facts
                                    )
                                )),
                                Err(message) => ClickError::new(format!(
                                    "`ensures {comparison}` failed for `{ensure_label}` path {path_index}: could not form comparison proof obligation: {}\n{}",
                                    message.message(),
                                    describe_proof_context(
                                        available_pure_facts,
                                        state.resources().facts(),
                                        parameters,
                                        arguments,
                                        execution_pure_facts
                                    )
                                )),
                            }
                        })?;
                }
                other => {
                    return Err(ClickError::new(format!(
                        "`ensures {comparison}` failed for `{ensure_label}` path {path_index}: {}\n{}",
                        describe_function_outcome(other, parameters, arguments),
                        describe_proof_context(
                            available_pure_facts,
                            pre_state.resources().facts(),
                            parameters,
                            arguments,
                            execution_pure_facts
                        )
                    )));
                }
            }
        }
        ClickProposition::And(left, right) => {
            prove_ensure_proposition(
                ensure_label,
                path_index,
                execution_pure_facts,
                available_pure_facts,
                left,
                parameters,
                arguments,
                pre_state,
                outcome,
                predicate_environment,
                click_function_environment,
                program_point_states,
                unfolded_predicates,
            )?;
            prove_ensure_proposition(
                ensure_label,
                path_index,
                execution_pure_facts,
                available_pure_facts,
                right,
                parameters,
                arguments,
                pre_state,
                outcome,
                predicate_environment,
                click_function_environment,
                program_point_states,
                unfolded_predicates,
            )?;
        }
        _ => {
            let surface_goal = proposition;
            let surface_proposition = describe_click_proposition(surface_goal);
            let CFunctionOutcome::Return { value, state } = outcome else {
                return Err(ClickError::new(format!(
                    "`ensures {surface_proposition}` failed for `{ensure_label}` path {path_index}: {}\n{}",
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
            let mut lowered_proposition = lower_outcome_proposition_with_program_points(
                parameters,
                arguments,
                pre_state,
                state,
                value,
                available_pure_facts,
                surface_goal,
                predicate_environment,
                click_function_environment,
                program_point_states,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`ensures {surface_proposition}` failed for `{ensure_label}` path {path_index}: could not lower proposition: {message}\n{}",
                    describe_proof_context(
                        available_pure_facts,
                        state.resources().facts(),
                        parameters,
                        arguments,
                        execution_pure_facts
                    )
                ))
            })?;
            let assumptions = assumptions_from_propositions(available_pure_facts);
            lowered_proposition = unfold_predicates_in_proposition(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                &lowered_proposition,
                &assumptions,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`ensures {surface_proposition}` failed for `{ensure_label}` path {path_index}: {message}"
                ))
            })?;
            if !assumptions.proves(&lowered_proposition) {
                return Err(ClickError::new(format!(
                    "`ensures {surface_proposition}` failed for `{ensure_label}` path {path_index}: {}",
                    describe_unclosed_surface_goal(
                        surface_goal,
                        available_pure_facts,
                        state.resources().facts(),
                        parameters,
                        arguments,
                        execution_pure_facts
                    )
                )));
            }
        }
    }
    Ok(())
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
                        | Proposition::CHeapLifetimeRetired { .. }
                )
            })
            .cloned()
            .map(ExecutionPureFact::new),
    );
    // Exact certificate replay uses only propositions named by the
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
            Proposition::CMemoryEffectSummary { mutable_ranges, .. } => {
                Some(mutable_ranges.as_slice())
            }
            _ => None,
        })
        .flatten()
        .filter(|range| is_preexisting_effect_pointer(range.base(), pre_state));

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
    fn contains(fact: &Proposition, required: &Proposition) -> bool {
        fact == required
            || matches!(fact, Proposition::And(left, right)
                if contains(left, required) || contains(right, required))
    }

    available.iter().any(|fact| contains(fact, required))
        || matches!(normalize_proposition(required), SimpProposition::True)
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
                Assumptions::new()
                    .assume_proposition(fact.clone())
                    .derive_proposition(&goal)
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
    exact_proposition_is_available_or_true(&pointer_offset_alignment_goal(left, right), available)
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
    assumptions: &Assumptions,
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

pub(super) fn is_effect_relevant_pointer(pointer: &Pointer) -> bool {
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
pub(super) struct EvaluatedContractSegment {
    pub(super) source: ContractSegment,
    pub(super) base: Pointer,
    pub(super) start: Bitvector32Term,
    pub(super) end: Bitvector32Term,
}

pub(super) fn evaluate_effect_segment(
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
    let evaluate = |assumptions: &Assumptions| {
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
        })
    };

    // Most effect clauses are direct entry-state places. Evaluate those
    // without indexing the proof's accumulated snapshot facts; fall back to
    // contextual equality reasoning only when the expression actually needs
    // it.
    evaluate(&Assumptions::new()).or_else(|_| {
        let assumptions = assumptions_from_propositions(available_pure_facts);
        evaluate(&assumptions)
    })
}

pub(super) fn evaluate_requirement_segment(
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
    let assumptions = Assumptions::new();
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
    })
}

pub(super) fn segment_contains_pointer(
    segment: &EvaluatedContractSegment,
    pointer: &Pointer,
    assumptions: &Assumptions,
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

pub(super) fn segment_contains_range(
    segment: &EvaluatedContractSegment,
    range: &CMemoryRange,
    assumptions: &Assumptions,
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

pub(super) fn pointer_element_index_from_base(
    pointer: &Pointer,
    base: &Pointer,
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
) -> bool {
    c_pointer_offsets_proven_equal_for_effect(left, right, assumptions)
}

pub(super) fn int32_element_index_from_pointer_offset(
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

pub(super) fn prove_value_comparison(
    actual: &CValue,
    operator: ComparisonOperator,
    expected: &CValue,
    available_pure_facts: &[Proposition],
) -> Option<()> {
    let proposition = comparison_proposition(actual.clone(), operator, expected.clone()).ok()?;
    let assumptions = available_pure_facts
        .iter()
        .cloned()
        .fold(Assumptions::new(), Assumptions::assume_proposition);
    assumptions.proves(&proposition).then_some(())
}

pub(super) fn comparison_condition(
    actual: Bitvector32Term,
    operator: ComparisonOperator,
    expected: Bitvector32Term,
) -> Option<(ConditionTerm, bool)> {
    match operator {
        ComparisonOperator::Equal => Some((bitvector32_equal(actual, expected), true)),
        ComparisonOperator::NotEqual => Some((bitvector32_equal(actual, expected), false)),
        ComparisonOperator::LessThan => Some((signed_less_than(actual, expected), true)),
        ComparisonOperator::LessEqual => Some((signed_less_equal(actual, expected), true)),
        ComparisonOperator::GreaterThan => Some((signed_greater_than(actual, expected), true)),
        ComparisonOperator::GreaterEqual => Some((signed_greater_equal(actual, expected), true)),
    }
}
