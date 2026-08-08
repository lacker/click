use super::diagnostics::*;
use super::proof::FunctionClaimRef;
use super::*;

mod contract_evaluation;
mod effects;
mod predicates;
mod simp;
use crate::kernel::memory_effect_write_pointers;
pub(super) use contract_evaluation::*;
pub(super) use effects::*;
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
