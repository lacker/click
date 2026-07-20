use super::diagnostics::*;
use super::proof::FunctionClaimRef;
use super::*;
use crate::kernel::memory_effect_write_pointers;

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
    let CFunctionOutcome::Return {
        state: post_state, ..
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
    let expected = lower_resource_clause(resource, parameters, arguments, pre_state.memory())?;
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
                )
            })
            .map(|fact| fact.proposition().clone()),
    );
    let assumptions = assumptions_from_propositions(&reasoning_facts);
    match simp_proposition(&proposition, &assumptions) {
        SimpProposition::True => Ok(()),
        simplified => Err(ClickError::new(format!(
            "`simp` failed for `{ensure_label}` path {path_index}: simplified proposition was not true: {simplified:?}\n  {}",
            describe_missing_pure_fact(
                &proposition,
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
    )?;
    let assumptions = assumptions_from_propositions(available_pure_facts);
    unfold_predicates_in_proposition(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        &proposition,
        &assumptions,
    )
}

pub(super) fn unfold_available_predicate_facts(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    available_pure_facts: &[Proposition],
) -> Result<Vec<Proposition>, String> {
    if unfolded_predicates.is_empty() {
        return Ok(available_pure_facts.to_vec());
    }

    let assumptions = assumptions_from_propositions(available_pure_facts);
    let mut propositions = available_pure_facts.to_vec();
    for proposition in available_pure_facts {
        let unfolded = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            proposition,
            &assumptions,
        )?;
        if &unfolded != proposition && !propositions.contains(&unfolded) {
            propositions.push(unfolded);
        }
    }
    Ok(propositions)
}

pub(super) fn unfold_predicates_in_proposition(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    proposition: &Proposition,
    assumptions: &Assumptions,
) -> Result<Proposition, String> {
    let mut active = BTreeSet::new();
    unfold_predicates_in_proposition_with_active(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        proposition,
        assumptions,
        &mut active,
    )
}

pub(super) fn unfold_predicates_in_proposition_with_active(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    proposition: &Proposition,
    assumptions: &Assumptions,
    active: &mut BTreeSet<String>,
) -> Result<Proposition, String> {
    match proposition {
        Proposition::Predicate { name, arguments }
            if unfolded_predicates
                .iter()
                .any(|predicate| predicate == name) =>
        {
            if !active.insert(name.clone()) {
                return Err(format!("recursive unfold of predicate `{name}`"));
            }
            let definition = predicate_environment
                .get(name)
                .ok_or_else(|| format!("unknown predicate `{name}`"))?;
            let unfolded = instantiate_predicate_definition(
                definition,
                arguments,
                assumptions,
                predicate_environment,
                click_function_environment,
            )?;
            let unfolded = unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                &unfolded,
                assumptions,
                active,
            )?;
            active.remove(name);
            Ok(unfolded)
        }
        Proposition::And(left, right) => Ok(Proposition::And(
            Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                left,
                assumptions,
                active,
            )?),
            Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                right,
                assumptions,
                active,
            )?),
        )),
        Proposition::Or(left, right) => Ok(Proposition::Or(
            Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                left,
                assumptions,
                active,
            )?),
            Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                right,
                assumptions,
                active,
            )?),
        )),
        Proposition::Not(body) => Ok(Proposition::Not(Box::new(
            unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                body,
                assumptions,
                active,
            )?,
        ))),
        Proposition::Implies(left, right) => {
            let left = unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                left,
                assumptions,
                active,
            )?;
            let right_assumptions = assumptions.clone().assume_proposition(left.clone());
            let right = unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                right,
                &right_assumptions,
                active,
            )?;
            Ok(Proposition::Implies(Box::new(left), Box::new(right)))
        }
        Proposition::ForAll { var, sort, body } => Ok(Proposition::ForAll {
            var: *var,
            sort: sort.clone(),
            body: Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                body,
                assumptions,
                active,
            )?),
        }),
        Proposition::Exists {
            name,
            var,
            sort,
            body,
        } => Ok(Proposition::Exists {
            name: name.clone(),
            var: *var,
            sort: sort.clone(),
            body: Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                body,
                assumptions,
                active,
            )?),
        }),
        _ => Ok(proposition.clone()),
    }
}

pub(super) fn instantiate_predicate_definition(
    definition: &PredicateDefinition,
    arguments: &[Term],
    assumptions: &Assumptions,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let (memory, mut values, array_refs) = decode_predicate_arguments(definition, arguments)?;

    let mut next_variable = 2_500_000;
    let mut active_functions = BTreeSet::new();
    let program_point_states = ProgramPointStates::new();
    lower_predicate_body_proposition_with_environment(
        &mut values,
        &array_refs,
        &memory,
        assumptions,
        definition.body(),
        &mut next_variable,
        predicate_environment,
        click_function_environment,
        &program_point_states,
        &mut active_functions,
    )
}

pub(super) fn decode_predicate_arguments(
    definition: &PredicateDefinition,
    arguments: &[Term],
) -> Result<(CMemory, BTreeMap<String, CValue>, ClickArrayRefs), String> {
    let expanded_len = definition
        .parameters()
        .iter()
        .map(|parameter| {
            if parameter_is_click_array_ref(parameter) {
                2
            } else {
                1
            }
        })
        .sum::<usize>();

    if arguments.len() == expanded_len {
        let mut values = BTreeMap::new();
        let mut array_refs = BTreeMap::new();
        let mut default_memory = None;
        let mut index = 0;
        for parameter in definition.parameters() {
            if parameter_is_click_array_ref(parameter) {
                let Some(Term::CMemory(memory)) = arguments.get(index) else {
                    return Err(format!(
                        "predicate `{}` argument `{}` is missing its array-ref memory",
                        definition.name(),
                        parameter.name()
                    ));
                };
                let Some(Term::CValue(CValue::Pointer(pointer))) = arguments.get(index + 1) else {
                    return Err(format!(
                        "predicate `{}` argument `{}` is missing its array-ref pointer",
                        definition.name(),
                        parameter.name()
                    ));
                };
                default_memory.get_or_insert_with(|| memory.clone());
                values.insert(
                    parameter.name().to_string(),
                    CValue::Pointer(pointer.clone()),
                );
                array_refs.insert(
                    parameter.name().to_string(),
                    ClickArrayRef {
                        memory: memory.clone(),
                        pointer: pointer.clone(),
                        element_type: click_array_element_type(parameter.c_type()).ok_or_else(
                            || {
                                format!(
                                    "predicate `{}` argument `{}` is not an array-ref parameter",
                                    definition.name(),
                                    parameter.name()
                                )
                            },
                        )?,
                    },
                );
                index += 2;
            } else {
                let Some(Term::CValue(value)) = arguments.get(index) else {
                    return Err(format!(
                        "predicate `{}` argument `{}` did not lower to a C value",
                        definition.name(),
                        parameter.name()
                    ));
                };
                values.insert(parameter.name().to_string(), value.clone());
                index += 1;
            }
        }
        return Ok((default_memory.unwrap_or_default(), values, array_refs));
    }

    Err(format!(
        "predicate `{}` has malformed lowered argument count: expected {} expanded argument term(s), got {}",
        definition.name(),
        expanded_len,
        arguments.len()
    ))
}

pub(super) fn lower_predicate_body_proposition_with_environment(
    values: &mut BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    assumptions: &Assumptions,
    proposition: &ClickProposition,
    next_variable: &mut u64,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<Proposition, String> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            comparison_proposition(left, *operator, right).map_err(|error| error.message)
        }
        ClickProposition::Separate { left, right } => {
            let left = evaluate_predicate_resource_subject(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_resource_subject(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            Ok(Proposition::CResourceSeparate { left, right })
        }
        ClickProposition::Contains { parent, child } => {
            let parent = evaluate_predicate_resource_subject(
                values,
                array_refs,
                memory,
                assumptions,
                parent,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let child = evaluate_predicate_resource_subject(
                values,
                array_refs,
                memory,
                assumptions,
                child,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            Ok(Proposition::CResourceContains { parent, child })
        }
        ClickProposition::Loadable { segment } => {
            let segment = evaluate_predicate_contract_segment(
                values,
                array_refs,
                memory,
                assumptions,
                segment,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let element_width =
                contract_segment_element_width_from_array_refs(array_refs, &segment.source)
                    .unwrap_or(4);
            loadable_segment_prop(memory, segment, element_width).map_err(|error| error.message)
        }
        ClickProposition::Defined { expression } => {
            let expression = contract_expression_to_c_fragment(expression).ok_or_else(|| {
                "`defined(...)` currently requires an expression without `old`, `at`, folds, lets, or Click function calls".to_string()
            })?;
            let state = values.iter().fold(
                CState::new().with_memory(memory.clone()),
                |state, (name, value)| state.with_local(name.clone(), value.clone()),
            );
            c_expression_definedness_proposition(&state, &expression).map_err(|limit| {
                format!("`defined(...)` elaboration hit execution limit {limit:?}")
            })
        }
        ClickProposition::And(left, right) => Ok(Proposition::And(
            Box::new(lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?),
            Box::new(lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?),
        )),
        ClickProposition::Or(left, right) => Ok(Proposition::Or(
            Box::new(lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?),
            Box::new(lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?),
        )),
        ClickProposition::Not(body) => Ok(Proposition::Not(Box::new(
            lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?,
        ))),
        ClickProposition::Implies(left, right) => {
            let left = lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right_assumptions = assumptions.clone().assume_proposition(left.clone());
            let right = lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                &right_assumptions,
                right,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            Ok(Proposition::Implies(Box::new(left), Box::new(right)))
        }
        ClickProposition::ForAll { c_type, name, body } => {
            if *c_type != C0Type::Int32 {
                return Err("only `forall (int32 ...)` is supported".to_string());
            }
            let variable = Variable(*next_variable);
            *next_variable += 1;
            let previous = values.insert(
                name.clone(),
                CValue::Int32(Bitvector32Term::Variable(variable)),
            );
            let body = lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            match previous {
                Some(value) => {
                    values.insert(name.clone(), value);
                }
                None => {
                    values.remove(name);
                }
            }
            Ok(Proposition::ForAll {
                var: variable,
                sort: Sort::CInt32,
                body: Box::new(body),
            })
        }
        ClickProposition::Exists { c_type, name, body } => {
            if *c_type != C0Type::Int32 {
                return Err("only `exists (int32 ...)` is supported".to_string());
            }
            let variable = Variable(*next_variable);
            *next_variable += 1;
            let previous = values.insert(
                name.clone(),
                CValue::Int32(Bitvector32Term::Variable(variable)),
            );
            let body = lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            match previous {
                Some(value) => {
                    values.insert(name.clone(), value);
                }
                None => {
                    values.remove(name);
                }
            }
            Ok(Proposition::Exists {
                name: name.clone(),
                var: variable,
                sort: Sort::CInt32,
                body: Box::new(body),
            })
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => {
            let start = int32_term_value(
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    start,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?,
                "range `all` start bound",
            )?;
            let end = int32_term_value(
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    end,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?,
                "range `all` end bound",
            )?;
            let variable = Variable(*next_variable);
            *next_variable += 1;
            let item_bits = Bitvector32Term::Variable(variable);
            let item_value = CValue::Int32(item_bits.clone());
            let outer_values = values.clone();
            values.insert(item.clone(), item_value.clone());
            let body_assumptions =
                assumptions
                    .clone()
                    .assume_proposition(range_membership_proposition(
                        start.clone(),
                        item_bits.clone(),
                        end.clone(),
                    ));
            let body = match lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                &body_assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            ) {
                Ok(body) => body,
                Err(error) => {
                    *values = outer_values;
                    return Err(error);
                }
            };
            *values = outer_values;
            Ok(bounded_forall_int32(variable, start, item_bits, end, body))
        }
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            let start = int32_term_value(
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    start,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?,
                "range `any` start bound",
            )?;
            let end = int32_term_value(
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    end,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?,
                "range `any` end bound",
            )?;
            let outer_values = values.clone();
            match (
                concrete_bound_from_term(&start, "any", "start"),
                concrete_bound_from_term(&end, "any", "end"),
            ) {
                (Ok(start), Ok(end)) => {
                    let mut proposition = false_proposition();
                    for index in concrete_fold_range(start, end)? {
                        *values = outer_values.clone();
                        values.insert(
                            item.clone(),
                            CValue::Int32(Bitvector32Term::Constant(index as u32)),
                        );
                        let body = match lower_predicate_body_proposition_with_environment(
                            values,
                            array_refs,
                            memory,
                            assumptions,
                            body,
                            next_variable,
                            predicate_environment,
                            click_function_environment,
                            program_point_states,
                            active_functions,
                        ) {
                            Ok(body) => body,
                            Err(error) => {
                                *values = outer_values;
                                return Err(error);
                            }
                        };
                        proposition = disjunction(proposition, body);
                    }
                    *values = outer_values;
                    Ok(proposition)
                }
                _ => {
                    let variable = Variable(*next_variable);
                    *next_variable += 1;
                    let item_bits = Bitvector32Term::Variable(variable);
                    let item_value = CValue::Int32(item_bits.clone());
                    values.insert(item.clone(), item_value.clone());
                    let body_assumptions =
                        assumptions
                            .clone()
                            .assume_proposition(range_membership_proposition(
                                start.clone(),
                                item_bits.clone(),
                                end.clone(),
                            ));
                    let body = match lower_predicate_body_proposition_with_environment(
                        values,
                        array_refs,
                        memory,
                        &body_assumptions,
                        body,
                        next_variable,
                        predicate_environment,
                        click_function_environment,
                        program_point_states,
                        active_functions,
                    ) {
                        Ok(body) => body,
                        Err(error) => {
                            *values = outer_values;
                            return Err(error);
                        }
                    };
                    *values = outer_values;
                    Ok(bounded_exists_int32(
                        item.clone(),
                        variable,
                        start,
                        item_bits,
                        end,
                        body,
                    ))
                }
            }
        }
        ClickProposition::PredicateCall { name, arguments } => {
            let definition = predicate_environment
                .get(name)
                .ok_or_else(|| format!("unknown predicate `{name}`"))?;
            let state = CState::new().with_memory(memory.clone());
            let lowered_arguments = lower_predicate_call_arguments_with_environment(
                definition,
                arguments,
                values,
                array_refs,
                &state,
                &state,
                None,
                assumptions,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            Ok(Proposition::Predicate {
                name: name.clone(),
                arguments: lowered_arguments,
            })
        }
    }
}

fn evaluate_predicate_contract_segment(
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    assumptions: &Assumptions,
    segment: &ContractSegment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<EvaluatedContractSegment, String> {
    if segment.state != ContractSegmentState::Current {
        return Err("`old(...)` is not available in memory resource subjects".to_string());
    }
    let base = evaluate_predicate_contract_expression(
        values,
        array_refs,
        memory,
        assumptions,
        &ContractExpression::CFragment(segment.base.clone()),
        predicate_environment,
        click_function_environment,
        program_point_states,
        active_functions,
    )?;
    let CValue::Pointer(base) = base else {
        return Err("segment base did not evaluate to a pointer".to_string());
    };
    let start = evaluate_predicate_contract_expression(
        values,
        array_refs,
        memory,
        assumptions,
        &ContractExpression::CFragment(segment.start.clone()),
        predicate_environment,
        click_function_environment,
        program_point_states,
        active_functions,
    )?;
    let CValue::Int32(start) = start else {
        return Err("segment start did not evaluate to int32".to_string());
    };
    let end = evaluate_predicate_contract_expression(
        values,
        array_refs,
        memory,
        assumptions,
        &ContractExpression::CFragment(segment.end.clone()),
        predicate_environment,
        click_function_environment,
        program_point_states,
        active_functions,
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

fn evaluate_predicate_resource_subject(
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    assumptions: &Assumptions,
    resource: &ResourceSubject,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<CResource, String> {
    match resource {
        ResourceSubject::Memory(segment) => {
            let segment = evaluate_predicate_contract_segment(
                values,
                array_refs,
                memory,
                assumptions,
                segment,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            Ok(CResource::Memory(CMemoryRange::new(
                segment.base,
                segment.start,
                segment.end,
            )))
        }
        ResourceSubject::Declared {
            kind,
            name,
            arguments,
            parameter_types,
        } => {
            if arguments.len() != parameter_types.len() {
                return Err(format!(
                    "resource `{name}` has malformed argument type metadata"
                ));
            }
            let mut values_out = Vec::new();
            for (index, (argument, parameter_type)) in
                arguments.iter().zip(parameter_types).enumerate()
            {
                let value = evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    argument,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?;
                if !c_value_matches_click_type(&value, *parameter_type) {
                    return Err(format!(
                        "resource `{name}` argument {index} evaluated to {value:?}, which does not match {:?}",
                        parameter_type
                    ));
                }
                values_out.push(value);
            }
            Ok(match kind {
                ResourceKind::Composite => CResource::Composite {
                    name: name.clone(),
                    arguments: values_out,
                },
                ResourceKind::Token => CResource::Token {
                    name: name.clone(),
                    arguments: values_out,
                },
            })
        }
    }
}

pub(super) fn evaluate_predicate_contract_expression(
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    assumptions: &Assumptions,
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<CValue, String> {
    let state = CState::new().with_memory(memory.clone());
    match expression {
        ContractExpression::CFragment(expression) => {
            evaluate_c_contract_expression(values, &state, None, assumptions, expression)
        }
        ContractExpression::Old(_) => {
            Err("`old(...)` is not available in predicate definitions".to_string())
        }
        ContractExpression::At { .. } => {
            Err("`at(...)` is not available in predicate definitions".to_string())
        }
        ContractExpression::Add(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_add(left, right)
        }
        ContractExpression::Subtract(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_sub(left, right)
        }
        ContractExpression::Multiply(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_multiply(left, right)
        }
        ContractExpression::Divide(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_divide(left, right)
        }
        ContractExpression::Remainder(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_remainder(left, right)
        }
        ContractExpression::ShiftLeft(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_shift_left(left, right)
        }
        ContractExpression::ShiftRight(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_shift_right(left, right)
        }
        ContractExpression::BitwiseAnd(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "&", bitvector32_and)
        }
        ContractExpression::BitwiseOr(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "|", bitvector32_or)
        }
        ContractExpression::BitwiseXor(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "^", bitvector32_xor)
        }
        ContractExpression::BitwiseNot(expression) => {
            let value = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_not(value)
        }
        ContractExpression::Index(base, index) => {
            if contains_old_expression(base) {
                return Err("`old(...)` is not available in predicate definitions".to_string());
            }
            if contains_at_expression(base) {
                return Err("`at(...)` is not available in predicate definitions".to_string());
            }
            let array_ref = evaluate_contract_array_ref_with_environment(
                values,
                array_refs,
                &state,
                &state,
                None,
                assumptions,
                base,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let index = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                index,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let CValue::Int32(index) = index else {
                return Err(format!(
                    "array index did not evaluate to int32: `{index:?}`"
                ));
            };
            let element_type = array_ref.element_type;
            let pointer =
                offset_pointer_by_elements(array_ref.pointer, index, element_type.byte_width());
            evaluate_contract_memory_load_from_memory(
                &array_ref.memory,
                pointer,
                element_type,
                assumptions,
            )
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut condition_values = values.clone();
            let mut next_variable = 2_500_000;
            let condition = lower_predicate_body_proposition_with_environment(
                &mut condition_values,
                array_refs,
                memory,
                assumptions,
                condition,
                &mut next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            if assumptions.proves(&condition) {
                return evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    then_branch,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                );
            }
            if assumptions_prove_proposition_false(assumptions, &condition) {
                return evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    else_branch,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                );
            }

            let then_value = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                then_branch,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let else_value = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                else_branch,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            conditional_contract_value(&condition, then_value, else_value)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let start = int32_term_value(
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    start,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?,
                "fold start",
            )?;
            let end = int32_term_value(
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    end,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?,
                "fold end",
            )?;
            let mut value = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                initial,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            match (
                concrete_bound_from_term(&start, "fold", "start"),
                concrete_bound_from_term(&end, "fold", "end"),
            ) {
                (Ok(start), Ok(end)) => {
                    for index in concrete_fold_range(start, end)? {
                        let mut fold_values = values.clone();
                        fold_values.insert(accumulator.clone(), value);
                        fold_values.insert(
                            item.clone(),
                            CValue::Int32(Bitvector32Term::Constant(index as u32)),
                        );
                        value = evaluate_predicate_contract_expression(
                            &fold_values,
                            array_refs,
                            memory,
                            assumptions,
                            body,
                            predicate_environment,
                            click_function_environment,
                            program_point_states,
                            active_functions,
                        )?;
                    }
                    Ok(value)
                }
                _ => {
                    let mut fold_values = values.clone();
                    fold_values.insert(
                        accumulator.clone(),
                        CValue::Int32(Bitvector32Term::Variable(fold_bound_variable(
                            accumulator,
                            0,
                        ))),
                    );
                    fold_values.insert(
                        item.clone(),
                        CValue::Int32(Bitvector32Term::Variable(fold_bound_variable(item, 1))),
                    );
                    let body_value = evaluate_predicate_contract_expression(
                        &fold_values,
                        array_refs,
                        memory,
                        assumptions,
                        body,
                        predicate_environment,
                        click_function_environment,
                        program_point_states,
                        active_functions,
                    )?;
                    symbolic_range_fold_value(start, end, value, accumulator, item, body_value)
                }
            }
        }
        ContractExpression::Let {
            name,
            c_type,
            value,
            body,
        } => {
            let value = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                value,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let value = checked_contract_let_value(value, *c_type, name)?;
            let mut let_values = values.clone();
            let_values.insert(name.clone(), value);
            evaluate_predicate_contract_expression(
                &let_values,
                array_refs,
                memory,
                assumptions,
                body,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )
        }
        ContractExpression::Call { name, arguments } => evaluate_click_function_call(
            click_function_environment,
            name,
            arguments,
            values,
            array_refs,
            &state,
            &state,
            None,
            assumptions,
            predicate_environment,
            program_point_states,
            active_functions,
        ),
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum SimpProposition {
    True,
    False,
    Proposition(Proposition),
}

pub(super) fn normalize_proposition(proposition: &Proposition) -> SimpProposition {
    match proposition {
        Proposition::Equal(left, right) => match simp_terms_equal(left, right) {
            Some(true) => SimpProposition::True,
            Some(false) => SimpProposition::False,
            None => {
                SimpProposition::Proposition(Proposition::Equal(simp_term(left), simp_term(right)))
            }
        },
        Proposition::ConditionIs(condition, expected) => {
            match simp_condition_without_assumptions(condition) {
                Some(actual) if actual == *expected => SimpProposition::True,
                Some(_) => SimpProposition::False,
                None => SimpProposition::Proposition(proposition.clone()),
            }
        }
        Proposition::And(left, right) => {
            let left = normalize_proposition(left);
            let right = normalize_proposition(right);
            match (left, right) {
                (SimpProposition::False, _) | (_, SimpProposition::False) => SimpProposition::False,
                (SimpProposition::True, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::True, right) => right,
                (left, SimpProposition::True) => left,
                (left, right) => SimpProposition::Proposition(Proposition::And(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Or(left, right) => {
            let left = normalize_proposition(left);
            let right = normalize_proposition(right);
            match (left, right) {
                (SimpProposition::True, _) | (_, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::False, SimpProposition::False) => SimpProposition::False,
                (SimpProposition::False, right) => right,
                (left, SimpProposition::False) => left,
                (left, right) => SimpProposition::Proposition(Proposition::Or(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Not(body) => match normalize_proposition(body) {
            SimpProposition::True => SimpProposition::False,
            SimpProposition::False => SimpProposition::True,
            body => {
                SimpProposition::Proposition(Proposition::Not(Box::new(body.into_proposition())))
            }
        },
        Proposition::Implies(left, right) => {
            let left = normalize_proposition(left);
            let right = normalize_proposition(right);
            match (left, right) {
                (SimpProposition::False, _) | (_, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::True, right) => right,
                (_, SimpProposition::False) => SimpProposition::False,
                (left, right) => SimpProposition::Proposition(Proposition::Implies(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        _ => SimpProposition::Proposition(proposition.clone()),
    }
}

pub(super) fn rewrite_proposition_by_exact_equality(
    goal: &Proposition,
    equality: &Proposition,
    available: &[Proposition],
) -> Result<Proposition, String> {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = equality
    else {
        return Err("`rewrite` currently expects an int32 equality".to_string());
    };
    let reverse = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(right.as_ref().clone()),
            Box::new(left.as_ref().clone()),
        ),
        true,
    );
    if !available.contains(equality) && !available.contains(&reverse) {
        return Err(format!(
            "`rewrite` requires an exact available equality, missing {equality:?}"
        ));
    }
    let Bitvector32Term::Variable(variable) = left.as_ref() else {
        return Err(
            "`rewrite` currently requires the equality's left side to be an int32 variable"
                .to_string(),
        );
    };
    let rewritten =
        substitute_int32_variable_in_proposition(goal, *variable, right.as_ref().clone());
    if &rewritten == goal {
        return Err("`rewrite` equality does not occur in the current goal".to_string());
    }
    Ok(rewritten)
}

pub(super) fn normalize_direct_atomic_memory_loads(proposition: &Proposition) -> Proposition {
    let Proposition::ConditionIs(condition, value) = proposition else {
        return proposition.clone();
    };
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        (
            normalize_direct_atomic_memory_load(left),
            normalize_direct_atomic_memory_load(right),
        )
    };
    let condition = match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedLessThan(Box::new(left), Box::new(right))
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedLessEqual(Box::new(left), Box::new(right))
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedGreaterThan(Box::new(left), Box::new(right))
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedGreaterEqual(Box::new(left), Box::new(right))
        }
        ConditionTerm::Bitvector32Equal(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right))
        }
        _ => return proposition.clone(),
    };
    Proposition::ConditionIs(condition, *value)
}

fn normalize_direct_atomic_memory_load(term: &Bitvector32Term) -> Bitvector32Term {
    let Bitvector32Term::MemoryLoad(memory, pointer) = term else {
        return term.clone();
    };
    match memory.load(pointer) {
        CExpressionOutcome::Value(CValue::Int32(value) | CValue::UInt8(value))
            if &value != term =>
        {
            value
        }
        _ => term.clone(),
    }
}

pub(super) fn plan_simp_certificate(
    proposition: &Proposition,
    assumptions: &Assumptions,
) -> Option<ProofReplayPlan> {
    let tactic = if matches!(normalize_proposition(proposition), SimpProposition::True) {
        ProofTactic::Normalize
    } else {
        ProofTactic::ExactPropositionDerivation(assumptions.derive_simp_proposition(proposition)?)
    };
    ProofReplayPlan::from_planned_tactics(&[tactic]).ok()
}

pub(super) fn replay_simp_certificate(
    proposition: &Proposition,
    assumptions: &Assumptions,
    certificate: &ProofReplayPlan,
) -> bool {
    match certificate.tactics() {
        [ProofTactic::Normalize] => {
            matches!(normalize_proposition(proposition), SimpProposition::True)
        }
        [ProofTactic::ExactPropositionDerivation(derivation)] => {
            derivation.conclusion() == proposition && derivation.replay(assumptions)
        }
        _ => false,
    }
}

pub(super) fn simp_proposition(
    proposition: &Proposition,
    assumptions: &Assumptions,
) -> SimpProposition {
    if let Some(certificate) = plan_simp_certificate(proposition, assumptions)
        && replay_simp_certificate(proposition, assumptions, &certificate)
    {
        return SimpProposition::True;
    }
    let simplified = match proposition {
        Proposition::Equal(left, right) => match simp_terms_equal(left, right) {
            Some(true) => SimpProposition::True,
            Some(false) => SimpProposition::False,
            None => {
                SimpProposition::Proposition(Proposition::Equal(simp_term(left), simp_term(right)))
            }
        },
        Proposition::ConditionIs(condition, expected) => {
            match simp_condition(condition, assumptions) {
                Some(actual) if actual == *expected => SimpProposition::True,
                Some(_) => SimpProposition::False,
                None => SimpProposition::Proposition(proposition.clone()),
            }
        }
        Proposition::And(left, right) => {
            let left = simp_proposition(left, assumptions);
            let right = simp_proposition(right, assumptions);
            match (left, right) {
                (SimpProposition::False, _) | (_, SimpProposition::False) => SimpProposition::False,
                (SimpProposition::True, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::True, right) => right,
                (left, SimpProposition::True) => left,
                (left, right) => SimpProposition::Proposition(Proposition::And(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Or(left, right) => {
            let left = simp_proposition(left, assumptions);
            let right = simp_proposition(right, assumptions);
            match (left, right) {
                (SimpProposition::True, _) | (_, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::False, SimpProposition::False) => SimpProposition::False,
                (SimpProposition::False, right) => right,
                (left, SimpProposition::False) => left,
                (left, right) => SimpProposition::Proposition(Proposition::Or(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Not(body) => match simp_proposition(body, assumptions) {
            SimpProposition::True => SimpProposition::False,
            SimpProposition::False => SimpProposition::True,
            body => {
                SimpProposition::Proposition(Proposition::Not(Box::new(body.into_proposition())))
            }
        },
        Proposition::Implies(left, right) => {
            let left = simp_proposition(left, assumptions);
            let right = simp_proposition(right, assumptions);
            match (left, right) {
                (SimpProposition::False, _) | (_, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::True, right) => right,
                (_, SimpProposition::False) => SimpProposition::False,
                (left, right) => SimpProposition::Proposition(Proposition::Implies(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::ForAll { .. }
        | Proposition::Exists { .. }
        | Proposition::Predicate { .. }
        | Proposition::CExpressionEvaluates { .. }
        | Proposition::CConditionEvaluates { .. }
        | Proposition::CStatementExecutes { .. }
        | Proposition::CFunctionExecutes { .. }
        | Proposition::CFunctionSatisfiesSpecification { .. }
        | Proposition::CMemoryLoads { .. }
        | Proposition::CMemoryLoadable { .. }
        | Proposition::CMemoryCanStore { .. }
        | Proposition::CMemoryDisjoint { .. }
        | Proposition::CResourceSeparate { .. }
        | Proposition::CResourceContains { .. }
        | Proposition::CMemoryMutatesOnly { .. }
        | Proposition::CMemoryEffectSummary { .. }
        | Proposition::CWhileInvariantRule { .. } => {
            SimpProposition::Proposition(proposition.clone())
        }
    };
    if matches!(simplified, SimpProposition::True) {
        // A successful smart tactic must come from the certificate path above.
        SimpProposition::Proposition(proposition.clone())
    } else {
        simplified
    }
}

impl SimpProposition {
    fn into_proposition(self) -> Proposition {
        match self {
            Self::True => Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            Self::False => Proposition::ConditionIs(ConditionTerm::Constant(false), true),
            Self::Proposition(proposition) => proposition,
        }
    }
}

pub(super) fn simp_terms_equal(left: &Term, right: &Term) -> Option<bool> {
    let left = simp_term(left);
    let right = simp_term(right);
    if left == right {
        return Some(true);
    }
    match (&left, &right) {
        (Term::Bitvector32(left), Term::Bitvector32(right)) => Some(
            simp_bitvector_const(&simp_bitvector(left))?
                == simp_bitvector_const(&simp_bitvector(right))?,
        ),
        (Term::Condition(left), Term::Condition(right)) => Some(
            simp_condition_without_assumptions(left)? == simp_condition_without_assumptions(right)?,
        ),
        _ => None,
    }
}

pub(super) fn simp_term(term: &Term) -> Term {
    match term {
        Term::Condition(condition) => match simp_condition_without_assumptions(condition) {
            Some(value) => Term::Condition(ConditionTerm::Constant(value)),
            None => term.clone(),
        },
        Term::Bitvector32(term) => Term::Bitvector32(simp_bitvector(term)),
        Term::CValue(CValue::Int32(term)) => Term::CValue(CValue::Int32(simp_bitvector(term))),
        _ => term.clone(),
    }
}

pub(super) fn simp_condition(condition: &ConditionTerm, assumptions: &Assumptions) -> Option<bool> {
    simp_condition_without_assumptions(condition)
        .or_else(|| assumptions.decide_condition_for_simp(condition))
}

pub(super) fn simp_condition_without_assumptions(condition: &ConditionTerm) -> Option<bool> {
    match condition {
        ConditionTerm::Constant(value) => Some(*value),
        ConditionTerm::Bitvector32Equal(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(true)
            } else {
                Some(simp_bitvector_const(&left)? == simp_bitvector_const(&right)?)
            }
        }
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(false)
            } else {
                Some((simp_bitvector_const(&left)? as i32) < (simp_bitvector_const(&right)? as i32))
            }
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(true)
            } else {
                Some(
                    (simp_bitvector_const(&left)? as i32) <= (simp_bitvector_const(&right)? as i32),
                )
            }
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(false)
            } else {
                Some((simp_bitvector_const(&left)? as i32) > (simp_bitvector_const(&right)? as i32))
            }
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(true)
            } else {
                Some(
                    (simp_bitvector_const(&left)? as i32) >= (simp_bitvector_const(&right)? as i32),
                )
            }
        }
        ConditionTerm::Variable(_)
        | ConditionTerm::Bitvector32SignedAddOverflows(_, _)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(_, _)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(_, _)
        | ConditionTerm::Bitvector32SignedDivideOverflows(_, _)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(_, _)
        | ConditionTerm::PointerOffsetEqual(_, _)
        | ConditionTerm::PointerEqual(_, _) => None,
    }
}

pub(super) fn simp_bitvector_const(term: &Bitvector32Term) -> Option<u32> {
    match term {
        Bitvector32Term::Constant(value) => Some(*value),
        Bitvector32Term::Variable(_)
        | Bitvector32Term::RangeFold { .. }
        | Bitvector32Term::MemoryLoad(_, _) => None,
        Bitvector32Term::Add(left, right) => {
            Some(simp_bitvector_const(left)?.wrapping_add(simp_bitvector_const(right)?))
        }
        Bitvector32Term::Subtract(left, right) => {
            Some(simp_bitvector_const(left)?.wrapping_sub(simp_bitvector_const(right)?))
        }
        Bitvector32Term::Multiply(left, right) => {
            Some(simp_bitvector_const(left)?.wrapping_mul(simp_bitvector_const(right)?))
        }
        Bitvector32Term::Divide(left, right) => {
            let left = simp_bitvector_const(left)? as i32;
            let right = simp_bitvector_const(right)? as i32;
            if right == 0 || (left == i32::MIN && right == -1) {
                None
            } else {
                Some((left / right) as u32)
            }
        }
        Bitvector32Term::Remainder(left, right) => {
            let left = simp_bitvector_const(left)? as i32;
            let right = simp_bitvector_const(right)? as i32;
            if right == 0 || (left == i32::MIN && right == -1) {
                None
            } else {
                Some((left % right) as u32)
            }
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let left = simp_bitvector_const(left)? as i32;
            let right = bitvector32_shift_count(simp_bitvector_const(right)?)?;
            if left < 0 {
                None
            } else {
                let shifted = (left as i64) << right;
                (shifted <= i64::from(i32::MAX)).then_some((shifted as i32) as u32)
            }
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let left = simp_bitvector_const(left)? as i32;
            let right = bitvector32_shift_count(simp_bitvector_const(right)?)?;
            Some((left >> right) as u32)
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            Some(simp_bitvector_const(left)? & simp_bitvector_const(right)?)
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            Some(simp_bitvector_const(left)? | simp_bitvector_const(right)?)
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            Some(simp_bitvector_const(left)? ^ simp_bitvector_const(right)?)
        }
        Bitvector32Term::BitwiseNot(value) => Some(!simp_bitvector_const(value)?),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => match simp_condition_without_assumptions(condition)? {
            true => simp_bitvector_const(then_term),
            false => simp_bitvector_const(else_term),
        },
    }
}

pub(super) fn simp_bitvector(term: &Bitvector32Term) -> Bitvector32Term {
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => term.clone(),
        Bitvector32Term::Add(left, right) => {
            bitvector32_add(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::Subtract(left, right) => {
            bitvector32_subtract(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::Multiply(left, right) => {
            bitvector32_multiply(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::Divide(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            bitvector32_divide(left.clone(), right.clone())
                .unwrap_or_else(|_| Bitvector32Term::Divide(Box::new(left), Box::new(right)))
        }
        Bitvector32Term::Remainder(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            bitvector32_remainder(left.clone(), right.clone())
                .unwrap_or_else(|_| Bitvector32Term::Remainder(Box::new(left), Box::new(right)))
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            bitvector32_shift_left(left.clone(), right.clone())
                .unwrap_or_else(|_| Bitvector32Term::ShiftLeft(Box::new(left), Box::new(right)))
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            bitvector32_shift_right(left.clone(), right.clone()).unwrap_or_else(|_| {
                Bitvector32Term::ArithmeticShiftRight(Box::new(left), Box::new(right))
            })
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            bitvector32_and(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            bitvector32_or(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            bitvector32_xor(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::BitwiseNot(value) => bitvector32_not(simp_bitvector(value)),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => match simp_condition_without_assumptions(condition) {
            Some(true) => simp_bitvector(then_term),
            Some(false) => simp_bitvector(else_term),
            None => Bitvector32Term::if_then_else(
                condition.as_ref().clone(),
                simp_bitvector(then_term),
                simp_bitvector(else_term),
            ),
        },
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => Bitvector32Term::range_fold(
            simp_bitvector(start),
            simp_bitvector(end),
            simp_bitvector(initial),
            *accumulator,
            *item,
            simp_bitvector(body),
        ),
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            Bitvector32Term::MemoryLoad(memory.clone(), pointer.clone())
        }
    }
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
                )
            })
            .cloned()
            .map(ExecutionPureFact::new),
    );
    let mut reasoning_facts = available_pure_facts.to_vec();
    reasoning_facts.extend(effect_facts.iter().map(|fact| fact.proposition().clone()));
    let assumptions = assumptions_from_propositions(&reasoning_facts);
    let mut derivations = Vec::new();
    let mut writes = memory_effect_write_pointers(&effect_facts);
    writes.retain(is_effect_relevant_pointer);

    for pointer in &writes {
        let Some(selected) = segments.iter().find_map(|segment| {
            let goals = pointer_containment_goals(segment, pointer, &assumptions)?;
            goals
                .into_iter()
                .map(|goal| assumptions.derive_proposition(&goal))
                .collect::<Option<Vec<_>>>()
        }) else {
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
        .filter(|range| is_effect_relevant_pointer(range.base()))
    {
        let Some(selected) = segments.iter().find_map(|segment| {
            let goals = range_containment_goals(segment, range, &assumptions)?;
            goals
                .into_iter()
                .map(|goal| assumptions.derive_proposition(&goal))
                .collect::<Option<Vec<_>>>()
        }) else {
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
                                Ok(required) => ClickError::new(format!(
                                    "`ensures {comparison}` failed for `{ensure_label}` path {path_index}: left side evaluated to {}, right side evaluated to {}\n  {}",
                                    describe_c_value(&left_value, parameters, arguments),
                                    describe_c_value(&right_value, parameters, arguments),
                                    describe_missing_pure_fact(
                                        &required,
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
            let surface_proposition = describe_click_proposition(proposition);
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
            let mut proposition = lower_outcome_proposition_with_program_points(
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
            proposition = unfold_predicates_in_proposition(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                &proposition,
                &assumptions,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`ensures {surface_proposition}` failed for `{ensure_label}` path {path_index}: {message}"
                ))
            })?;
            if !assumptions.proves(&proposition) {
                return Err(ClickError::new(format!(
                    "`ensures {surface_proposition}` failed for `{ensure_label}` path {path_index}: {}",
                    describe_missing_pure_fact(
                        &proposition,
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
                )
            })
            .cloned()
            .map(ExecutionPureFact::new),
    );
    let mut effect_reasoning_facts = available_pure_facts.to_vec();
    effect_reasoning_facts.extend(effect_facts.iter().map(|fact| fact.proposition().clone()));
    let assumptions = assumptions_from_propositions(&effect_reasoning_facts);
    let mut writes = memory_effect_write_pointers(&effect_facts);
    writes.retain(is_effect_relevant_pointer);

    for pointer in &writes {
        if !segments.iter().any(|segment| match policy {
            FootprintProofPolicy::Exact => {
                segment_contains_pointer_exact(segment, pointer, available_pure_facts)
            }
            FootprintProofPolicy::Contextual => {
                segment_contains_pointer(segment, pointer, &assumptions)
            }
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
        .filter(|range| is_effect_relevant_pointer(range.base()));

    for range in effect_summary_ranges {
        if !segments.iter().any(|segment| match policy {
            FootprintProofPolicy::Exact => {
                segment_contains_range_exact(segment, range, available_pure_facts)
            }
            FootprintProofPolicy::Contextual => {
                segment_contains_range(segment, range, &assumptions)
            }
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
    let Some(index) = pointer_element_index_from_base(pointer, &segment.base, &Assumptions::new())
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
) -> Option<[Proposition; 2]> {
    let index = pointer_element_index_from_base(pointer, &segment.base, assumptions)?;
    Some([
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
        pointer_element_index_from_base(range.base(), &segment.base, &Assumptions::new())
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
) -> Option<[Proposition; 2]> {
    let base_index = pointer_element_index_from_base(range.base(), &segment.base, assumptions)?;
    let range_start = bitvector32_add(base_index.clone(), range.start().clone());
    let range_end = bitvector32_add(base_index, range.end().clone());
    Some([
        Proposition::ConditionIs(signed_less_equal(segment.start.clone(), range_start), true),
        Proposition::ConditionIs(signed_less_equal(range_end, segment.end.clone()), true),
    ])
}

pub(super) fn is_effect_relevant_pointer(pointer: &Pointer) -> bool {
    !pointer.block.starts_with("local:") && !pointer.block.starts_with("havoc:")
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
    let assumptions = assumptions_from_propositions(available_pure_facts);
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

    if pointer_offsets_equal_for_effect(&pointer.offset, &base.offset, assumptions) {
        return Some(Bitvector32Term::Constant(0));
    }

    if base.offset == PointerOffsetTerm::Constant(0) {
        return int32_element_index_from_pointer_offset(&pointer.offset);
    }

    match &pointer.offset {
        PointerOffsetTerm::Add(left, right)
            if pointer_offsets_equal_for_effect(left, &base.offset, assumptions) =>
        {
            int32_element_index_from_pointer_offset(right)
        }
        PointerOffsetTerm::Add(left, right)
            if pointer_offsets_equal_for_effect(right, &base.offset, assumptions) =>
        {
            int32_element_index_from_pointer_offset(left)
        }
        _ => {
            if let (Some(pointer_index), Some(base_index)) = (
                int32_element_index_from_pointer_offset(&pointer.offset),
                int32_element_index_from_pointer_offset(&base.offset),
            ) {
                Some(bitvector32_subtract(pointer_index, base_index))
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

#[allow(clippy::too_many_arguments)]
pub(super) fn evaluate_contract_expression_with_program_points(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_pure_facts: &[Proposition],
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
) -> Result<CValue, String> {
    let parameter_values =
        parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &parameter_values, post_state.memory());
    let assumptions = assumptions_from_propositions(available_pure_facts);
    let mut active_functions = BTreeSet::new();
    evaluate_contract_expression_with_environment(
        &parameter_values,
        &array_refs,
        pre_state,
        post_state,
        Some(result),
        &assumptions,
        expression,
        predicate_environment,
        click_function_environment,
        program_point_states,
        &mut active_functions,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_outcome_proposition(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_pure_facts: &[Proposition],
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let program_point_states = ProgramPointStates::new();
    lower_outcome_proposition_with_program_points(
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        available_pure_facts,
        proposition,
        predicate_environment,
        click_function_environment,
        &program_point_states,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_outcome_proposition_with_program_points(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_pure_facts: &[Proposition],
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
) -> Result<Proposition, String> {
    let mut values = parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &values, post_state.memory());
    let assumptions = assumptions_from_propositions(available_pure_facts);
    let mut next_variable = 2_000_000;
    let mut active_functions = BTreeSet::new();
    lower_outcome_proposition_with_environment(
        &mut values,
        &array_refs,
        pre_state,
        post_state,
        Some(result),
        &assumptions,
        proposition,
        &mut next_variable,
        predicate_environment,
        click_function_environment,
        program_point_states,
        &mut active_functions,
    )
}

pub(super) fn lower_outcome_proposition_with_environment(
    values: &mut BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    proposition: &ClickProposition,
    next_variable: &mut u64,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<Proposition, String> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let left = evaluate_contract_expression_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            comparison_proposition(left, *operator, right).map_err(|error| error.message)
        }
        ClickProposition::Separate { left, right } => {
            let left = evaluate_resource_subject_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_resource_subject_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            Ok(Proposition::CResourceSeparate { left, right })
        }
        ClickProposition::Contains { parent, child } => {
            let parent = evaluate_resource_subject_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                parent,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let child = evaluate_resource_subject_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                child,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            Ok(Proposition::CResourceContains { parent, child })
        }
        ClickProposition::Loadable { segment } => {
            let segment = evaluate_contract_segment_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                segment,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let element_width =
                contract_segment_element_width_from_array_refs(array_refs, &segment.source)
                    .unwrap_or(4);
            let memory = match segment.source.state {
                ContractSegmentState::Current => post_state.memory(),
                ContractSegmentState::Old => pre_state.memory(),
            };
            loadable_segment_prop(memory, segment, element_width).map_err(|error| error.message)
        }
        ClickProposition::Defined { expression } => {
            let expression = contract_expression_to_c_fragment(expression).ok_or_else(|| {
                "`defined(...)` currently requires an expression without `old`, `at`, folds, lets, or Click function calls".to_string()
            })?;
            let mut state = post_state.clone();
            for (name, value) in values.iter() {
                state = state.with_local(name.clone(), value.clone());
            }
            if let Some(result) = result {
                state = state.with_local("result", result.clone());
            }
            c_expression_definedness_proposition(&state, &expression).map_err(|limit| {
                format!("`defined(...)` elaboration hit execution limit {limit:?}")
            })
        }
        ClickProposition::And(left, right) => Ok(Proposition::And(
            Box::new(lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?),
            Box::new(lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?),
        )),
        ClickProposition::Or(left, right) => Ok(Proposition::Or(
            Box::new(lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?),
            Box::new(lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?),
        )),
        ClickProposition::Not(body) => Ok(Proposition::Not(Box::new(
            lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?,
        ))),
        ClickProposition::Implies(left, right) => {
            let left = lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right_assumptions = assumptions.clone().assume_proposition(left.clone());
            let right = lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                &right_assumptions,
                right,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            Ok(Proposition::Implies(Box::new(left), Box::new(right)))
        }
        ClickProposition::ForAll { c_type, name, body } => {
            if *c_type != C0Type::Int32 {
                return Err("only `forall (int32 ...)` is supported".to_string());
            }
            let variable = Variable(*next_variable);
            *next_variable += 1;
            let previous = values.insert(
                name.clone(),
                CValue::Int32(Bitvector32Term::Variable(variable)),
            );
            let body = lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            match previous {
                Some(value) => {
                    values.insert(name.clone(), value);
                }
                None => {
                    values.remove(name);
                }
            }
            Ok(Proposition::ForAll {
                var: variable,
                sort: Sort::CInt32,
                body: Box::new(body),
            })
        }
        ClickProposition::Exists { c_type, name, body } => {
            if *c_type != C0Type::Int32 {
                return Err("only `exists (int32 ...)` is supported".to_string());
            }
            let variable = Variable(*next_variable);
            *next_variable += 1;
            let previous = values.insert(
                name.clone(),
                CValue::Int32(Bitvector32Term::Variable(variable)),
            );
            let body = lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            match previous {
                Some(value) => {
                    values.insert(name.clone(), value);
                }
                None => {
                    values.remove(name);
                }
            }
            Ok(Proposition::Exists {
                name: name.clone(),
                var: variable,
                sort: Sort::CInt32,
                body: Box::new(body),
            })
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => {
            let start = int32_term_value(
                evaluate_contract_expression_with_environment(
                    values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    start,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?,
                "range `all` start bound",
            )?;
            let end = int32_term_value(
                evaluate_contract_expression_with_environment(
                    values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    end,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?,
                "range `all` end bound",
            )?;
            let variable = Variable(*next_variable);
            *next_variable += 1;
            let item_bits = Bitvector32Term::Variable(variable);
            let item_value = CValue::Int32(item_bits.clone());
            let outer_values = values.clone();
            values.insert(item.clone(), item_value.clone());
            let body_assumptions =
                assumptions
                    .clone()
                    .assume_proposition(range_membership_proposition(
                        start.clone(),
                        item_bits.clone(),
                        end.clone(),
                    ));
            let body = match lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                &body_assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            ) {
                Ok(body) => body,
                Err(error) => {
                    *values = outer_values;
                    return Err(error);
                }
            };
            *values = outer_values;
            Ok(bounded_forall_int32(variable, start, item_bits, end, body))
        }
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            let start = int32_term_value(
                evaluate_contract_expression_with_environment(
                    values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    start,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?,
                "range `any` start bound",
            )?;
            let end = int32_term_value(
                evaluate_contract_expression_with_environment(
                    values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    end,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?,
                "range `any` end bound",
            )?;
            let outer_values = values.clone();
            match (
                concrete_bound_from_term(&start, "any", "start"),
                concrete_bound_from_term(&end, "any", "end"),
            ) {
                (Ok(start), Ok(end)) => {
                    let mut proposition = false_proposition();
                    for index in concrete_fold_range(start, end)? {
                        *values = outer_values.clone();
                        values.insert(
                            item.clone(),
                            CValue::Int32(Bitvector32Term::Constant(index as u32)),
                        );
                        let body = match lower_outcome_proposition_with_environment(
                            values,
                            array_refs,
                            pre_state,
                            post_state,
                            result,
                            assumptions,
                            body,
                            next_variable,
                            predicate_environment,
                            click_function_environment,
                            program_point_states,
                            active_functions,
                        ) {
                            Ok(body) => body,
                            Err(error) => {
                                *values = outer_values;
                                return Err(error);
                            }
                        };
                        proposition = disjunction(proposition, body);
                    }
                    *values = outer_values;
                    Ok(proposition)
                }
                _ => {
                    let variable = Variable(*next_variable);
                    *next_variable += 1;
                    let item_bits = Bitvector32Term::Variable(variable);
                    let item_value = CValue::Int32(item_bits.clone());
                    values.insert(item.clone(), item_value.clone());
                    let body_assumptions =
                        assumptions
                            .clone()
                            .assume_proposition(range_membership_proposition(
                                start.clone(),
                                item_bits.clone(),
                                end.clone(),
                            ));
                    let body = match lower_outcome_proposition_with_environment(
                        values,
                        array_refs,
                        pre_state,
                        post_state,
                        result,
                        &body_assumptions,
                        body,
                        next_variable,
                        predicate_environment,
                        click_function_environment,
                        program_point_states,
                        active_functions,
                    ) {
                        Ok(body) => body,
                        Err(error) => {
                            *values = outer_values;
                            return Err(error);
                        }
                    };
                    *values = outer_values;
                    Ok(bounded_exists_int32(
                        item.clone(),
                        variable,
                        start,
                        item_bits,
                        end,
                        body,
                    ))
                }
            }
        }
        ClickProposition::PredicateCall { name, arguments } => {
            let lowered_arguments = if let Some(definition) = predicate_environment.get(name) {
                lower_predicate_call_arguments_with_environment(
                    definition,
                    arguments,
                    values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?
            } else {
                let mut lowered_arguments = vec![Term::CMemory(post_state.memory().clone())];
                lowered_arguments.extend(
                    arguments
                        .iter()
                        .map(|argument| {
                            evaluate_contract_expression_with_environment(
                                values,
                                array_refs,
                                pre_state,
                                post_state,
                                result,
                                assumptions,
                                argument,
                                predicate_environment,
                                click_function_environment,
                                program_point_states,
                                active_functions,
                            )
                            .map(Term::CValue)
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                );
                lowered_arguments
            };
            Ok(Proposition::Predicate {
                name: name.clone(),
                arguments: lowered_arguments,
            })
        }
    }
}

fn evaluate_contract_segment_with_environment(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    segment: &ContractSegment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<EvaluatedContractSegment, String> {
    let evaluation_post_state = match segment.state {
        ContractSegmentState::Current => post_state,
        ContractSegmentState::Old => pre_state,
    };
    let base = evaluate_contract_expression_with_environment(
        parameter_values,
        array_refs,
        pre_state,
        evaluation_post_state,
        result,
        assumptions,
        &ContractExpression::CFragment(segment.base.clone()),
        predicate_environment,
        click_function_environment,
        program_point_states,
        active_functions,
    )?;
    let CValue::Pointer(base) = base else {
        return Err("segment base did not evaluate to a pointer".to_string());
    };
    let start = evaluate_contract_expression_with_environment(
        parameter_values,
        array_refs,
        pre_state,
        evaluation_post_state,
        result,
        assumptions,
        &ContractExpression::CFragment(segment.start.clone()),
        predicate_environment,
        click_function_environment,
        program_point_states,
        active_functions,
    )?;
    let CValue::Int32(start) = start else {
        return Err("segment start did not evaluate to int32".to_string());
    };
    let end = evaluate_contract_expression_with_environment(
        parameter_values,
        array_refs,
        pre_state,
        evaluation_post_state,
        result,
        assumptions,
        &ContractExpression::CFragment(segment.end.clone()),
        predicate_environment,
        click_function_environment,
        program_point_states,
        active_functions,
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

fn evaluate_resource_subject_with_environment(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    resource: &ResourceSubject,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<CResource, String> {
    match resource {
        ResourceSubject::Memory(segment) => {
            let segment = evaluate_contract_segment_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                segment,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            Ok(CResource::Memory(CMemoryRange::new(
                segment.base,
                segment.start,
                segment.end,
            )))
        }
        ResourceSubject::Declared {
            kind,
            name,
            arguments,
            parameter_types,
        } => {
            if arguments.len() != parameter_types.len() {
                return Err(format!(
                    "resource `{name}` has malformed argument type metadata"
                ));
            }
            let mut values = Vec::new();
            for (index, (argument, parameter_type)) in
                arguments.iter().zip(parameter_types).enumerate()
            {
                let value = evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    argument,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?;
                if !c_value_matches_click_type(&value, *parameter_type) {
                    return Err(format!(
                        "resource `{name}` argument {index} evaluated to {value:?}, which does not match {:?}",
                        parameter_type
                    ));
                }
                values.push(value);
            }
            Ok(match kind {
                ResourceKind::Composite => CResource::Composite {
                    name: name.clone(),
                    arguments: values,
                },
                ResourceKind::Token => CResource::Token {
                    name: name.clone(),
                    arguments: values,
                },
            })
        }
    }
}

pub(super) fn evaluate_contract_expression_with_environment(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<CValue, String> {
    match expression {
        ContractExpression::CFragment(expression) => evaluate_c_contract_expression(
            parameter_values,
            post_state,
            result,
            assumptions,
            expression,
        ),
        ContractExpression::Old(expression) => evaluate_contract_expression_with_environment(
            parameter_values,
            &array_refs_with_memory(array_refs, pre_state.memory()),
            pre_state,
            pre_state,
            None,
            assumptions,
            expression,
            predicate_environment,
            click_function_environment,
            program_point_states,
            active_functions,
        ),
        ContractExpression::At {
            selector,
            expression,
        } => {
            let snapshot_state =
                concrete_program_point_state(selector, pre_state, program_point_states)?;
            let (snapshot_values, snapshot_array_refs) =
                contract_environment_at_state(parameter_values, array_refs, snapshot_state);
            evaluate_contract_expression_with_environment(
                &snapshot_values,
                &snapshot_array_refs,
                pre_state,
                snapshot_state,
                None,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )
        }
        ContractExpression::Add(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_add(left, right)
        }
        ContractExpression::Subtract(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_sub(left, right)
        }
        ContractExpression::Multiply(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_multiply(left, right)
        }
        ContractExpression::Divide(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_divide(left, right)
        }
        ContractExpression::Remainder(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_remainder(left, right)
        }
        ContractExpression::ShiftLeft(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_shift_left(left, right)
        }
        ContractExpression::ShiftRight(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_shift_right(left, right)
        }
        ContractExpression::BitwiseAnd(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "&", bitvector32_and)
        }
        ContractExpression::BitwiseOr(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "|", bitvector32_or)
        }
        ContractExpression::BitwiseXor(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "^", bitvector32_xor)
        }
        ContractExpression::BitwiseNot(expression) => {
            let value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_not(value)
        }
        ContractExpression::Index(base, index) => {
            let array_ref = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                base,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let index = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                index,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let CValue::Int32(index) = index else {
                return Err(format!(
                    "array index did not evaluate to int32: `{index:?}`"
                ));
            };
            let element_type = array_ref.element_type;
            let pointer =
                offset_pointer_by_elements(array_ref.pointer, index, element_type.byte_width());
            evaluate_contract_memory_load_from_memory(
                &array_ref.memory,
                pointer,
                element_type,
                assumptions,
            )
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut values = parameter_values.clone();
            let mut next_variable = 2_000_000;
            let condition = lower_outcome_proposition_with_environment(
                &mut values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                condition,
                &mut next_variable,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            if assumptions.proves(&condition) {
                return evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    then_branch,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                );
            }
            if assumptions_prove_proposition_false(assumptions, &condition) {
                return evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    else_branch,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                );
            }

            let then_value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                then_branch,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let else_value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                else_branch,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            conditional_contract_value(&condition, then_value, else_value)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let start = int32_term_value(
                evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    start,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?,
                "fold start",
            )?;
            let end = int32_term_value(
                evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    end,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?,
                "fold end",
            )?;
            let mut value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                initial,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            match (
                concrete_bound_from_term(&start, "fold", "start"),
                concrete_bound_from_term(&end, "fold", "end"),
            ) {
                (Ok(start), Ok(end)) => {
                    for index in concrete_fold_range(start, end)? {
                        let mut fold_values = parameter_values.clone();
                        fold_values.insert(accumulator.clone(), value);
                        fold_values.insert(
                            item.clone(),
                            CValue::Int32(Bitvector32Term::Constant(index as u32)),
                        );
                        value = evaluate_contract_expression_with_environment(
                            &fold_values,
                            array_refs,
                            pre_state,
                            post_state,
                            result,
                            assumptions,
                            body,
                            predicate_environment,
                            click_function_environment,
                            program_point_states,
                            active_functions,
                        )?;
                    }
                    Ok(value)
                }
                _ => {
                    let mut fold_values = parameter_values.clone();
                    fold_values.insert(
                        accumulator.clone(),
                        CValue::Int32(Bitvector32Term::Variable(fold_bound_variable(
                            accumulator,
                            0,
                        ))),
                    );
                    fold_values.insert(
                        item.clone(),
                        CValue::Int32(Bitvector32Term::Variable(fold_bound_variable(item, 1))),
                    );
                    let body_value = evaluate_contract_expression_with_environment(
                        &fold_values,
                        array_refs,
                        pre_state,
                        post_state,
                        result,
                        assumptions,
                        body,
                        predicate_environment,
                        click_function_environment,
                        program_point_states,
                        active_functions,
                    )?;
                    symbolic_range_fold_value(start, end, value, accumulator, item, body_value)
                }
            }
        }
        ContractExpression::Let {
            name,
            c_type,
            value,
            body,
        } => {
            let value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                value,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let value = checked_contract_let_value(value, *c_type, name)?;
            let mut let_values = parameter_values.clone();
            let_values.insert(name.clone(), value);
            evaluate_contract_expression_with_environment(
                &let_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                body,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )
        }
        ContractExpression::Call { name, arguments } => evaluate_click_function_call(
            click_function_environment,
            name,
            arguments,
            parameter_values,
            array_refs,
            pre_state,
            post_state,
            result,
            assumptions,
            predicate_environment,
            program_point_states,
            active_functions,
        ),
    }
}

pub(super) fn array_refs_with_memory(
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
) -> ClickArrayRefs {
    array_refs
        .iter()
        .map(|(name, array_ref)| {
            (
                name.clone(),
                ClickArrayRef {
                    memory: memory.clone(),
                    pointer: array_ref.pointer.clone(),
                    element_type: array_ref.element_type,
                },
            )
        })
        .collect()
}

pub(super) fn contract_environment_at_state(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    state: &CState,
) -> (BTreeMap<String, CValue>, ClickArrayRefs) {
    let mut values = parameter_values.clone();
    values.extend(
        state
            .locals()
            .object_values()
            .map(|(name, value)| (name.to_string(), value.clone())),
    );

    let mut state_array_refs = array_refs_with_memory(array_refs, state.memory());
    for (name, value, element_type) in state.locals().array_object_values() {
        let CValue::Pointer(pointer) = value.clone() else {
            unreachable!("local array values are pointers")
        };
        values.insert(name.to_string(), value);
        state_array_refs.insert(
            name.to_string(),
            ClickArrayRef {
                memory: state.memory().clone(),
                pointer,
                element_type,
            },
        );
    }
    (values, state_array_refs)
}

fn concrete_program_point_state<'a>(
    selector: &VisitSelector,
    function_entry_state: &'a CState,
    program_point_states: &'a ProgramPointStates,
) -> Result<&'a CState, String> {
    match selector {
        VisitSelector::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        }) => Ok(function_entry_state),
        VisitSelector::ProgramPoint(point @ ProgramPointRef {
            region:
                CodeRegionRef::Statement(_) | CodeRegionRef::Loop(_) | CodeRegionRef::Label(_),
            ..
        }) => program_point_states.get(point).ok_or_else(|| {
            format!(
                "no state snapshot was recorded for `{}`; run `execute_step()` across that statement before using it in `at(...)`",
                describe_program_point_ref(point)
            )
        }),
        VisitSelector::ProgramPoint(point) => Err(format!(
            "`at({}, ...)` is not supported in concrete evaluation yet",
            describe_program_point_ref(point)
        )),
    }
}

pub(super) fn evaluate_click_function_call(
    click_function_environment: &ClickFunctionEnvironment,
    name: &str,
    arguments: &[ContractExpression],
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    predicate_environment: &PredicateEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<CValue, String> {
    let definition = click_function_environment
        .get(name)
        .ok_or_else(|| format!("unknown function `{name}`"))?;
    if arguments.len() != definition.parameters().len() {
        return Err(format!(
            "function `{}` expects {} argument(s), got {}",
            definition.name(),
            definition.parameters().len(),
            arguments.len()
        ));
    }
    if !active_functions.insert(name.to_string()) {
        return Err(format!(
            "recursive function call `{name}` is not supported yet"
        ));
    }

    let mut function_values = BTreeMap::new();
    let mut function_array_refs = BTreeMap::new();
    for (parameter, argument) in definition.parameters().iter().zip(arguments) {
        let value = if parameter_is_click_array_ref(parameter) {
            let array_ref = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let expected_element_type =
                click_array_element_type(parameter.c_type()).ok_or_else(|| {
                    format!(
                        "function `{}` parameter `{}` is not an array-ref parameter",
                        definition.name(),
                        parameter.name()
                    )
                })?;
            if array_ref.element_type != expected_element_type {
                return Err(format!(
                    "function `{}` parameter `{}` expects {:?} array elements, got {:?}",
                    definition.name(),
                    parameter.name(),
                    expected_element_type,
                    array_ref.element_type
                ));
            }
            let pointer = array_ref.pointer.clone();
            function_array_refs.insert(parameter.name().to_string(), array_ref);
            CValue::Pointer(pointer)
        } else {
            evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?
        };
        function_values.insert(parameter.name().to_string(), value);
    }

    let value = evaluate_contract_expression_with_environment(
        &function_values,
        &function_array_refs,
        post_state,
        post_state,
        None,
        assumptions,
        definition.body(),
        predicate_environment,
        click_function_environment,
        program_point_states,
        active_functions,
    )?;
    active_functions.remove(name);

    if !c_value_matches_click_type(&value, definition.return_type()) {
        return Err(format!(
            "function `{}` returned {value:?}, which does not match {:?}",
            definition.name(),
            definition.return_type()
        ));
    }
    Ok(value)
}

pub(super) fn evaluate_contract_array_ref_with_environment(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<ClickArrayRef, String> {
    match expression {
        ContractExpression::Old(expression) => {
            let pointer_value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                pre_state,
                None,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let CValue::Pointer(pointer) = pointer_value else {
                return Err(format!(
                    "array reference expression inside `old(...)` did not evaluate to a pointer: `{pointer_value:?}`"
                ));
            };
            let element_type =
                contract_array_ref_element_type(array_refs, expression).unwrap_or(CType::Int32);
            Ok(ClickArrayRef {
                memory: pre_state.memory().clone(),
                pointer,
                element_type,
            })
        }
        ContractExpression::At {
            selector,
            expression,
        } => {
            let snapshot_state =
                concrete_program_point_state(selector, pre_state, program_point_states)?;
            let (snapshot_values, snapshot_array_refs) =
                contract_environment_at_state(parameter_values, array_refs, snapshot_state);
            let pointer_value = evaluate_contract_expression_with_environment(
                &snapshot_values,
                &snapshot_array_refs,
                pre_state,
                snapshot_state,
                None,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let CValue::Pointer(pointer) = pointer_value else {
                return Err(format!(
                    "array reference expression inside `at({}, ...)` did not evaluate to a pointer: `{pointer_value:?}`",
                    describe_visit_selector(selector)
                ));
            };
            let element_type =
                contract_array_ref_element_type(array_refs, expression).unwrap_or(CType::Int32);
            Ok(ClickArrayRef {
                memory: snapshot_state.memory().clone(),
                pointer,
                element_type,
            })
        }
        ContractExpression::CFragment(CExpression::Variable(name)) => {
            if let Some(array_ref) = array_refs.get(name) {
                return Ok(array_ref.clone());
            }
            let pointer_value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let CValue::Pointer(pointer) = pointer_value else {
                return Err(format!(
                    "array reference `{name}` did not evaluate to a pointer: `{pointer_value:?}`"
                ));
            };
            Ok(ClickArrayRef {
                memory: post_state.memory().clone(),
                pointer,
                element_type: CType::Int32,
            })
        }
        ContractExpression::Add(left, right) => {
            if let Ok(array_ref) = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            ) {
                let offset = evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    right,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?;
                let CValue::Int32(offset) = offset else {
                    return Err(format!(
                        "array reference offset did not evaluate to int32: `{offset:?}`"
                    ));
                };
                let element_type = array_ref.element_type;
                return Ok(ClickArrayRef {
                    memory: array_ref.memory,
                    pointer: offset_pointer_by_elements(
                        array_ref.pointer,
                        offset,
                        element_type.byte_width(),
                    ),
                    element_type,
                });
            }
            if let Ok(array_ref) = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            ) {
                let offset = evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    left,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?;
                let CValue::Int32(offset) = offset else {
                    return Err(format!(
                        "array reference offset did not evaluate to int32: `{offset:?}`"
                    ));
                };
                let element_type = array_ref.element_type;
                return Ok(ClickArrayRef {
                    memory: array_ref.memory,
                    pointer: offset_pointer_by_elements(
                        array_ref.pointer,
                        offset,
                        element_type.byte_width(),
                    ),
                    element_type,
                });
            }
            evaluate_pointer_expression_as_current_array_ref(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )
        }
        ContractExpression::Subtract(left, right) => {
            if let Ok(array_ref) = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            ) {
                let offset = evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    right,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                    active_functions,
                )?;
                let CValue::Int32(offset) = offset else {
                    return Err(format!(
                        "array reference offset did not evaluate to int32: `{offset:?}`"
                    ));
                };
                let element_type = array_ref.element_type;
                return Ok(ClickArrayRef {
                    memory: array_ref.memory,
                    pointer: offset_pointer_by_elements(
                        array_ref.pointer,
                        bitvector32_subtract(Bitvector32Term::Constant(0), offset),
                        element_type.byte_width(),
                    ),
                    element_type,
                });
            }
            evaluate_pointer_expression_as_current_array_ref(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )
        }
        _ => evaluate_pointer_expression_as_current_array_ref(
            parameter_values,
            array_refs,
            pre_state,
            post_state,
            result,
            assumptions,
            expression,
            predicate_environment,
            click_function_environment,
            program_point_states,
            active_functions,
        ),
    }
}

pub(super) fn contract_array_ref_element_type(
    array_refs: &ClickArrayRefs,
    expression: &ContractExpression,
) -> Option<CType> {
    match expression {
        ContractExpression::CFragment(CExpression::Variable(name)) => {
            array_refs.get(name).map(|array_ref| array_ref.element_type)
        }
        ContractExpression::Old(expression) => {
            contract_array_ref_element_type(array_refs, expression)
        }
        ContractExpression::At { expression, .. } => {
            contract_array_ref_element_type(array_refs, expression)
        }
        ContractExpression::Add(left, right) => contract_array_ref_element_type(array_refs, left)
            .or_else(|| contract_array_ref_element_type(array_refs, right)),
        ContractExpression::Subtract(left, _) => contract_array_ref_element_type(array_refs, left),
        _ => None,
    }
}

pub(super) fn evaluate_pointer_expression_as_current_array_ref(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<ClickArrayRef, String> {
    let pointer_value = evaluate_contract_expression_with_environment(
        parameter_values,
        array_refs,
        pre_state,
        post_state,
        result,
        assumptions,
        expression,
        predicate_environment,
        click_function_environment,
        program_point_states,
        active_functions,
    )?;
    let CValue::Pointer(pointer) = pointer_value else {
        return Err(format!(
            "array reference expression did not evaluate to a pointer: `{pointer_value:?}`"
        ));
    };
    Ok(ClickArrayRef {
        memory: post_state.memory().clone(),
        pointer,
        element_type: CType::Int32,
    })
}

pub(super) fn lower_predicate_call_arguments_with_environment(
    definition: &PredicateDefinition,
    arguments: &[ContractExpression],
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    active_functions: &mut BTreeSet<String>,
) -> Result<Vec<Term>, String> {
    if arguments.len() != definition.parameters().len() {
        return Err(format!(
            "predicate `{}` expects {} argument(s), got {}",
            definition.name(),
            definition.parameters().len(),
            arguments.len()
        ));
    }

    let mut lowered_arguments = Vec::new();
    for (parameter, argument) in definition.parameters().iter().zip(arguments) {
        if parameter_is_click_array_ref(parameter) {
            let array_ref = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            let expected_element_type =
                click_array_element_type(parameter.c_type()).ok_or_else(|| {
                    format!(
                        "predicate `{}` parameter `{}` is not an array-ref parameter",
                        definition.name(),
                        parameter.name()
                    )
                })?;
            if array_ref.element_type != expected_element_type {
                return Err(format!(
                    "predicate `{}` parameter `{}` expects {:?} array elements, got {:?}",
                    definition.name(),
                    parameter.name(),
                    expected_element_type,
                    array_ref.element_type
                ));
            }
            lowered_arguments.push(Term::CMemory(array_ref.memory));
            lowered_arguments.push(Term::CValue(CValue::Pointer(array_ref.pointer)));
        } else {
            let value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                program_point_states,
                active_functions,
            )?;
            lowered_arguments.push(Term::CValue(value));
        }
    }
    Ok(lowered_arguments)
}

pub(super) fn c_value_matches_click_type(value: &CValue, c_type: C0Type) -> bool {
    matches!(
        (value, c_type),
        (CValue::Int32(_), C0Type::Int32)
            | (CValue::UInt8(_), C0Type::UInt8)
            | (CValue::Pointer(_), C0Type::Int32Pointer)
            | (CValue::Pointer(_), C0Type::UInt8Pointer)
    )
}

pub(super) fn checked_contract_let_value(
    value: CValue,
    c_type: Option<C0Type>,
    name: &str,
) -> Result<CValue, String> {
    let Some(c_type) = c_type else {
        return Ok(value);
    };
    if c_value_matches_click_type(&value, c_type) {
        Ok(value)
    } else {
        Err(format!(
            "let binding `{name}` evaluated to {value:?}, which does not match {c_type:?}"
        ))
    }
}

pub(super) fn evaluate_c_contract_expression(
    parameter_values: &BTreeMap<String, CValue>,
    state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    expression: &CExpression,
) -> Result<CValue, String> {
    match expression {
        CExpression::Value(value) => Ok(value.clone()),
        CExpression::Variable(name) if name == "result" => result
            .cloned()
            .ok_or_else(|| "`result` is not available inside `old(...)`".to_string()),
        CExpression::Variable(name) => parameter_values
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unknown contract variable `{name}`")),
        CExpression::Add(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_add(left, right)
        }
        CExpression::Subtract(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_sub(left, right)
        }
        CExpression::Multiply(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_multiply(left, right)
        }
        CExpression::Divide(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_divide(left, right)
        }
        CExpression::Remainder(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_remainder(left, right)
        }
        CExpression::ShiftLeft(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_shift_left(left, right)
        }
        CExpression::ShiftRight(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_shift_right(left, right)
        }
        CExpression::BitwiseAnd(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "&", bitvector32_and)
        }
        CExpression::BitwiseOr(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "|", bitvector32_or)
        }
        CExpression::BitwiseXor(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "^", bitvector32_xor)
        }
        CExpression::BitwiseNot(expression) => {
            let value = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                expression,
            )?;
            evaluate_postcondition_bitwise_not(value)
        }
        CExpression::Load(pointer) => {
            let pointer = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                pointer,
            )?;
            let CValue::Pointer(pointer) = pointer else {
                return Err("field load base is not a pointer".to_string());
            };
            evaluate_contract_memory_load(state, pointer, CType::Int32, assumptions)
        }
        CExpression::TypedLoad {
            pointer,
            value_type,
        } => {
            let pointer = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                pointer,
            )?;
            let CValue::Pointer(pointer) = pointer else {
                return Err("field load base is not a pointer".to_string());
            };
            evaluate_contract_memory_load(state, pointer, *value_type, assumptions)
        }
        CExpression::Index(base, index) => {
            let base =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, base)?;
            let index = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                index,
            )?;
            let pointer = evaluate_postcondition_pointer_add(base, index)?;
            evaluate_contract_memory_load(state, pointer, CType::Int32, assumptions)
        }
        _ => Err(format!(
            "unsupported postcondition expression `{expression:?}`"
        )),
    }
}

pub(super) fn evaluate_contract_memory_load(
    state: &CState,
    pointer: Pointer,
    value_type: CType,
    assumptions: &Assumptions,
) -> Result<CValue, String> {
    evaluate_contract_memory_load_from_memory(state.memory(), pointer, value_type, assumptions)
}

pub(super) fn evaluate_contract_memory_load_from_memory(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    assumptions: &Assumptions,
) -> Result<CValue, String> {
    match memory.load(&pointer) {
        crate::kernel::CExpressionOutcome::Value(value)
            if c_value_matches_kernel_type(&value, value_type) =>
        {
            Ok(value)
        }
        crate::kernel::CExpressionOutcome::Value(CValue::Int32(
            bits @ Bitvector32Term::MemoryLoad(_, _),
        )) if matches!(value_type, CType::Int32Pointer | CType::UInt8Pointer) => {
            symbolic_pointer_contract_memory_load(pointer, bits, value_type)
        }
        crate::kernel::CExpressionOutcome::Value(value) => Err(format!(
            "load from {pointer:?} produced {value:?}, not {value_type:?}"
        )),
        outcome => {
            let required = Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: pointer.clone(),
                bytes: Bitvector32Term::Constant(value_type.byte_width()),
            };
            if assumptions.proves(&required) {
                return symbolic_contract_memory_load(memory, pointer, value_type);
            }
            let pure_facts = assumptions.pure_facts();
            Err(format!(
                "{}\n  load from {pointer:?} as {value_type:?} produced {outcome:?}",
                describe_missing_pure_fact(&required, &pure_facts, &[], &[], &[], &[])
            ))
        }
    }
}

pub(super) fn c_value_matches_kernel_type(value: &CValue, c_type: CType) -> bool {
    matches!(
        (value, c_type),
        (CValue::Int32(_), CType::Int32)
            | (CValue::UInt8(_), CType::UInt8)
            | (
                CValue::Pointer(_),
                CType::Int32Pointer | CType::UInt8Pointer
            )
    )
}

pub(super) fn symbolic_contract_memory_load(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
) -> Result<CValue, String> {
    let load = Bitvector32Term::MemoryLoad(Box::new(memory.clone()), Box::new(pointer.clone()));
    match value_type {
        CType::Int32 => Ok(CValue::Int32(load)),
        CType::UInt8 => Ok(CValue::UInt8(load)),
        CType::Int32Pointer | CType::UInt8Pointer => {
            symbolic_pointer_contract_memory_load(pointer, load, value_type)
        }
        CType::Int32Array(_) | CType::UInt8Array(_) => {
            Err(format!("cannot symbolically load {value_type:?}"))
        }
    }
}

fn symbolic_pointer_contract_memory_load(
    pointer: Pointer,
    bits: Bitvector32Term,
    value_type: CType,
) -> Result<CValue, String> {
    let pointee_byte_width = match value_type {
        CType::Int32Pointer => 4,
        CType::UInt8Pointer => 1,
        _ => {
            return Err(format!(
                "cannot symbolically load {value_type:?} as pointer"
            ));
        }
    };
    Ok(CValue::Pointer(Pointer {
        block: pointer.block,
        offset: scale_int32_offset(bits, i64::from(pointee_byte_width)),
    }))
}

pub(super) fn evaluate_postcondition_add(left: CValue, right: CValue) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        return Ok(CValue::Int32(bitvector32_add(left_term, right_term)));
    }

    match (left, right) {
        (CValue::Pointer(pointer), offset) => promoted_int32_term(&offset)
            .map(|index| CValue::Pointer(offset_pointer_by_int32_elements(pointer, index)))
            .ok_or_else(|| format!("cannot add pointer and `{offset:?}`")),
        (offset, CValue::Pointer(pointer)) => promoted_int32_term(&offset)
            .map(|index| CValue::Pointer(offset_pointer_by_int32_elements(pointer, index)))
            .ok_or_else(|| format!("cannot add `{offset:?}` and pointer")),
        (left, right) => Err(format!("cannot add `{left:?}` and `{right:?}`")),
    }
}

pub(super) fn evaluate_postcondition_sub(left: CValue, right: CValue) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        return Ok(CValue::Int32(bitvector32_subtract(left_term, right_term)));
    }

    match (left, right) {
        (CValue::Pointer(pointer), offset) => {
            let Some(index) = promoted_int32_term(&offset) else {
                return Err(format!("cannot subtract `{offset:?}` from pointer"));
            };
            Ok(CValue::Pointer(offset_pointer_by_int32_elements(
                pointer,
                bitvector32_subtract(Bitvector32Term::Constant(0), index),
            )))
        }
        (left, right) => Err(format!("cannot subtract `{right:?}` from `{left:?}`")),
    }
}

pub(super) fn evaluate_postcondition_multiply(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        Ok(CValue::Int32(bitvector32_multiply(left_term, right_term)))
    } else {
        Err(format!("cannot multiply `{left:?}` and `{right:?}`"))
    }
}

pub(super) fn evaluate_postcondition_divide(left: CValue, right: CValue) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_divide(left_term, right_term).map(CValue::Int32)
    } else {
        Err(format!("cannot divide `{left:?}` by `{right:?}`"))
    }
}

pub(super) fn evaluate_postcondition_remainder(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_remainder(left_term, right_term).map(CValue::Int32)
    } else {
        Err(format!("cannot compute `{left:?}` % `{right:?}`"))
    }
}

pub(super) fn evaluate_postcondition_shift_left(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_shift_left(left_term, right_term).map(CValue::Int32)
    } else {
        Err(format!("cannot apply `<<` to `{left:?}` and `{right:?}`"))
    }
}

pub(super) fn evaluate_postcondition_shift_right(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_shift_right(left_term, right_term).map(CValue::Int32)
    } else {
        Err(format!("cannot apply `>>` to `{left:?}` and `{right:?}`"))
    }
}

pub(super) fn evaluate_postcondition_bitwise_binary(
    left: CValue,
    right: CValue,
    operator: &str,
    apply: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        Ok(CValue::Int32(apply(left_term, right_term)))
    } else {
        Err(format!(
            "cannot apply `{operator}` to `{left:?}` and `{right:?}`"
        ))
    }
}

pub(super) fn evaluate_postcondition_bitwise_not(value: CValue) -> Result<CValue, String> {
    if let Some(term) = promoted_int32_term(&value) {
        Ok(CValue::Int32(bitvector32_not(term)))
    } else {
        Err(format!("cannot apply `~` to `{value:?}`"))
    }
}

pub(super) fn evaluate_postcondition_pointer_add(
    left: CValue,
    right: CValue,
) -> Result<Pointer, String> {
    match evaluate_postcondition_add(left, right)? {
        CValue::Pointer(pointer) => Ok(pointer),
        value => Err(format!(
            "index base did not evaluate to a pointer: `{value:?}`"
        )),
    }
}

pub(super) fn offset_pointer_by_int32_elements(
    pointer: Pointer,
    elements: Bitvector32Term,
) -> Pointer {
    offset_pointer_by_elements(pointer, elements, 4)
}

pub(super) fn offset_pointer_by_elements(
    pointer: Pointer,
    elements: Bitvector32Term,
    element_width: u32,
) -> Pointer {
    Pointer {
        block: pointer.block,
        offset: add_pointer_offset(
            pointer.offset,
            scale_int32_offset(elements, i64::from(element_width)),
        ),
    }
}

pub(super) fn add_pointer_offset(
    left: PointerOffsetTerm,
    right: PointerOffsetTerm,
) -> PointerOffsetTerm {
    match (&left, &right) {
        (PointerOffsetTerm::Constant(left), PointerOffsetTerm::Constant(right)) => {
            PointerOffsetTerm::Constant(left + right)
        }
        (PointerOffsetTerm::Constant(0), _) => right,
        (_, PointerOffsetTerm::Constant(0)) => left,
        _ => PointerOffsetTerm::Add(Box::new(left), Box::new(right)),
    }
}

pub(super) fn scale_int32_offset(value: Bitvector32Term, byte_width: i64) -> PointerOffsetTerm {
    match value {
        Bitvector32Term::Constant(value) => {
            PointerOffsetTerm::Constant((value as i32 as i64) * byte_width)
        }
        value => PointerOffsetTerm::Int32Scaled {
            value: Box::new(value),
            byte_width,
        },
    }
}
