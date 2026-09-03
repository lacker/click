use super::diagnostics::*;
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
    let chosen_variable = Variable(*next_choice_variable);
    *next_choice_variable += 1;
    let chosen = match sort {
        Sort::CInt32 => CValue::Int32(Bitvector32Term::Variable(chosen_variable)),
        Sort::CPointer(c_type @ CType::FunctionPointer(_)) => {
            CValue::typed_pointer(Pointer::symbolic_function(chosen_variable), c_type)
        }
        Sort::CPointer(c_type) => CValue::typed_pointer(Pointer::symbolic(chosen_variable), c_type),
        _ => {
            return Err(ClickError::new(format!(
                "`choose` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: unsupported existential sort"
            )));
        }
    };
    let chosen_fact = match &chosen {
        CValue::Int32(value) => substitute_int32_variable_in_proposition(&body, var, value.clone()),
        CValue::Pointer(pointer) => {
            crate::kernel::substitute_pointer_variable_in_proposition(&body, var, pointer.pointer())
        }
        CValue::Void | CValue::UInt8(_) => unreachable!("unsupported choice sort above"),
    };
    values.insert(choice.name.clone(), chosen);
    available_pure_facts.push(chosen_fact);
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
    assumptions: &PureFactContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    recorded_snapshots: &RecordedSnapshots,
) -> Result<CValue, ClickError> {
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
        recorded_snapshots,
        &mut active_functions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: could not evaluate witness value for `{}`: {message}",
            witness.name
        ))
    })?;
    Ok(value)
}

pub(super) fn apply_witness_tactic(
    witness: &ProofWitness,
    witness_value: CValue,
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
    if name != witness.name {
        return Err(ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: goal binds `{name}`, but proof provided witness `{}`",
            witness.name
        )));
    }

    let result = match (sort, witness_value) {
        (Sort::CInt32, CValue::Int32(value)) => {
            substitute_int32_variable_in_proposition(&body, var, value)
        }
        (Sort::CPointer(expected), CValue::Pointer(pointer))
            if expected.accepts(&CValue::Pointer(pointer.clone())) =>
        {
            crate::kernel::substitute_pointer_variable_in_proposition(&body, var, pointer.pointer())
        }
        (Sort::CPointer(_), CValue::Pointer(_)) => {
            return Err(ClickError::new(format!(
                "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: witness `{}` has the wrong pointer kind",
                witness.name
            )));
        }
        (Sort::CInt32, _) => {
            return Err(ClickError::new(format!(
                "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: witness `{}` did not evaluate to int32",
                witness.name
            )));
        }
        _ => {
            return Err(ClickError::new(format!(
                "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: unsupported existential witness sort for `{}`",
                witness.name
            )));
        }
    };
    Ok(result)
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
    recorded_snapshots: &RecordedSnapshots,
    unfolded_predicates: &[String],
) -> Result<Proposition, String> {
    let CFunctionOutcome::Return { value, state } = outcome else {
        return Err("the execution path does not return".to_string());
    };
    let proposition = lower_outcome_proposition_with_recorded_snapshots(
        parameters,
        arguments,
        pre_state,
        state,
        value,
        available_pure_facts,
        proposition,
        predicate_environment,
        click_function_environment,
        recorded_snapshots,
    );
    if crate::instrumentation::deadline_exceeded() {
        return Err(format!(
            "verification budget exhausted inside {}",
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
