use super::*;

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn evaluate_contract_expression_with_recorded_snapshots(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_pure_facts: &[Proposition],
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    recorded_snapshots: &RecordedSnapshots,
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
        recorded_snapshots,
        &mut active_functions,
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn lower_outcome_proposition(
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
    let recorded_snapshots = RecordedSnapshots::new();
    lower_outcome_proposition_with_recorded_snapshots(
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        available_pure_facts,
        proposition,
        predicate_environment,
        click_function_environment,
        &recorded_snapshots,
    )
}

/// Lowers an outcome proposition against an already-indexed assumption
/// context. Proof-object transitions use this entry point so one proof step
/// does not rebuild the complete ambient fact context merely to lower its
/// explicit surface proposition.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn lower_outcome_proposition_with_assumptions(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    assumptions: &PureFactContext,
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let values = parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &values, post_state.memory());
    crate::surface::proof::lower_fixed_state_proposition_through_kernel(
        proposition,
        assumptions,
        &values,
        &array_refs,
        pre_state,
        post_state,
        Some(result),
        &RecordedSnapshots::new(),
        predicate_environment,
        click_function_environment,
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn lower_outcome_proposition_with_recorded_snapshots(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_pure_facts: &[Proposition],
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    recorded_snapshots: &RecordedSnapshots,
) -> Result<Proposition, String> {
    let values = parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &values, post_state.memory());
    let assumptions = assumptions_from_propositions(available_pure_facts);
    crate::surface::proof::lower_fixed_state_proposition_through_kernel(
        proposition,
        &assumptions,
        &values,
        &array_refs,
        pre_state,
        post_state,
        Some(result),
        recorded_snapshots,
        predicate_environment,
        click_function_environment,
    )
}

/// Lowers a proposition while retaining symbolic external-memory loads even
/// when the selected snapshot already materializes their values.
///
/// Fact transport needs this form for propositions such as
/// `at(mark, field == 11)`: reducing the marked load to `11 == 11` proves the
/// source but erases the memory identity needed to frame it to a later state.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn lower_outcome_proposition_symbolically_with_recorded_snapshots(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_pure_facts: &[Proposition],
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    recorded_snapshots: &RecordedSnapshots,
) -> Result<Proposition, String> {
    let values = parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &values, post_state.memory());
    let assumptions = assumptions_from_propositions(available_pure_facts)
        .allow_symbolic_contract_loads()
        .force_symbolic_external_loads();
    crate::surface::proof::lower_fixed_state_proposition_through_kernel(
        proposition,
        &assumptions,
        &values,
        &array_refs,
        pre_state,
        post_state,
        Some(result),
        recorded_snapshots,
        predicate_environment,
        click_function_environment,
    )
}
