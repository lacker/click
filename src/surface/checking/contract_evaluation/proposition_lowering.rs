use super::*;

pub(in crate::surface) fn lower_outcome_proposition(
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    post_state: &ExecutionState,
    result: &ProgramValue,
    available_pure_facts: &(impl PropositionSource + ?Sized),
    proposition: &ClickProposition,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    let recorded_states = RecordedStates::new();
    lower_outcome_proposition_with_recorded_states(
        parameter_binding,
        pre_state,
        post_state,
        result,
        available_pure_facts,
        proposition,
        spec_definitions,
        &recorded_states,
    )
}

/// Retains the kernel's checked auxiliary facts beside a resource body fact.
pub(in crate::surface) fn lower_outcome_proposition_with_auxiliary_facts(
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    post_state: &ExecutionState,
    result: &ProgramValue,
    assumptions: &PureFactContext,
    proposition: &ClickProposition,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<(Proposition, Vec<Proposition>), String> {
    let values = parameter_values(parameter_binding).map_err(|error| error.message)?;
    let array_refs =
        array_refs_for_parameters(parameter_binding.parameters, &values, post_state.memory());
    crate::surface::proof::lower_fixed_state_proposition_through_kernel_with_facts(
        proposition,
        assumptions,
        ContractEnvironment::new(&values, &array_refs),
        FixedStateFrame::new(pre_state, post_state, Some(result), &RecordedStates::new()),
        spec_definitions,
        FixedStateLoweringOptions::default(),
    )
    .map(|(proposition, _, facts)| {
        let facts = { facts };
        (proposition, facts)
    })
}

/// Lowers an outcome proposition against an already-indexed assumption
/// context. Proof-object transitions use this entry point so one proof step
/// does not rebuild the complete ambient fact context merely to lower its
/// explicit surface proposition.
pub(in crate::surface) fn lower_outcome_proposition_with_assumptions(
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    post_state: &ExecutionState,
    result: &ProgramValue,
    assumptions: &PureFactContext,
    proposition: &ClickProposition,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    let mut names = BTreeSet::new();
    crate::surface::lowering::collect_click_proposition_referenced_names(proposition, &mut names);
    let values = crate::surface::lowering::parameter_values_named(parameter_binding, &names)
        .map_err(|error| error.message)?;
    let array_refs = crate::surface::lowering::array_refs_for_values(
        parameter_binding,
        &values,
        post_state.memory(),
    );
    crate::surface::proof::lower_fixed_state_proposition_through_kernel(
        proposition,
        assumptions,
        ContractEnvironment::new(&values, &array_refs),
        FixedStateFrame::new(pre_state, post_state, Some(result), &RecordedStates::new()),
        spec_definitions,
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn lower_outcome_proposition_with_recorded_states(
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    post_state: &ExecutionState,
    result: &ProgramValue,
    available_pure_facts: &(impl PropositionSource + ?Sized),
    proposition: &ClickProposition,
    spec_definitions: SpecDefinitions<'_>,
    recorded_states: &RecordedStates,
) -> Result<Proposition, String> {
    let values = parameter_values(parameter_binding).map_err(|error| error.message)?;
    let array_refs =
        array_refs_for_parameters(parameter_binding.parameters, &values, post_state.memory());
    let assumptions = assumptions_from_propositions(available_pure_facts);
    crate::surface::proof::lower_fixed_state_proposition_through_kernel(
        proposition,
        &assumptions,
        ContractEnvironment::new(&values, &array_refs),
        FixedStateFrame::new(pre_state, post_state, Some(result), recorded_states),
        spec_definitions,
    )
}
