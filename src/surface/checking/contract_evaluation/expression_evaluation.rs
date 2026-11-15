use super::*;

pub(in crate::surface) fn evaluate_contract_expression_with_environment(
    parameter_values: &BTreeMap<String, ProgramValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &ExecutionState,
    post_state: &ExecutionState,
    result: Option<&ProgramValue>,
    assumptions: &PureFactContext,
    expression: &ContractExpression,
    spec_definitions: SpecDefinitions<'_>,
    recorded_states: &RecordedStates,
    opaque_click_functions: &mut BTreeSet<String>,
) -> Result<ProgramValue, String> {
    crate::surface::proof::evaluate_fixed_state_expression_through_kernel(
        expression,
        assumptions,
        ContractEnvironment::new(parameter_values, array_refs),
        FixedStateFrame::new(pre_state, post_state, result, recorded_states),
        spec_definitions,
        opaque_click_functions,
    )
}
