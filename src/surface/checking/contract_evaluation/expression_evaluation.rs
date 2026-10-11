use super::*;

pub(in crate::surface) fn evaluate_contract_expression_with_environment(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &PureFactContext,
    expression: &ContractExpression,
    spec_definitions: SpecDefinitions<'_>,
    recorded_snapshots: &RecordedSnapshots,
    opaque_click_functions: &mut BTreeSet<String>,
) -> Result<CValue, String> {
    crate::surface::proof::evaluate_fixed_state_expression_through_kernel(
        expression,
        assumptions,
        parameter_values,
        array_refs,
        pre_state,
        post_state,
        result,
        recorded_snapshots,
        spec_definitions,
        opaque_click_functions,
    )
}
