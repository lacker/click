use super::*;

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn lower_outcome_proposition(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_pure_facts: &(impl PropositionSource + ?Sized),
    proposition: &ClickProposition,
    spec_definitions: SpecDefinitions<'_>,
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
        spec_definitions,
        &recorded_snapshots,
    )
}

/// Retains the kernel's checked auxiliary facts beside a resource body fact.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn lower_outcome_proposition_with_auxiliary_facts(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    assumptions: &PureFactContext,
    proposition: &ClickProposition,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<(Proposition, Vec<Proposition>), String> {
    let values = parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &values, post_state.memory());
    crate::surface::proof::lower_fixed_state_proposition_through_kernel_recording_introductions_with_bound_array_memories_and_facts(
        proposition,
        assumptions,
        assumptions,
        &values,
        &array_refs,
        &BTreeMap::new(),
        &crate::persistent::PersistentMap::default(),
        &BTreeMap::new(),
        pre_state,
        post_state,
        Some(result),
        &RecordedSnapshots::new(),
        spec_definitions,
        &std::collections::BTreeSet::new(),
        BTreeMap::new(),
    )
    .map(|(proposition, _, facts)| {
        let facts = {
            facts
        };
        (proposition, facts)
    })
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
    spec_definitions: SpecDefinitions<'_>,
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
        spec_definitions,
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn lower_outcome_proposition_with_recorded_snapshots(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_pure_facts: &(impl PropositionSource + ?Sized),
    proposition: &ClickProposition,
    spec_definitions: SpecDefinitions<'_>,
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
        spec_definitions,
    )
}
