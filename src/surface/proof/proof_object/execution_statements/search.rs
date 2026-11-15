//! Premise discovery for bare transport. Explicit transport stays on Proof.

use super::*;

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// The one mid-execution `transport` premise law, shared by the drivers:
    /// the source and target are lowered at the frontier, the premise
    /// planner names the premises, and the driver applies the explicit
    /// `transport using` transition. The planner's failure is the answer,
    /// with its diagnostic. `source_refusal` is the refusal of the bare
    /// form's source-only attempt, which that diagnostic reports when it
    /// names a frame the source could not cross.
    pub(in crate::surface::proof) fn apply_planned_fact_transport(
        search_input: &Proof<'a>,
        surface_source: &ClickProposition,
        surface_target: &ClickProposition,
        tactic_index: usize,
        source_refusal: Option<&ClickError>,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_planned_fact_transport");
        Self::apply_planned_fact_transport_inner(
            search_input,
            surface_source,
            surface_target,
            tactic_index,
            source_refusal,
        )
        .map_err(|error| {
            search_input.record_certification_failure_trace(search_input.claim_label(), 0);
            search_input.attach_step_diagnostic(error)
        })
    }

    fn apply_planned_fact_transport_inner(
        search_input: &Proof<'a>,
        surface_source: &ClickProposition,
        surface_target: &ClickProposition,
        tactic_index: usize,
        source_refusal: Option<&ClickError>,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_planned_fact_transport_inner");
        let resolved_source =
            search_input.substitute_fixed_state_locals_in_proposition(surface_source)?;
        let resolved_target =
            search_input.substitute_fixed_state_locals_in_proposition(surface_target)?;
        let ProofContext::Execution(context) = search_input.context.as_ref() else {
            return Err(search_input.step_error("`transport` requires an execution-frontier proof"));
        };
        let claim_label = context.claim_label;
        if search_input.focused_outcome_data().is_some() {
            return Self::apply_planned_outcome_fact_transport(
                search_input,
                surface_source,
                surface_target,
                tactic_index,
                source_refusal,
            );
        }
        let premises = {
            let view = search_input.planning_execution_view()?;
            let (state, frontier, facts) = (view.state, view.frontier, &view.facts.to_vec());
            if frontier.is_at_function_entry() || frontier.is_at_function_exit() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a current statement frontier after at least one completed execution step"
                )));
            }
            let assumptions = assumptions_from_propositions(facts);
            let pre_state = view.context.old_reference_state(frontier, state);
            let source = lower_fixed_state_proposition(
                &resolved_source,
                facts,
                context.parameter_binding(),
                FixedStateFrame::new(pre_state, state, None, &view.execution.presentation.recorded_states),
                context.spec_definitions,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport` source: {message}"
                ))
            })?;
            if crate::kernel::search::ProofSearch::derive_proposition(&(assumptions), &source)
                .is_none()
            {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a source derivable from its ambient facts: {}",
                    describe_missing_pure_fact(
                        &source,
                        facts,
                        state.resources().facts(),
                        context.parameter_binding(),
                        &view.execution.core.effect_facts,
                    )
                )));
            }
            let target = lower_fixed_state_proposition(
                &resolved_target,
                facts,
                context.parameter_binding(),
                FixedStateFrame::new(pre_state, state, None, &view.execution.presentation.recorded_states),
                context.spec_definitions,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport` target: {message}"
                ))
            })?;
            let transition_facts =
                crate::surface::proof::cursor_execution::fact_transport_transition_facts(
                    &view.execution.core.effect_facts,
                    &source,
                );
            plan_explicit_fact_transport(
                surface_source,
                &source,
                &target,
                view.facts,
                &transition_facts,
                context.parameter_binding(),
                state,
            )
            .map_err(|error| {
                let mut reason = fact_transport_planning_failure(
                    surface_source,
                    surface_target,
                    view.unfolded_predicates,
                    &error,
                    source_refusal,
                );
                if crate::instrumentation::deadline_exceeded() {
                    // Lowering already produced these checked identities.
                    // A stopped planner may print them without rechecking or
                    // trying further proof routes after its budget expired.
                    use crate::surface::proof_diagnostics::render;
                    let _typed = render::TypedNotationScope::enter();
                    let mut labels = render::MemoryStateLabels::with_state(
                        context.parameter_binding(), state,
                    );
                    let source = render::render_proposition_labeled(&source, &mut labels);
                    let target = render::render_proposition_labeled(&target, &mut labels);
                    reason.push_str(&format!(
                        "\n  checked source (holds): {source}\n  checked target (wanted): {target}{}",
                        labels.trace_legend(),
                    ));
                }
                ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {reason}"))
            })?
        };
        search_input.driver().apply_step(ProofStep::TransportUsing {
            source: surface_source.clone(),
            target: surface_target.clone(),
            premises,
        })
    }
    /// The live-state search planner on a focused function outcome:
    /// the same premise planner, reading the path's effects, the returned
    /// state and the outcome's facts.
    fn apply_planned_outcome_fact_transport(
        search_input: &Proof<'a>,
        surface_source: &ClickProposition,
        surface_target: &ClickProposition,
        tactic_index: usize,
        source_refusal: Option<&ClickError>,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_planned_outcome_fact_transport");
        let ProofContext::Execution(context) = search_input.context.as_ref() else {
            return Err(search_input.step_error("`transport` requires an execution proof"));
        };
        let claim_label = context.claim_label;
        let (Some(data), Some(execution)) = (
            search_input.focused_outcome_data(),
            search_input.execution(),
        ) else {
            return Err(search_input.step_error("`transport` lost its focused function outcome"));
        };
        let source =
            search_input.lower_surface_proposition_direct(surface_source, "`transport` source")?;
        if crate::kernel::search::ProofSearch::derive_proposition(
            search_input.facts().assumptions(),
            &source,
        )
        .is_none()
        {
            let facts = search_input.facts().to_vec();
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `transport` requires a source derivable from its ambient facts: {}",
                describe_missing_pure_fact(
                    &source,
                    &facts,
                    data.core.state.resources().facts(),
                    context.parameter_binding(),
                    &*data.core.effect_facts,
                )
            )));
        }
        let target =
            search_input.lower_surface_proposition_direct(surface_target, "`transport` target")?;
        let transition_facts =
            crate::surface::proof::cursor_execution::fact_transport_transition_facts(
                &*data.core.effect_facts,
                &source,
            );
        let premises = plan_explicit_fact_transport(
            surface_source,
            &source,
            &target,
            search_input.facts(),
            &transition_facts,
            context.parameter_binding(),
            &data.core.state,
        )
        .map_err(|error| {
            let reason = fact_transport_planning_failure(
                surface_source,
                surface_target,
                &execution.core.unfolded_predicates,
                &error,
                source_refusal,
            );
            ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {reason}"))
        })?;
        search_input.driver().apply_step(ProofStep::TransportUsing {
            source: surface_source.clone(),
            target: surface_target.clone(),
            premises,
        })
    }
}
