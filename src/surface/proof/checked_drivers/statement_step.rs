use super::*;

pub(in crate::surface::proof) struct CheckedStatementStep {
    pub(in crate::surface::proof) execution: ExecutionProofState,
    pub(in crate::surface::proof) facts: ProofFacts,
    pub(in crate::surface::proof) added_facts: Vec<Proposition>,
}

/// Checks one statement transition in the complete proof context and
/// atomically advances the caller-selected execution successor.
///
/// This is the audited semantic operation shared by explicit source check
/// and the checked proof-object frontier. It performs no premise selection;
/// the proof's facts and resources are the transition context.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn check_statement_step(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    requirement_pure_facts: &ProofFacts,
    context: Option<&PureFactContext>,
) -> Result<CheckedStatementStep, ClickError> {
    let prerequisite_policy = if context.is_some() {
        StatementPrerequisitePolicy::Contextual
    } else {
        StatementPrerequisitePolicy::Explicit
    };
    check_statement_step_with_policy(
        execution,
        proof_context,
        requirement_pure_facts,
        context,
        prerequisite_policy,
    )
}

/// Checks one statement with the caller-selected prerequisite policy. The
/// source-backed retry policy shares Contextual derivation and differs only in
/// exposing a supported call carrier before hidden derivation.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn check_statement_step_with_policy(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    requirement_pure_facts: &ProofFacts,
    context: Option<&PureFactContext>,
    prerequisite_policy: StatementPrerequisitePolicy,
) -> Result<CheckedStatementStep, ClickError> {
    let function_block = proof_context.function_block;
    let function = proof_context.function;
    let parsed_function = proof_context.parsed_function;
    let arguments = proof_context.arguments;
    let predicate_environment = proof_context.predicate_environment;
    let click_function_environment = proof_context.click_function_environment;
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;

    let state: &mut CState = &mut execution.core.state;
    let assumptions = requirement_pure_facts.assumptions();
    // A bare `step()` executes in the whole proof context: prerequisites
    // are proved from it, and nothing is transported per step because the
    // kernel keeps cell names it can prove unwritten from that context.
    let tactic_name = "step()";
    let loop_step_policy = LoopStepPolicy::EnterBody;
    // Resuming from a completed branch region reaches this statement without
    // recording its entry snapshot. Later facts may still name this boundary.
    record_current_statement_entry(
        &execution.core.frontier,
        &mut execution.presentation.recorded_snapshots,
        state,
        function_block,
        function,
        arguments,
        claim_label,
        tactic_index,
        tactic_name,
    )?;
    let pre_state = proof_context
        .old_reference_state(&execution.core.frontier, state)
        .clone();
    let mut step_facts = Vec::new();
    for case in &execution.presentation.case_assumptions {
        let branch_fact = if let Some(fact) = &case.fact {
            fact.clone()
        } else {
            let proposition = lower_fixed_state_proposition_with_assumptions(
                &case.condition,
                assumptions,
                parsed_function.parameters(),
                arguments,
                &pre_state,
                state,
                None,
                &execution.presentation.recorded_snapshots,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower enclosing proof-branch condition: {message}"
                ))
            })?;
            if case.value {
                proposition
            } else {
                match proposition {
                    Proposition::ConditionIs(condition, value) => {
                        Proposition::ConditionIs(condition, !value)
                    }
                    Proposition::Not(body) => *body,
                    proposition => Proposition::Not(Box::new(proposition)),
                }
            }
        };
        if requirement_pure_facts
            .available_across_effects(&branch_fact, &execution.core.effect_facts)
            && !step_facts.contains(&branch_fact)
        {
            step_facts.push(branch_fact);
        }
    }
    let step_assumptions = match context {
        Some(context) => context.clone(),
        None => assumptions_from_propositions(&step_facts),
    };
    for resource_fact in state
        .resources()
        .observable_facts_assuming_valid(&step_assumptions)
    {
        if !step_facts.contains(&resource_fact) {
            step_facts.push(resource_fact);
        }
    }
    let apply = |policy, selected_context| {
        execute_step_successor_from_frontier_position(
            execution,
            proof_context,
            &step_facts,
            tactic_name,
            policy,
            // A step transports nothing: the kernel keeps the names of cells it
            // proves unwritten from the whole context, and ambient facts are
            // restored below at their original snapshots.
            StatementFactTransportPolicy::None,
            loop_step_policy,
            selected_context,
        )
    };
    let successor = match apply(prerequisite_policy, context) {
        Err(error) if matches!(prerequisite_policy, StatementPrerequisitePolicy::Retained) => {
            let exact_retained_requirement =
                error.unresolved_requirement().is_some_and(|requirement| {
                    // The execution obligation is an implication from the
                    // currently refused prerequisite to the remaining call.
                    // Authorize the retry from that one exact antecedent,
                    // never from a related ambient fact.
                    let stated_prerequisite = match &requirement.proposition {
                        Proposition::Implies(prerequisite, _) => prerequisite.as_ref(),
                        proposition => proposition,
                    };
                    requirement.call_site.is_some()
                        && execution
                            .presentation
                            .surface_record
                            .retained_have_facts
                            .pure_assumption_available(stated_prerequisite)
                });
            if !exact_retained_requirement {
                return Err(error);
            }
            // Contextual checking may now compose the call, but only from
            // ordinary checked `have`s and this statement's local path or
            // resource facts. The ambient proof context is deliberately not
            // visible to the retry.
            let retained_context = step_facts.iter().fold(
                execution
                    .presentation
                    .surface_record
                    .retained_have_facts
                    .assumptions()
                    .clone(),
                |context, fact| context.assume_proposition(fact.clone()),
            );
            apply(
                StatementPrerequisitePolicy::Contextual,
                Some(&retained_context),
            )?
        }
        result => result?,
    };
    Ok(CheckedStatementStep {
        execution: successor.execution,
        facts: requirement_pure_facts.with_statement_facts(successor.pure_facts),
        added_facts: successor.introduced_facts,
    })
}
