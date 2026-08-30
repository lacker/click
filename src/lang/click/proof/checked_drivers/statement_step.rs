use super::*;

pub(in crate::lang::click::proof) struct CheckedStatementStep {
    pub(in crate::lang::click::proof) execution: ExecutionProofState,
    pub(in crate::lang::click::proof) facts: ProofFacts,
    pub(in crate::lang::click::proof) added_facts: Vec<Proposition>,
}

/// Checks one statement transition in the complete proof context and
/// atomically advances the caller-selected execution successor.
///
/// This is the audited semantic operation shared by explicit source check
/// and the checked proof-object frontier. It performs no premise selection;
/// the proof's facts and resources are the transition context.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn check_statement_step(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    requirement_pure_facts: &ProofFacts,
    context: Option<&PureFactContext>,
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
    let prerequisite_policy = if context.is_some() {
        StatementPrerequisitePolicy::Contextual
    } else {
        StatementPrerequisitePolicy::Explicit
    };
    let loop_step_policy = LoopStepPolicy::EnterBody;
    // Resuming from a completed branch region reaches this statement without
    // recording its entry snapshot. Later facts may still name this boundary.
    record_current_statement_entry(
        &execution.core.frontier,
        &mut execution.recorded_snapshots,
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
    for case in &execution.case_assumptions {
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
                &execution.recorded_snapshots,
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
    let successor = execute_step_successor_from_frontier_position(
        execution,
        proof_context,
        &step_facts,
        tactic_name,
        prerequisite_policy,
        // A step transports nothing: the kernel keeps the names of cells it
        // proves unwritten from the whole context, and ambient facts are
        // restored below at their original snapshots.
        StatementFactTransportPolicy::None,
        loop_step_policy,
        context,
    )?;
    Ok(CheckedStatementStep {
        execution: successor.execution,
        facts: requirement_pure_facts.with_statement_facts(successor.pure_facts),
        added_facts: successor.introduced_facts,
    })
}
