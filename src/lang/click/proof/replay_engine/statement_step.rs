use super::*;

pub(in crate::lang::click::proof) struct CheckedStatementStep {
    pub(in crate::lang::click::proof) replay: TacticReplayState,
    pub(in crate::lang::click::proof) state: CState,
    pub(in crate::lang::click::proof) facts: ProofFacts,
    pub(in crate::lang::click::proof) added_facts: Vec<Proposition>,
    pub(in crate::lang::click::proof) path: Option<(ConditionTerm, bool)>,
}

/// Checks one explicit statement transition from exactly the named surface
/// premises and atomically advances the caller-selected execution successor.
///
/// This is the audited semantic operation shared by explicit source replay
/// and the checked proof-object frontier. It performs no premise search: the
/// selected surface premises are lowered, checked, and used as the only facts
/// transported across the statement boundary before ambient facts are
/// restored at their original snapshots.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn check_statement_step(
    replay: &mut TacticReplayState,
    state: &mut CState,
    requirement_pure_facts: &ProofFacts,
    function_block: &FunctionBlock,
    function: &CFunction,
    parsed_function: &syntax::C0Function,
    arguments: &[CExpression],
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
    tactic_index: usize,
    context: Option<&PureFactContext>,
) -> Result<Vec<CheckedStatementStep>, ClickError> {
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
    // Resuming from a completed branch region reaches this
    // statement without recording its entry snapshot; a premise
    // written `at(statement(N).entry, ...)` for the statement this
    // step crosses must still lower.
    record_current_statement_entry(
        replay,
        state,
        function_block,
        function,
        arguments,
        claim_label,
        tactic_index,
        tactic_name,
    )?;
    let pre_state = replay.old_reference_state(state).clone();
    let mut explicit_premises = Vec::new();
    for case in &replay.case_assumptions {
        let branch_fact = if let Some(fact) = &case.fact {
            fact.clone()
        } else {
            let proposition = lower_point_proposition_with_assumptions(
                &case.condition,
                assumptions,
                parsed_function.parameters(),
                arguments,
                &pre_state,
                state,
                None,
                &replay.program_point_states,
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
            .replay_available_across_effects(&branch_fact, &replay.effect_facts)
            && !explicit_premises.contains(&branch_fact)
        {
            explicit_premises.push(branch_fact);
        }
    }
    let explicit_assumptions = match context {
        Some(context) => context.clone(),
        None => assumptions_from_propositions(&explicit_premises),
    };
    for resource_fact in state
        .resources()
        .observable_facts_assuming_valid(&explicit_assumptions)
    {
        if !explicit_premises.contains(&resource_fact) {
            explicit_premises.push(resource_fact);
        }
    }
    let successors = execute_step_successors_from_execution_point(
        replay,
        state,
        &explicit_premises,
        function_block,
        function,
        parsed_function.parameters(),
        arguments,
        function_environment,
        claim_label,
        tactic_index,
        tactic_name,
        prerequisite_policy,
        // A step transports nothing: the kernel keeps the names of cells it
        // proves unwritten from the whole context, and ambient facts are
        // restored below at their original snapshots.
        StatementFactTransportPolicy::None,
        loop_step_policy,
        context,
    )?;
    Ok(successors
        .into_iter()
        .map(|successor| CheckedStatementStep {
            replay: successor.replay,
            state: successor.state,
            facts: requirement_pure_facts.with_statement_facts(successor.pure_facts),
            added_facts: successor.introduced_facts,
            path: successor.path,
        })
        .collect())
}
