use super::*;

pub(in crate::surface::proof) struct CheckedStatementStep {
    pub(in crate::surface::proof) execution: ExecutionProofState,
    pub(in crate::surface::proof) facts: ProofFacts,
    pub(in crate::surface::proof) added_facts: Vec<Proposition>,
}

/// Checks one statement transition in the complete proof context with the
/// caller-selected prerequisite policy, and atomically advances the
/// caller-selected execution successor.
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
    let predicate_environment = proof_context.spec_definitions.predicates;
    let click_function_environment = proof_context.spec_definitions.functions;
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;

    let checked_case_context = execution
        .core
        .checked_step_case_context(execution.presentation.case_assumptions.len());
    let state: &mut ExecutionState = &mut execution.core.state;
    let assumptions = requirement_pure_facts.assumptions();
    // A bare `step()` executes in the whole proof context: prerequisites
    // are proved from it, and nothing is transported per step because the
    // kernel keeps cell names it can prove unwritten from that context.
    let tactic_name = proof_context.step_tactic_name;
    let loop_step_policy = LoopStepPolicy::EnterBody;
    // Resuming from a completed branch region reaches this statement without
    // recording its entry state. Later facts may still name this boundary.
    record_current_statement_entry(
        &execution.core.frontier,
        &mut execution.presentation.recorded_states,
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
    // Membership of the list as it grows: a step lists every case of its
    // path, and scanning the list for each would cost the cases' square.
    let mut listed = std::collections::HashSet::new();
    for case in &execution.presentation.case_assumptions {
        let branch_fact = if let Some(fact) = &case.fact {
            fact.clone()
        } else {
            let proposition = lower_fixed_state_proposition_with_assumptions(
                &case.condition,
                assumptions,
                ParameterBinding::new(parsed_function.parameters(), arguments),
                FixedStateFrame::new(&pre_state, state, None, &execution.presentation.recorded_states),
                SpecDefinitions::new(predicate_environment, click_function_environment),
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
            && listed.insert(branch_fact.clone())
        {
            step_facts.push(branch_fact);
        }
    }
    // Reuse only the kernel-admitted case prefix when all written cases
    // selected one distinct available fact each. Other producers and dropped
    // or duplicate cases keep the ordinary ordered fold.
    let mut local_context = checked_case_context.filter(|cases| {
        step_facts.len() == execution.presentation.case_assumptions.len()
            && step_facts.iter().all(|fact| cases.proves_exact(fact))
    });
    let step_assumptions = match context {
        Some(context) => context.clone(),
        None => assumptions_from_propositions(&step_facts),
    };
    for resource_fact in state
        .resources()
        .observable_facts_assuming_valid(&step_assumptions)
    {
        if listed.insert(resource_fact.clone()) {
            if let Some(local) = &mut local_context {
                crate::kernel::reasoning::path_facts::count_context_rebuild_entries(1);
                *local = local.clone().assume_proposition(resource_fact.clone());
            }
            step_facts.push(resource_fact);
        }
    }
    let step_facts = match local_context {
        Some(context) => PureFactList::with_checked_context(step_facts, context),
        None => PureFactList::from(step_facts),
    };
    let apply = |policy, selected_context| {
        execute_step_successor_from_frontier_position(
            execution,
            proof_context,
            &step_facts,
            tactic_name,
            policy,
            // A step transports nothing: the kernel keeps the names of cells it
            // proves unwritten from the whole context, and ambient facts are
            // restored below at their original states.
            loop_step_policy,
            selected_context,
        )
    };
    let previous_effect_count = execution.core.effect_facts.len();
    let successor = apply(prerequisite_policy, context)?;
    let mut completed = successor.execution;
    let mut facts = requirement_pure_facts.with_statement_facts_retaining_prefix(
        successor.pure_facts.into_vec(),
        &completed.core.publication_case_prefix(),
    );
    // The checked core appends the selected statement's certified evidence.
    // Publish its typed read metadata as well as its proposition; walk only
    // this step's suffix, rather than earlier effects or ambient proof facts.
    let effect_delta = completed
        .core
        .effect_facts
        .len()
        .saturating_sub(previous_effect_count);
    for fact in completed.core.effect_facts.iter().rev().take(effect_delta) {
        facts.retain_checked_read_fact(fact);
    }
    let effect_leaf = super::super::proof_object::EffectLeaf::after_statement(
        completed.presentation.effect_leaf.as_deref(),
        &facts,
        &completed.core.effect_facts,
    );
    // This is checked semantic state, shared by both source and Proof drivers.
    // A statement with several outcomes cannot attach one branch's facts to
    // every candidate; loop-return producers likewise keep their own bases.
    completed.presentation.checked_leaf_facts = completed
        .core
        .frontier
        .execution()
        .filter(|paths| paths.path_count() == 1)
        .filter(|_| completed.core.frontier_loop_rules.is_empty())
        .map(|paths| {
            Arc::new((
                paths.candidate_at(0).expect("one checked outcome").clone(),
                effect_leaf.facts.clone(),
                true,
            ))
        });
    completed.presentation.effect_leaf = Some(Arc::new(effect_leaf));
    Ok(CheckedStatementStep {
        execution: completed,
        facts,
        added_facts: successor.introduced_facts,
    })
}
