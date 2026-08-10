//! Completion and independent replay of typed simple proofs.
//!
//! A smart tactic's search constructs its [`SimpleProof`] directly, step by
//! step, while it commits to each move (see
//! `construct_simple_step_for_planned_operation`). This module receives that
//! constructed proof, independently replays it through the ordinary simple
//! tactic executor, and merges the steps into the enclosing proof's surface
//! record. There is no intermediate plan language or plan replay: the
//! independent replay of the `SimpleProof` is the only re-execution, and its
//! resulting context is the smart tactic's result.

use super::*;

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn replay_simple_proof(
    context: ProofReplayContext,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    tactic_index: usize,
    source_index: usize,
    proof: &SimpleProof,
) -> Result<ProofReplayContext, ClickError> {
    let enclosing_branch_path = context.branch_path.clone();
    let enclosing_case_assumptions = context.replay.case_assumptions.clone();
    let program =
        build_generated_certificate_proof(&proof.to_proof_tactics(), claim_label, source_index)?;
    // The independent replay is a detached check of the constructed proof;
    // its tactic indices are certificate-local, so no expansion capture is
    // routed into it.
    let completed = execute_internal_proof(
        &program,
        context,
        None,
        function_block,
        parsed_function,
        claims,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        function,
        arguments,
    )?;
    merge_surface_certificate_contexts(
        completed,
        function,
        arguments,
        claim_label,
        tactic_index,
        source_index,
        &enclosing_branch_path,
        &enclosing_case_assumptions,
    )
}

fn merge_surface_certificate_contexts(
    mut completed: Vec<ProofReplayContext>,
    function: &CFunction,
    arguments: &[CExpression],
    claim_label: &str,
    tactic_index: usize,
    source_index: usize,
    enclosing_branch_path: &[String],
    enclosing_case_assumptions: &[ReplayCaseAssumption],
) -> Result<ProofReplayContext, ClickError> {
    if completed.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `SimpleProof` at source tactic {source_index} produced no replay contexts"
        )));
    }
    if completed.len() == 1 {
        return Ok(completed.pop().expect("one completed context exists"));
    }
    if completed
        .iter()
        .any(|context| !context.replay.is_at_function_exit())
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: branched `SimpleProof` at source tactic {source_index} did not finish every branch at function exit"
        )));
    }
    let execution_start_state = completed[0]
        .replay
        .frontier
        .execution_start_state
        .clone()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: branched `SimpleProof` has no execution start state"
            ))
        })?;
    let mut common_pure_facts = completed[0].pure_facts.clone();
    common_pure_facts.retain(|fact| {
        completed
            .iter()
            .skip(1)
            .all(|context| context.pure_facts.contains(fact))
    });
    let mut common_program_points = completed[0].replay.program_point_states.clone();
    common_program_points.retain(|point, point_state| {
        completed
            .iter()
            .skip(1)
            .all(|context| context.replay.program_point_states.get(point) == Some(point_state))
    });
    let mut paths = Vec::new();
    for context in &completed {
        let execution = context
            .replay
            .execution()
            .expect("every completed surface branch is at function exit");
        for path in execution.paths() {
            let mut facts = path.execution_facts();
            for fact in &context.pure_facts {
                let fact = ExecutionPureFact::new(fact.clone());
                if !facts.contains(&fact) {
                    facts.push(fact);
                }
            }
            let obligations = path.obligations().to_vec();
            if !paths
                .iter()
                .any(|(existing_outcome, existing_facts, existing_obligations)| {
                    existing_outcome == path.outcome()
                        && existing_facts == &facts
                        && existing_obligations == &obligations
                })
            {
                paths.push((path.outcome().clone(), facts, obligations));
            }
        }
    }
    let execution = c_function_execution_candidates_from_outcomes(
        execution_start_state.clone(),
        function.clone(),
        arguments.to_vec(),
        paths,
    );
    let mut merged = completed.remove(0);
    merged.replay.program_point_states = common_program_points;
    merged.replay.frontier.point = ProofExecutionPoint::FunctionExit { execution };
    merged.replay.case_assumptions = enclosing_case_assumptions.to_vec();
    merged.state = execution_start_state;
    merged.pure_facts = common_pure_facts;
    merged.branch_path = enclosing_branch_path.to_vec();
    Ok(merged)
}

/// Checks a smart tactic's constructed [`SimpleProof`] by independent replay
/// and merges its steps into the enclosing proof's surface record.
///
/// `construction` is the builder the smart search filled while committing to
/// its moves. `certified_frame` marks a contextual `frame` certificate, whose
/// synthesized branch structure replaces an existing surface branch instead of
/// being appended inside it.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn complete_smart_tactic(
    context: ProofReplayContext,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    tactic_index: usize,
    source_index: usize,
    construction: SimpleProofBuilder,
    certified_frame: bool,
) -> Result<ProofReplayContext, ClickError> {
    if let Some(blocker) = &construction.blocker {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: smart search found an internal plan, but `SimpleProof` construction failed: {blocker}"
        )));
    }
    if construction.steps.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: smart search found an internal plan, but `SimpleProof` construction produced no steps"
        )));
    }
    let proof = SimpleProof::from_steps(construction.steps.clone());
    let outer_simple_proof = context.replay.simple_proof_builder.clone();
    let mut verified_result = replay_simple_proof(
        context,
        function_block,
        parsed_function,
        claims,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        function,
        arguments,
        tactic_index,
        source_index,
        &proof,
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: constructed `SimpleProof` failed independent replay:\n{}\n{}",
            format_simple_proof(&proof),
            error.message()
        ))
    })?;
    let mut merged = outer_simple_proof;
    let replaces_existing_branch = certified_frame
        && matches!(proof.steps(), [SimpleProofStep::If { .. }])
        && merged
            .steps
            .iter()
            .any(|step| matches!(step, SimpleProofStep::If { .. }));
    if replaces_existing_branch {
        merged.replace_trailing_branch(proof.steps().to_vec());
    } else {
        for step in proof.steps() {
            merged.push_step(step.clone());
        }
    }
    merged.last_step_entry = construction.last_step_entry;
    verified_result.replay.simple_proof_builder = merged;
    Ok(verified_result)
}
