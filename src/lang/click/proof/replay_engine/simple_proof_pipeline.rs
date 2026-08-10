//! Construction and independent replay of typed simple proofs.

use super::*;

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) struct InternalPlanReplay {
    pub(in crate::lang::click::proof) context: ProofReplayContext,
    pub(in crate::lang::click::proof) construction: SimpleProofBuilder,
}

pub(in crate::lang::click::proof) fn replay_internal_plan(
    mut context: ProofReplayContext,
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
    certificate: &InternalProofPlan,
) -> Result<InternalPlanReplay, ClickError> {
    context.replay.planned_statement_transitions = certificate.statement_transitions().to_vec();
    let mut construction = std::mem::take(&mut context.replay.simple_proof_builder);
    let mut context_slot = Some(context);
    for (operation_index, operation) in certificate.operations().iter().cloned().enumerate() {
        let current = context_slot
            .take()
            .expect("internal plan replay context is restored after every operation");
        let result = match operation {
            InternalProofOperation::Surface(tactic) => {
                let surface = SimpleProof::from_proof_tactics(std::slice::from_ref(&tactic))
                    .map_err(|error| {
                        ClickError::new(format!(
                            "surface operation in internal plan is not a simple proof: {error:?}"
                        ))
                    })?;
                for step in surface.steps() {
                    construction.push_step(step.clone());
                }
                let indexed = IndexedTactic {
                    index: tactic_index,
                    source_index,
                    tactic,
                };
                let replayed = SUPPRESS_SIMPLE_PROOF_CONSTRUCTION.with(|suppressed| {
                    let previous = suppressed.replace(true);
                    let result = replay_linear_tactics(
                        current,
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
                        std::slice::from_ref(&indexed),
                    );
                    suppressed.set(previous);
                    result
                });
                replayed.map(|replayed| {
                    debug_assert!(replayed.replay.simple_proof_builder.steps.is_empty());
                    context_slot = Some(replayed);
                })
            }
            operation => {
                let ProofReplayContext {
                    mut state,
                    pure_facts: mut requirement_pure_facts,
                    mut replay,
                    branch_path,
                } = current;
                let replayed = replay_internal_operation(
                    &operation,
                    &mut replay,
                    &mut construction,
                    &mut state,
                    &mut requirement_pure_facts,
                    &branch_path,
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
                );
                context_slot = Some(ProofReplayContext {
                    state,
                    pure_facts: requirement_pure_facts,
                    replay,
                    branch_path,
                });
                replayed
            }
        };
        result.map_err(|error| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: internal plan operation {operation_index} failed: {}",
                error.message()
            ))
        })?;
    }
    let context = context_slot.expect("internal plan replay retains its final context");
    Ok(InternalPlanReplay {
        context,
        construction,
    })
}

fn build_simple_proof_from_internal_plan(
    context: &ProofReplayContext,
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
    plan: &InternalProofPlan,
) -> Result<(SimpleProof, ProofReplayContext, SimpleProofBuilder), ClickError> {
    let mut lowering_context = context.clone();
    let steps = if plan.is_certified_frame() {
        surface_branch_skeleton(&context.replay.simple_proof_builder.steps)
    } else {
        Vec::new()
    };
    lowering_context.replay.simple_proof_builder = SimpleProofBuilder {
        steps,
        last_step_entry: context.replay.simple_proof_builder.last_step_entry.clone(),
        ..SimpleProofBuilder::default()
    };
    let lowered = replay_internal_plan(
        lowering_context,
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
        plan,
    )?;
    if let Some(blocker) = &lowered.construction.blocker {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: smart search found an internal plan, but `SimpleProof` construction failed: {blocker}"
        )));
    }
    if lowered.construction.steps.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: smart search found an internal plan, but `SimpleProof` construction produced no steps"
        )));
    }
    let certificate = SimpleProof::from_steps(lowered.construction.steps.clone());
    Ok((certificate, lowered.context, lowered.construction))
}

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
    let completed = SUPPRESS_TACTIC_EXPANSION_CAPTURE.with(|suppressed| {
        let previous = suppressed.replace(true);
        let result = execute_internal_proof(
            &program,
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
        );
        suppressed.set(previous);
        result
    })?;
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
    plan: &InternalProofPlan,
) -> Result<ProofReplayContext, ClickError> {
    let outer_simple_proof = context.replay.simple_proof_builder.clone();
    let (proof, mut internal_result, mut construction) = build_simple_proof_from_internal_plan(
        &context,
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
        plan,
    )?;
    let mut verified_result = replay_simple_proof(
        context.clone(),
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
    let last_step_entry = construction.last_step_entry.clone();
    internal_result.replay.simple_proof_builder = outer_simple_proof;
    let replaces_existing_branch = plan.is_certified_frame()
        && matches!(proof.steps(), [SimpleProofStep::If { .. }])
        && internal_result
            .replay
            .simple_proof_builder
            .steps
            .iter()
            .any(|step| matches!(step, SimpleProofStep::If { .. }));
    if replaces_existing_branch {
        let branch_index = internal_result
            .replay
            .simple_proof_builder
            .steps
            .iter()
            .rposition(|step| matches!(step, SimpleProofStep::If { .. }))
            .expect("an existing surface branch was checked above");
        internal_result
            .replay
            .simple_proof_builder
            .steps
            .truncate(branch_index);
        internal_result
            .replay
            .simple_proof_builder
            .steps
            .extend(proof.steps().iter().cloned());
    } else {
        for step in proof.steps() {
            internal_result
                .replay
                .simple_proof_builder
                .push_step(step.clone());
        }
    }
    construction.last_step_entry = last_step_entry;
    internal_result.replay.simple_proof_builder.last_step_entry = construction.last_step_entry;
    verified_result.replay.simple_proof_builder = internal_result.replay.simple_proof_builder;
    Ok(verified_result)
}
