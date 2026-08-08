use super::*;

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn replay_internal_plan(
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
    certificate: &ProofReplayPlan,
) -> Result<ProofReplayContext, ClickError> {
    let tactics = certificate
        .tactics()
        .iter()
        .cloned()
        .map(|tactic| IndexedTactic {
            index: tactic_index,
            source_index,
            tactic,
        })
        .collect::<Vec<_>>();
    replay_linear_tactics(
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
        &tactics,
    )
}

fn lower_internal_plan_to_surface_certificate(
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
    plan: &ProofReplayPlan,
) -> Result<(TacticCertificate, ProofReplayContext), ClickError> {
    let mut lowering_context = context.clone();
    let tactics = matches!(plan.tactics(), [ProofTactic::CertifiedFrame(_)])
        .then(|| surface_branch_skeleton(&context.replay.surface_replay.tactics))
        .unwrap_or_default();
    lowering_context.replay.surface_replay = SurfaceReplay {
        tactics,
        last_step_entry: context.replay.surface_replay.last_step_entry.clone(),
        ..SurfaceReplay::default()
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
    if let Some(blocker) = &lowered.replay.surface_replay.blocker {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: smart tactic could not produce a surface certificate: {blocker}"
        )));
    }
    if lowered.replay.surface_replay.tactics.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: smart tactic produced an empty surface certificate"
        )));
    }
    let certificate =
        TacticCertificate::from_proof_tactics(&lowered.replay.surface_replay.tactics).map_err(
            |error| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: smart tactic produced a non-surface certificate at {:?}: {:?}",
                error.path(),
                error.tactic_class()
            ))
            },
        )?;
    Ok((certificate, lowered))
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn verify_surface_certificate(
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
    certificate: &TacticCertificate,
) -> Result<ProofReplayContext, ClickError> {
    let enclosing_branch_path = context.branch_path.clone();
    let enclosing_case_assumptions = context.replay.case_assumptions.clone();
    let program =
        build_generated_certificate_proof(certificate.tactics(), claim_label, source_index)?;
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
            "`{claim_label}` tactic {tactic_index}: surface certificate at source tactic {source_index} produced no replay contexts"
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
            "`{claim_label}` tactic {tactic_index}: branched surface certificate at source tactic {source_index} did not finish every branch at function exit"
        )));
    }
    let execution_start_state = completed[0]
        .replay
        .frontier
        .execution_start_state
        .clone()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: branched surface certificate has no execution start state"
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
pub(in crate::lang::click::proof) fn replay_smart_plan(
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
    plan: &ProofReplayPlan,
) -> Result<ProofReplayContext, ClickError> {
    let outer_surface_replay = context.replay.surface_replay.clone();
    let (certificate, mut internal_result) = lower_internal_plan_to_surface_certificate(
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
    let mut verified_result = verify_surface_certificate(
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
        &certificate,
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: generated surface certificate failed replay:\n{}\n{}",
            format_tactic_certificate(&certificate),
            error.message()
        ))
    })?;
    let last_step_entry = internal_result
        .replay
        .surface_replay
        .last_step_entry
        .clone();
    internal_result.replay.surface_replay = outer_surface_replay;
    let replaces_existing_branch = matches!(plan.tactics(), [ProofTactic::CertifiedFrame(_)])
        && matches!(certificate.tactics(), [ProofTactic::If(_)])
        && internal_result
            .replay
            .surface_replay
            .tactics
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::If(_)));
    if replaces_existing_branch {
        let branch_index = internal_result
            .replay
            .surface_replay
            .tactics
            .iter()
            .rposition(|tactic| matches!(tactic, ProofTactic::If(_)))
            .expect("an existing surface branch was checked above");
        internal_result
            .replay
            .surface_replay
            .tactics
            .truncate(branch_index);
        internal_result
            .replay
            .surface_replay
            .tactics
            .extend(certificate.tactics().iter().cloned());
    } else {
        for tactic in certificate.tactics() {
            internal_result.replay.surface_replay.push(tactic.clone());
        }
    }
    internal_result.replay.surface_replay.last_step_entry = last_step_entry;
    verified_result.replay.surface_replay = internal_result.replay.surface_replay;
    Ok(verified_result)
}
