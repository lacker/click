use super::*;

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn verify_loop_initialization_pure_proof(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    loop_index: usize,
    proof: &SourceProof,
    clause: &StructuralClause,
    context: &ExecutionProofContext,
    invariant_checks: &[CLoopInvariantCheck],
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<ProofCertificate, ClickError> {
    let legacy_site = ProofSite::LoopPhase {
        function_name: environment.function_block.signature().name().to_string(),
        loop_index,
        phase: "initialize",
    };
    let (claim_label, initialize_source_index, initialize_site) = environment
        .frontier_loop_source
        .map(|source| {
            (
                source.claim_label.clone(),
                source
                    .initialize_source_index
                    .unwrap_or(source.loop_source_index),
                source
                    .proof_site
                    .clone()
                    .unwrap_or_else(|| legacy_site.clone()),
            )
        })
        .unwrap_or_else(|| (legacy_site.description(), 0, legacy_site));
    let mut program_point_states = context.program_point_states.clone();
    program_point_states.insert(
        ProgramPointRef {
            region: CodeRegionRef::Loop(loop_index),
            kind: ProgramPointKind::Entry,
        },
        context.state.clone(),
    );
    for label in environment
        .function_block
        .structural_clauses()
        .iter()
        .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
        .filter_map(StructuralClause::label)
    {
        program_point_states.insert(
            ProgramPointRef {
                region: CodeRegionRef::Label(label.to_string()),
                kind: ProgramPointKind::Entry,
            },
            context.state.clone(),
        );
    }
    let invariant_items = clause
        .items()
        .iter()
        .filter(|item| item.kind() == StructuralItemKind::Invariant)
        .collect::<Vec<_>>();
    let initialization_surface_propositions =
        std::cell::RefCell::new(context.surface_propositions.clone());
    // Generated initialization steps belong to the explicit phase tactic when
    // one exists, or to the enclosing `loop` keyword for an omitted phase.
    // Computing the source statement is only worth it when timings are read.
    let timings_enabled = crate::instrumentation::enabled();
    let initialize_statement_index = if timings_enabled {
        SourceExecutionLayout::new(environment.parsed_function.body())
            .loop_body_entry(loop_index)
            .unwrap_or(0)
    } else {
        0
    };
    let entry_obligations = c_loop_invariant_obligations_at_entry(
        &context.state,
        invariant_checks,
        &assumptions_from_propositions(&context.pure_facts),
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
    // Expansion lowers a shared initialize proof to optional predicate
    // unfolds followed by one explicit `have` per invariant.  Recognize that
    // surface-certificate shape on the next verification pass and replay it
    // directly.  Sending it back through the per-invariant planner would
    // treat the whole certificate as the proof of every individual `have`,
    // recursively duplicate it, and can make a valid first expansion fail.
    let source_certificate = proof.tactics().and_then(|tactics| {
        let invariant_start = tactics.len().checked_sub(invariant_items.len())?;
        let prefix_is_explicit = tactics[..invariant_start]
            .iter()
            .all(|tactic| matches!(tactic, ProofTactic::UnfoldPredicate(_)));
        let invariants_match =
            tactics[invariant_start..]
                .iter()
                .zip(&invariant_items)
                .all(|(tactic, item)| {
                    matches!(
                        tactic,
                        ProofTactic::Have(have)
                            if item.proposition() == Some(&have.proposition)
                    )
                });
        (prefix_is_explicit && invariants_match)
            .then(|| ProofCertificate::from_proof_tactics(tactics).ok())
            .flatten()
    });
    let (certificate, available) = pure_goal_proof_certificate_gateway_with_checked_result(
        &claim_label,
        || {
            if let Some(certificate) = source_certificate {
                return Ok((certificate, None));
            }
            let mut planning_available = context.pure_facts.clone();
            let mut tactics = Vec::new();
            let mut all_invariants_checked = true;
            for (invariant_index, item) in invariant_items.iter().enumerate() {
                let proposition = item
                    .proposition()
                    .expect("invariant region proof item should contain a proposition");
                let invariant_claim_label =
                    format!("{claim_label} (loop {loop_index} invariant {invariant_index} entry)");
                let obligation_context =
                    format!("loop {loop_index} invariant {invariant_index} entry");
                let expected_goal = entry_obligations
                    .iter()
                    .find(|obligation| obligation.context() == Some(&obligation_context))
                    .map(|obligation| obligation.proposition().clone());
                let planning_assumptions = assumptions_from_propositions(&planning_available);
                let expected_goal = expected_goal.map(|mut expected_goal| {
                    while let Proposition::Implies(antecedent, body) = &expected_goal {
                        if !planning_assumptions.proves(antecedent) {
                            break;
                        }
                        expected_goal = body.as_ref().clone();
                    }
                    expected_goal
                });
                // Planning an invariant's entry proof is proof search, not
                // replay. Classify it by the `by` clause the search is
                // discharging, exactly as if it were written as a `have`.
                let planned_step = timings_enabled.then(|| {
                    ProofTactic::Have(ProofHave {
                        proposition: proposition.clone(),
                        proof: proof.clone(),
                    })
                });
                let _timing = planned_step.as_ref().and_then(|planned_step| {
                    TacticTiming::named_for_tactic(
                        &claim_label,
                        "plan_invariant_entry",
                        planned_step,
                        invariant_index,
                        initialize_source_index,
                        initialize_statement_index,
                    )
                });
                let plan = |expansion_capture: Option<&mut ExpansionCapture>| {
                    plan_point_pure_goal_certificate(
                        expansion_capture,
                        &initialize_site,
                        proposition,
                        proof,
                        &invariant_claim_label,
                        invariant_index,
                        &planning_available,
                        environment.parsed_function.parameters(),
                        environment.arguments,
                        environment.initial_state,
                        &context.state,
                        &program_point_states,
                        environment.predicate_environment,
                        environment.click_function_environment,
                        &context.surface_propositions,
                        expected_goal.as_ref(),
                        environment.theorem_environment,
                    )
                };
                // Nested frontier-loop phase tactics use absolute source
                // indices in the enclosing proof. The per-invariant pure
                // planner sees only the local phase script, so route no
                // expansion capture into it there; the phase merger below
                // retains the expansion at the absolute source site.
                let direct_plan = if environment.frontier_loop_source.is_some() {
                    plan(None)
                } else {
                    plan(expansion_capture.as_deref_mut())
                }?;
                let PlannedPointPureGoal {
                    fact: planned_fact,
                    certificate: planned_certificate,
                    certificate_already_checked,
                } = direct_plan;
                all_invariants_checked &= certificate_already_checked;
                initialization_surface_propositions
                    .borrow_mut()
                    .record_lowering(proposition, &planned_fact)?;
                tactics.push(ProofTactic::Have(ProofHave {
                    proposition: proposition.clone(),
                    proof: SourceProof::Script(planned_certificate.to_proof_tactics().to_vec()),
                }));
                if !planning_available.contains(&planned_fact) {
                    planning_available.push(planned_fact);
                }
            }
            let certificate = ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` produced an invalid initialization certificate: {error:?}"
                ))
            })?;
            Ok((
                certificate,
                all_invariants_checked.then_some(planning_available),
            ))
        },
        |certificate| {
            if certificate.to_proof_tactics().len() < invariant_items.len() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` certificate has only {} steps for {} invariants",
                    certificate.to_proof_tactics().len(),
                    invariant_items.len()
                )));
            }
            let mut replay_available = context.pure_facts.clone();
            let invariant_start = certificate.to_proof_tactics().len() - invariant_items.len();
            for (certificate_index, tactic) in certificate.to_proof_tactics().iter().enumerate() {
                // Certificate replay for the initialize phase never reaches
                // `replay_linear_tactics`, so time each step here in the same
                // format and let `source_tactic_class` classify it.
                let _timing = TacticTiming::new(
                    &claim_label,
                    certificate_index,
                    initialize_source_index,
                    tactic,
                    initialize_statement_index,
                );
                if certificate_index < invariant_start
                    && let ProofTactic::UnfoldPredicate(name) = tactic
                {
                    if environment.predicate_environment.get(name).is_none() {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` certificate step {certificate_index} names unknown predicate `{name}`"
                        )));
                    }
                    replay_available = unfold_available_predicate_facts(
                        environment.predicate_environment,
                        environment.click_function_environment,
                        std::slice::from_ref(name),
                        &replay_available,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` certificate step {certificate_index}: {message}"
                        ))
                    })?;
                    continue;
                }
                let ProofTactic::Have(have) = tactic else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` certificate step {certificate_index} is not a pure `have`"
                    )));
                };
                let invariant_index = certificate_index.checked_sub(invariant_start);
                if let Some(invariant_index) = invariant_index {
                    let proposition = invariant_items[invariant_index]
                        .proposition()
                        .expect("invariant region proof item should contain a proposition");
                    if &have.proposition != proposition {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` certificate step {certificate_index} changed invariant {invariant_index}"
                        )));
                    }
                }
                let step_claim_label = invariant_index
                    .map(|invariant_index| {
                        format!(
                            "{claim_label} (loop {loop_index} invariant {invariant_index} entry)"
                        )
                    })
                    .unwrap_or_else(|| format!("{claim_label} prerequisite {certificate_index}"));
                let surface_propositions = initialization_surface_propositions.borrow();
                let fact = prove_pure_proposition_at_point(
                    &have.proposition,
                    surface_propositions.unique_kernel(&have.proposition),
                    &have.proof,
                    "initialize",
                    environment.theorem_environment,
                    &step_claim_label,
                    certificate_index,
                    &replay_available,
                    &[],
                    environment.parsed_function.parameters(),
                    environment.arguments,
                    environment.initial_state,
                    &context.state,
                    None,
                    &program_point_states,
                    Some(&surface_propositions),
                    environment.predicate_environment,
                    environment.click_function_environment,
                    environment.function_block.requires(),
                    None,
                )?;
                if !replay_available.contains(&fact) {
                    replay_available.push(fact);
                }
            }
            Ok(replay_available)
        },
    )?;
    let assumptions = assumptions_from_propositions(&available);
    c_loop_invariants_hold_at_entry(&context.state, invariant_checks, &assumptions)
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
    Ok(certificate)
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn plan_automatic_loop_preservation_body(
    loop_index: usize,
    preservation: &crate::kernel::CLoopPreservationContext,
    pure_facts: &[Proposition],
    body: &CStatement,
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<ProofCertificate, ClickError> {
    let claim_label = environment.frontier_loop_source.map_or_else(
        || {
            format!(
                "{}.loop({loop_index}).preserve",
                environment.function_block.signature().name()
            )
        },
        |source| source.claim_label.clone(),
    );
    let source_layout = SourceExecutionLayout::new(environment.parsed_function.body());
    let loop_body_statement_index = source_layout.loop_body_entry(loop_index).ok_or_else(|| {
        ClickError::new(format!("`{claim_label}` has no source loop({loop_index})"))
    })?;
    let mut replay = TacticReplayState {
        proof_site: environment
            .frontier_loop_source
            .and_then(|source| source.proof_site.clone()),
        frontier: ExecutionFrontier {
            point: ProofExecutionPoint::StatementEntry {
                remaining: body.clone().into(),
            },
            region: ExecutionRegionKind::LoopBody,
            execution_start_state: Some(preservation.state().clone()),
            next_statement_index: loop_body_statement_index,
            ..ExecutionFrontier::default()
        },
        source_layout,
        region_proof: true,
        loop_invariant_region: true,
        function_entry_state: Some(environment.initial_state.clone()),
        surface_propositions: environment.surface_propositions.clone(),
        ..TacticReplayState::default()
    };
    record_statement_program_point_state(
        &mut replay,
        environment.function_block,
        loop_body_statement_index,
        ProgramPointKind::Entry,
        preservation.state().clone(),
    );
    record_loop_program_point_state(
        &mut replay,
        environment.function_block,
        loop_index,
        ProgramPointKind::Entry,
        preservation.loop_entry_state().clone(),
    );
    let mut pending = vec![ProofReplayContext {
        state: preservation.state().clone(),
        pure_facts: pure_facts.to_vec(),
        replay: Box::new(replay),
        branch_path: PersistentSequence::default(),
    }];
    let mut completed = Vec::new();
    let mut steps = 0;
    while let Some(context) = pending.pop() {
        if context.replay.is_at_region_boundary() {
            completed.push(context);
            continue;
        }
        if steps == BOUNDED_EXECUTE_STEP_LIMIT {
            return Err(ClickError::new(format!(
                "`{claim_label}` automatic preservation exhausted its {BOUNDED_EXECUTE_STEP_LIMIT}-step budget"
            )));
        }
        steps += 1;
        let is_branch = context
            .replay
            .source_layout
            .statement(context.replay.frontier.next_statement_index)
            .is_some_and(|region| matches!(region.kind, SourceStatementKind::If { .. }));
        let candidates = if is_branch {
            let ProofExecutionPoint::StatementEntry { remaining } = &context.replay.frontier.point
            else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` automatic preservation branch is not at a statement entry"
                )));
            };
            let (source_statement, _) =
                split_next_source_operation(remaining).map_err(ClickError::new)?;
            let CStatement::If { condition, .. } = source_statement else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` source branch does not match the lowered statement"
                )));
            };
            vec![ProofTactic::If(ProofIf {
                condition: surface_c_condition(&condition),
                then_tactics: vec![ProofTactic::SmartStep],
                else_tactics: vec![ProofTactic::SmartStep],
            })]
        } else {
            vec![ProofTactic::SmartStep]
        };
        let mut advanced = Vec::new();
        let mut errors = Vec::new();
        for tactic in candidates {
            let program = if let Some(source) = environment.frontier_loop_source {
                build_generated_certificate_proof(
                    std::slice::from_ref(&tactic),
                    &claim_label,
                    source.loop_source_index,
                )?
            } else {
                build_internal_proof(std::slice::from_ref(&tactic), &claim_label)?
            };
            match execute_internal_proof(
                &program,
                context.clone(),
                None,
                environment.function_block,
                environment.parsed_function,
                &[],
                &claim_label,
                environment.function_environment,
                environment.predicate_environment,
                environment.click_function_environment,
                environment.resource_environment,
                environment.theorem_environment,
                environment.function,
                environment.arguments,
            ) {
                Ok(contexts) => advanced.extend(contexts),
                Err(error) => errors.push(error),
            }
        }
        if advanced.is_empty() {
            return Err(errors.pop().unwrap_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` automatic preservation could not advance the loop body"
                ))
            }));
        }
        pending.extend(advanced);
    }
    let mut paths = Vec::new();
    for context in completed {
        if let Some(blocker) = &context.replay.proof_certificate_builder.blocker {
            return Err(ClickError::new(format!(
                "`{claim_label}` automatic preservation could not lower a body step: {blocker}"
            )));
        }
        let case_path = context
            .replay
            .case_assumptions
            .iter()
            .map(|choice| ProofCaseChoice {
                condition: choice.condition.clone(),
                value: choice.value,
            })
            .collect::<Vec<_>>();
        let surface_tactics =
            ProofCertificate::from_steps(context.replay.proof_certificate_builder.steps.clone())
                .to_proof_tactics();
        let certificate =
            certificate_leaf_for_case_path(&claim_label, &surface_tactics, &case_path)?;
        paths.push(PathCertificate {
            case_path,
            certificate,
        });
    }
    merge_path_aligned_certificates(&claim_label, paths)
}

fn loop_effect_linear_step_supported(step: &SimpleProofStep) -> bool {
    match step {
        SimpleProofStep::Mark(_)
        | SimpleProofStep::Step
        | SimpleProofStep::StepUsing(_)
        | SimpleProofStep::ApplyTheoremUsing { .. }
        | SimpleProofStep::TransportUsing { .. }
        | SimpleProofStep::UnfoldPredicate(_)
        | SimpleProofStep::UnfoldResource(_)
        | SimpleProofStep::FoldResource(_)
        | SimpleProofStep::ObserveResource(_)
        | SimpleProofStep::Choose(_)
        | SimpleProofStep::Witness(_)
        | SimpleProofStep::InstantiateUsing { .. }
        | SimpleProofStep::Extract(_)
        | SimpleProofStep::Rewrite(_)
        | SimpleProofStep::Assumption
        | SimpleProofStep::Normalize
        | SimpleProofStep::Intro
        | SimpleProofStep::Split
        | SimpleProofStep::Left
        | SimpleProofStep::Right
        | SimpleProofStep::Enumerate
        | SimpleProofStep::Contradiction(_)
        | SimpleProofStep::CloseInvariants
        | SimpleProofStep::FrameUsing { .. } => true,
        SimpleProofStep::Have { proof, .. } => {
            Proof::supports_linear_source(&SourceProof::Script(proof.to_proof_tactics()))
        }
        SimpleProofStep::Induct { .. }
        | SimpleProofStep::ApplyInduction { .. }
        | SimpleProofStep::CloseInduction
        | SimpleProofStep::Open { .. }
        | SimpleProofStep::If { .. }
        | SimpleProofStep::Cases { .. }
        | SimpleProofStep::Branch { .. }
        | SimpleProofStep::Loop(_) => false,
    }
}

fn loop_effect_scope_step_supported(step: &SimpleProofStep) -> bool {
    match step {
        SimpleProofStep::Open { proof, .. } => {
            proof.steps().iter().all(loop_effect_scope_step_supported)
        }
        step => loop_effect_linear_step_supported(step),
    }
}

fn loop_effect_open_body_supported(certificate: &ProofCertificate) -> bool {
    loop_effect_open_body_analysis(certificate).is_some()
}

/// Returns whether this supported body contains an execution `if` or logical
/// `cases` tree.
/// Validation and branch discovery share this linear walk so deep leading
/// scopes and recursively nested arms are not rescanned once per level.
fn loop_effect_open_body_analysis(certificate: &ProofCertificate) -> Option<bool> {
    let mut contains_branch = false;
    for (index, step) in certificate.steps().iter().enumerate() {
        let step_contains_branch = match step {
            // The branch closes every leading open representation
            // independently on each terminal arm, so it must own the
            // remainder of every enclosing scope. Nested execution branches
            // recurse through this same typed tree driver; logical branches
            // inside `have` use the proposition driver.
            SimpleProofStep::If {
                then_proof,
                else_proof,
                ..
            }
            | SimpleProofStep::Cases {
                left_proof: then_proof,
                right_proof: else_proof,
                ..
            } => {
                if index + 1 != certificate.steps().len()
                    || loop_effect_open_body_analysis(then_proof).is_none()
                    || loop_effect_open_body_analysis(else_proof).is_none()
                {
                    return None;
                }
                true
            }
            SimpleProofStep::Open { proof, .. } => {
                let nested_contains_branch = loop_effect_open_body_analysis(proof)?;
                if nested_contains_branch && index + 1 != certificate.steps().len() {
                    return None;
                }
                nested_contains_branch
            }
            step => {
                if !loop_effect_scope_step_supported(step) {
                    return None;
                }
                false
            }
        };
        contains_branch |= step_contains_branch;
    }
    Some(contains_branch)
}

fn loop_effect_open_branch_path(certificate: &ProofCertificate) -> Option<Vec<usize>> {
    let mut path = Vec::new();
    loop_effect_open_branch_path_into(certificate, &mut path).then_some(path)
}

fn loop_effect_open_branch_path_into(
    certificate: &ProofCertificate,
    path: &mut Vec<usize>,
) -> bool {
    for (index, step) in certificate.steps().iter().enumerate() {
        match step {
            SimpleProofStep::If { .. } | SimpleProofStep::Cases { .. } => {
                path.push(index);
                return true;
            }
            SimpleProofStep::Open { proof, .. } => {
                path.push(index);
                if loop_effect_open_branch_path_into(proof, path) {
                    return true;
                }
                path.pop();
            }
            _ => {}
        }
    }
    false
}

fn loop_effect_step_source_width(step: &SimpleProofStep) -> usize {
    match step {
        // Resource scopes participate in the outer source-index sequence;
        // proposition-scope bodies have their own proof site and therefore,
        // like `source_tactic_width`, count only the enclosing `have` here.
        SimpleProofStep::Open { proof, .. } => {
            1 + proof
                .steps()
                .iter()
                .map(loop_effect_step_source_width)
                .sum::<usize>()
        }
        SimpleProofStep::If {
            then_proof,
            else_proof,
            ..
        } => {
            1 + then_proof
                .steps()
                .iter()
                .map(loop_effect_step_source_width)
                .sum::<usize>()
                + else_proof
                    .steps()
                    .iter()
                    .map(loop_effect_step_source_width)
                    .sum::<usize>()
        }
        SimpleProofStep::Cases {
            left_proof,
            right_proof,
            ..
        } => {
            1 + left_proof
                .steps()
                .iter()
                .map(loop_effect_step_source_width)
                .sum::<usize>()
                + right_proof
                    .steps()
                    .iter()
                    .map(loop_effect_step_source_width)
                    .sum::<usize>()
        }
        _ => 1,
    }
}

fn select_loop_effect_path_prefix(
    claim_label: &str,
    tactics: &[ProofTactic],
    case_path: &[ProofCaseChoice],
) -> Result<ProofCertificate, ClickError> {
    let mut selected = tactics;
    let mut next_case = 0;
    while let [ProofTactic::If(proof_if)] = selected {
        let Some(choice) = case_path.get(next_case) else {
            break;
        };
        if choice.condition != proof_if.condition {
            break;
        }
        selected = if choice.value {
            &proof_if.then_tactics
        } else {
            &proof_if.else_tactics
        };
        next_case += 1;
    }
    ProofCertificate::from_proof_tactics(selected).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` selected an invalid structural-effect certificate: {error:?}"
        ))
    })
}

fn apply_loop_effect_scope_certificate_at<'a>(
    mut scope: ProofScope<'a>,
    certificate: &ProofCertificate,
    tactic_index_offset: usize,
    source_index_offset: usize,
) -> Result<ProofScope<'a>, ClickError> {
    let mut source_index = source_index_offset;
    for (local_index, step) in certificate.steps().iter().enumerate() {
        let tactic_index = tactic_index_offset + local_index;
        match step {
            SimpleProofStep::Open { resource, proof } => {
                let nested = scope.begin_open(resource.clone(), source_index)?;
                let nested = apply_loop_effect_scope_certificate_at(
                    nested,
                    proof,
                    tactic_index + 1,
                    source_index + 1,
                )?;
                scope = scope.join_nested(nested)?;
            }
            SimpleProofStep::Have {
                proposition,
                proof: body,
            } => {
                let nested = scope.begin_have(proposition.clone())?;
                let tactics = body.to_proof_tactics();
                let nested = nested
                    .try_authoritative_linear_script(&tactics)?
                    .ok_or_else(|| {
                        ClickError::new(
                            "loop-effect `have` body was admitted without a checked Proof driver",
                        )
                    })?;
                scope = scope.join_nested(nested)?;
            }
            step => {
                scope = scope.apply_step_at(step.clone(), tactic_index, source_index)?;
            }
        }
        source_index += loop_effect_step_source_width(step);
    }
    Ok(scope)
}

fn apply_loop_effect_open_certificate_at<'a>(
    scope: ProofScope<'a>,
    certificate: &ProofCertificate,
    tactic_index_offset: usize,
    source_index_offset: usize,
) -> Result<Proof<'a>, ClickError> {
    if let Some(branch_path) = loop_effect_open_branch_path(certificate) {
        return apply_loop_effect_open_chain_certificate_at(
            vec![scope],
            certificate,
            &branch_path,
            0,
            tactic_index_offset,
            source_index_offset,
        );
    }
    let scope = apply_loop_effect_scope_certificate_at(
        scope,
        certificate,
        tactic_index_offset,
        source_index_offset,
    )?;
    scope.join()
}

fn apply_loop_effect_open_chain_certificate_at<'a>(
    mut scopes: Vec<ProofScope<'a>>,
    certificate: &ProofCertificate,
    branch_path: &[usize],
    wrap_from: usize,
    tactic_index_offset: usize,
    source_index_offset: usize,
) -> Result<Proof<'a>, ClickError> {
    let Some((&branch_index, nested_branch_path)) = branch_path.split_first() else {
        return Err(ClickError::new(
            "a loop-effect open-chain driver requires a terminal `if` path",
        ));
    };
    let mut source_index = source_index_offset;
    for (local_index, step) in certificate.steps().iter().enumerate() {
        let tactic_index = tactic_index_offset + local_index;
        match step {
            SimpleProofStep::If {
                condition,
                then_proof,
                else_proof,
            } => {
                if local_index != branch_index
                    || !nested_branch_path.is_empty()
                    || local_index + 1 != certificate.steps().len()
                {
                    return Err(ClickError::new(
                        "a loop-effect `if` inside `open` must be the terminal scope operation",
                    ));
                }
                let then_source_index = source_index + 1;
                let else_source_index = then_source_index
                    + then_proof
                        .steps()
                        .iter()
                        .map(loop_effect_step_source_width)
                        .sum::<usize>();
                let current = scopes
                    .last()
                    .expect("an open-chain driver owns a leading scope")
                    .clone();
                let joined = ProofScope::apply_loop_effect_if(
                    &scopes,
                    current,
                    condition.clone(),
                    |then_scope| {
                        apply_loop_effect_arm_certificate_at(
                            scopes.clone(),
                            then_scope,
                            then_proof,
                            tactic_index + 1,
                            then_source_index,
                        )
                    },
                    |else_scope| {
                        apply_loop_effect_arm_certificate_at(
                            scopes.clone(),
                            else_scope,
                            else_proof,
                            tactic_index + 1,
                            else_source_index,
                        )
                    },
                )?;
                return ProofScope::retain_loop_effect_open_scopes(&scopes, wrap_from, joined);
            }
            SimpleProofStep::Cases {
                disjunction,
                left_proof,
                right_proof,
            } => {
                if local_index != branch_index
                    || !nested_branch_path.is_empty()
                    || local_index + 1 != certificate.steps().len()
                {
                    return Err(ClickError::new(
                        "loop-effect `cases` inside `open` must be the terminal scope operation",
                    ));
                }
                let left_source_index = source_index + 1;
                let right_source_index = left_source_index
                    + left_proof
                        .steps()
                        .iter()
                        .map(loop_effect_step_source_width)
                        .sum::<usize>();
                let current = scopes
                    .last()
                    .expect("an open-chain driver owns a leading scope")
                    .clone();
                let joined = ProofScope::apply_loop_effect_cases(
                    &scopes,
                    current,
                    disjunction.clone(),
                    |left_scope| {
                        apply_loop_effect_arm_certificate_at(
                            scopes.clone(),
                            left_scope,
                            left_proof,
                            tactic_index + 1,
                            left_source_index,
                        )
                    },
                    |right_scope| {
                        apply_loop_effect_arm_certificate_at(
                            scopes.clone(),
                            right_scope,
                            right_proof,
                            tactic_index + 1,
                            right_source_index,
                        )
                    },
                )?;
                return ProofScope::retain_loop_effect_open_scopes(&scopes, wrap_from, joined);
            }
            SimpleProofStep::Open { resource, proof } => {
                let current = scopes
                    .last()
                    .expect("an open-chain driver owns a leading scope")
                    .clone();
                let nested = current.begin_open(resource.clone(), source_index)?;
                if local_index == branch_index {
                    if local_index + 1 != certificate.steps().len() {
                        return Err(ClickError::new(
                            "a leading loop-effect `open` containing `if` must be terminal",
                        ));
                    }
                    scopes.push(nested);
                    return apply_loop_effect_open_chain_certificate_at(
                        scopes,
                        proof,
                        nested_branch_path,
                        wrap_from,
                        tactic_index + 1,
                        source_index + 1,
                    );
                }
                let nested = apply_loop_effect_scope_certificate_at(
                    nested,
                    proof,
                    tactic_index + 1,
                    source_index + 1,
                )?;
                *scopes
                    .last_mut()
                    .expect("an open-chain driver owns a leading scope") =
                    current.join_nested(nested)?;
            }
            SimpleProofStep::Have {
                proposition,
                proof: body,
            } => {
                let current = scopes
                    .last()
                    .expect("an open-chain driver owns a leading scope")
                    .clone();
                let nested = current.begin_have(proposition.clone())?;
                let tactics = body.to_proof_tactics();
                let nested = nested
                    .try_authoritative_linear_script(&tactics)?
                    .ok_or_else(|| {
                        ClickError::new(
                            "loop-effect `have` body was admitted without a checked Proof driver",
                        )
                    })?;
                *scopes
                    .last_mut()
                    .expect("an open-chain driver owns a leading scope") =
                    current.join_nested(nested)?;
            }
            step => {
                let current = scopes
                    .last()
                    .expect("an open-chain driver owns a leading scope")
                    .clone();
                *scopes
                    .last_mut()
                    .expect("an open-chain driver owns a leading scope") =
                    current.apply_step_at(step.clone(), tactic_index, source_index)?;
            }
        }
        source_index += loop_effect_step_source_width(step);
    }
    Err(ClickError::new(
        "a loop-effect open-chain driver did not reach its checked terminal `if`",
    ))
}

fn apply_loop_effect_arm_certificate_at<'a>(
    mut scopes: Vec<ProofScope<'a>>,
    current: ProofScope<'a>,
    certificate: &ProofCertificate,
    tactic_index_offset: usize,
    source_index_offset: usize,
) -> Result<Proof<'a>, ClickError> {
    *scopes
        .last_mut()
        .expect("a loop-effect arm owns at least one open scope") = current.clone();
    if let Some(branch_path) = loop_effect_open_branch_path(certificate) {
        let wrap_from = scopes.len();
        return apply_loop_effect_open_chain_certificate_at(
            scopes,
            certificate,
            &branch_path,
            wrap_from,
            tactic_index_offset,
            source_index_offset,
        );
    }
    let leaf = apply_loop_effect_scope_certificate_at(
        current,
        certificate,
        tactic_index_offset,
        source_index_offset,
    )?;
    ProofScope::complete_loop_effect_leaf(&scopes, leaf)
}

fn apply_loop_effect_certificate_at<'a>(
    mut proof: Proof<'a>,
    certificate: &ProofCertificate,
    tactic_index_offset: usize,
    source_index_offset: usize,
) -> Result<Proof<'a>, ClickError> {
    let mut source_index = source_index_offset;
    for (local_index, step) in certificate.steps().iter().enumerate() {
        let tactic_index = tactic_index_offset + local_index;
        match step {
            SimpleProofStep::If {
                condition,
                then_proof,
                else_proof,
            } => {
                if local_index + 1 != certificate.steps().len() {
                    return Err(ClickError::new(
                        "a loop-effect `if` must be the terminal proof operation",
                    ));
                }
                let then_source_index = source_index + 1;
                let else_source_index = then_source_index
                    + then_proof
                        .steps()
                        .iter()
                        .map(loop_effect_step_source_width)
                        .sum::<usize>();
                return proof.apply_execution_if_with(
                    condition.clone(),
                    |then_proof_root| {
                        apply_loop_effect_certificate_at(
                            then_proof_root,
                            then_proof,
                            tactic_index + 1,
                            then_source_index,
                        )
                    },
                    |else_proof_root| {
                        apply_loop_effect_certificate_at(
                            else_proof_root,
                            else_proof,
                            tactic_index + 1,
                            else_source_index,
                        )
                    },
                );
            }
            SimpleProofStep::Cases {
                disjunction,
                left_proof,
                right_proof,
            } => {
                if local_index + 1 != certificate.steps().len() {
                    return Err(ClickError::new(
                        "loop-effect `cases` must be the terminal proof operation",
                    ));
                }
                let left_source_index = source_index + 1;
                let right_source_index = left_source_index
                    + left_proof
                        .steps()
                        .iter()
                        .map(loop_effect_step_source_width)
                        .sum::<usize>();
                return proof.apply_execution_cases_with(
                    disjunction.clone(),
                    |left_proof_root| {
                        apply_loop_effect_certificate_at(
                            left_proof_root,
                            left_proof,
                            tactic_index + 1,
                            left_source_index,
                        )
                    },
                    |right_proof_root| {
                        apply_loop_effect_certificate_at(
                            right_proof_root,
                            right_proof,
                            tactic_index + 1,
                            right_source_index,
                        )
                    },
                );
            }
            SimpleProofStep::Open {
                resource,
                proof: body,
            } => {
                let scope = proof.begin_open(resource.clone(), source_index)?;
                proof = apply_loop_effect_open_certificate_at(
                    scope,
                    body,
                    tactic_index + 1,
                    source_index + 1,
                )?;
            }
            SimpleProofStep::Have {
                proposition,
                proof: body,
            } => {
                let scope = proof.begin_have(proposition.clone())?;
                let tactics = body.to_proof_tactics();
                let scope = scope
                    .try_authoritative_linear_script(&tactics)?
                    .ok_or_else(|| {
                        ClickError::new(
                            "loop-effect `have` body was admitted without a checked Proof driver",
                        )
                    })?;
                proof = scope.join()?;
            }
            step => {
                proof = proof.apply_step_at(step.clone(), tactic_index, source_index)?;
            }
        }
        source_index += loop_effect_step_source_width(step);
    }
    Ok(proof)
}

#[allow(clippy::too_many_arguments)]
fn verify_structural_effect_proof(
    _expansion_capture: Option<&mut ExpansionCapture>,
    loop_index: usize,
    item_index: usize,
    item: &StructuralItem,
    check: &CLoopEffectCheck,
    body: &CStatement,
    before_state: &CState,
    case_path: &[ProofCaseChoice],
    preservation: &Proof<'_>,
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<ProofCertificate, ClickError> {
    let legacy_site = ProofSite::StructuralItem {
        function_name: environment.function_block.signature().name().to_string(),
        region: CodeRegion::Loop(loop_index),
        item_index,
        kind: item.kind(),
    };
    let (site, claim_label, effect_source_index) = environment
        .frontier_loop_source
        .map(|source| {
            (
                source
                    .proof_site
                    .clone()
                    .unwrap_or_else(|| legacy_site.clone()),
                source.claim_label.clone(),
                source
                    .effect_source_indices
                    .get(&item_index)
                    .copied()
                    .unwrap_or(source.loop_source_index),
            )
        })
        .unwrap_or_else(|| (legacy_site.clone(), legacy_site.description(), 0));
    let source_proof = item.proof();
    let smart_frame = matches!(
        source_proof,
        SourceProof::Default
            | SourceProof::Tactic(SmartTactic::Auto)
            | SourceProof::Tactic(SmartTactic::Frame)
    );
    let source_certificate = match source_proof {
        SourceProof::Default
        | SourceProof::Tactic(SmartTactic::Auto)
        | SourceProof::Tactic(SmartTactic::Frame) => {
            ProofCertificate::from_proof_tactics(&[ProofTactic::FrameUsing {
                region: None,
                premises: Vec::new(),
            }])
        }
        SourceProof::Script(tactics) => ProofCertificate::from_proof_tactics(tactics),
        SourceProof::Tactic(SmartTactic::Simp) => {
            return Err(ClickError::new(format!(
                "`{claim_label}` must use `auto`, `frame`, or a simple proof script"
            )));
        }
    }
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` produced an invalid structural-effect certificate: {error:?}"
        ))
    })?;
    // Structural effects are checked once per already-certified preservation
    // path. The source cursor consumes only the exact leading branch prefix
    // aligned with that path. Any remaining `if` or `cases` is a semantic
    // proof scope and advances the path's Proof through an audited split and
    // join. The cursor owns no facts or successor state, and the caller
    // reconstructs the structured Surface tree from checked provenance after
    // all paths complete.
    let certificate = select_loop_effect_path_prefix(
        &claim_label,
        &source_certificate.to_proof_tactics(),
        case_path,
    )?;
    // Every recursively simple operation and nested resource scope supported
    // by the typed Proof APIs is authoritative here. Smart frame syntax
    // selects its bounded explicit premises from this Proof; a search miss is
    // a checked failure rather than permission to replay the same candidate
    // elsewhere.
    if !loop_effect_open_body_supported(&certificate) {
        return Err(ClickError::new(format!(
            "`{claim_label}` uses a proof operation that is unavailable for a loop structural effect"
        )));
    }
    let root = preservation.start_loop_effect_goal(&claim_label, site, before_state, check)?;
    let checked = if smart_frame {
        root.try_smart_loop_effect_frame_at(body, 0, effect_source_index)?
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` smart structural-effect frame found no checked Proof descendant"
                ))
            })?
    } else {
        apply_loop_effect_certificate_at(root, &certificate, 0, effect_source_index)?
    };
    if !checked.is_complete() {
        return Err(ClickError::new(format!(
            "`{claim_label}` structural-effect proof did not close its checked Proof goal"
        )));
    }
    Ok(checked.certificate())
}

pub(in crate::lang::click::proof) struct LoopPreservationProofResult {
    pub(in crate::lang::click::proof) certificate: ProofCertificate,
    pub(in crate::lang::click::proof) effect_certificates: Vec<(usize, ProofCertificate)>,
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn verify_one_loop_preservation_proof(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    loop_index: usize,
    tactics: &[ProofTactic],
    first_generated_tactic_index: usize,
    preservation: &crate::kernel::CLoopPreservationContext,
    pure_facts: &[Proposition],
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    body: &CStatement,
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<LoopPreservationProofResult, ClickError> {
    let legacy_site = ProofSite::LoopPhase {
        function_name: environment.function_block.signature().name().to_string(),
        loop_index,
        phase: "preserve",
    };
    let (claim_label, preserve_source_index, preserve_site) = environment
        .frontier_loop_source
        .map(|source| {
            (
                source.claim_label.clone(),
                source
                    .preserve_source_index
                    .unwrap_or(source.loop_source_index),
                source
                    .proof_site
                    .clone()
                    .unwrap_or_else(|| legacy_site.clone()),
            )
        })
        .unwrap_or_else(|| (legacy_site.description(), 0, legacy_site));

    let proof_claims = [];
    let mut program = if environment
        .frontier_loop_source
        .is_some_and(|source| source.preserve_source_index.is_none())
    {
        build_generated_certificate_proof(tactics, &claim_label, preserve_source_index)?
    } else {
        build_internal_proof_from_source_index(tactics, preserve_source_index)?
    };
    if first_generated_tactic_index < tactics.len() {
        // Automatic preservation appends planned body steps and a closer
        // after the source-written unfold prefix. They are owned by the loop
        // tactic, not additional source occurrences after `preserve`.
        // Detach them so a later nested clause (notably `immutable by frame`)
        // cannot be mistaken for one of these generated tactics by expand.
        detach_generated_suffix_from_source_indices(&mut program, first_generated_tactic_index);
    }
    let source_layout = SourceExecutionLayout::new(environment.parsed_function.body());
    let loop_body_statement_index = source_layout.loop_body_entry(loop_index).ok_or_else(|| {
        ClickError::new(format!("`{claim_label}` has no source loop({loop_index})"))
    })?;
    let mut replay = TacticReplayState {
        proof_site: Some(preserve_site),
        frontier: ExecutionFrontier {
            point: ProofExecutionPoint::StatementEntry {
                remaining: body.clone().into(),
            },
            region: ExecutionRegionKind::LoopBody,
            execution_start_state: Some(preservation.state().clone()),
            next_statement_index: loop_body_statement_index,
            ..ExecutionFrontier::default()
        },
        source_layout,
        region_proof: true,
        loop_invariant_region: true,
        function_entry_state: Some(environment.initial_state.clone()),
        surface_propositions: environment.surface_propositions.clone(),
        ..TacticReplayState::default()
    };
    record_statement_program_point_state(
        &mut replay,
        environment.function_block,
        loop_body_statement_index,
        ProgramPointKind::Entry,
        preservation.state().clone(),
    );
    replay.program_point_states.insert(
        ProgramPointRef {
            region: CodeRegionRef::Loop(loop_index),
            kind: ProgramPointKind::Entry,
        },
        preservation.loop_entry_state().clone(),
    );
    let contexts = execute_internal_proof(
        &program,
        ProofReplayContext {
            state: preservation.state().clone(),
            pure_facts: pure_facts.to_vec(),
            replay: Box::new(replay),
            branch_path: PersistentSequence::default(),
        },
        expansion_capture.as_deref_mut(),
        environment.function_block,
        environment.parsed_function,
        &proof_claims,
        &claim_label,
        environment.function_environment,
        environment.predicate_environment,
        environment.click_function_environment,
        environment.resource_environment,
        environment.theorem_environment,
        environment.function,
        environment.arguments,
    )?;
    let effect_items = environment
        .function_block
        .structural_clauses()
        .iter()
        .find(|clause| clause.region() == &CodeRegion::Loop(loop_index))
        .into_iter()
        .flat_map(|clause| clause.items().iter().enumerate())
        .filter(|(_, item)| item.is_effect_kind())
        .collect::<Vec<_>>();
    if effect_items.len() != effect_checks.len() {
        return Err(ClickError::new(format!(
            "`{claim_label}` has {} structural effect items but {} lowered effect checks",
            effect_items.len(),
            effect_checks.len()
        )));
    }
    let mut certificate_paths = Vec::new();
    let mut effect_certificate_paths = vec![Vec::new(); effect_items.len()];
    for context in contexts {
        if !context.replay.is_at_region_boundary() {
            return Err(ClickError::new(format!(
                "`{claim_label}` must execute exactly one complete loop-body iteration"
            )));
        }
        let case_path = context
            .replay
            .case_assumptions
            .iter()
            .map(|choice| ProofCaseChoice {
                condition: choice.condition.clone(),
                value: choice.value,
            })
            .collect::<Vec<_>>();
        let source_tactics =
            ProofCertificate::from_steps(context.replay.proof_certificate_builder.steps.clone())
                .to_proof_tactics();
        let region_simp = context.replay.region_simp;
        let proof_site = context.replay.proof_site.clone();
        let invariants_already_closed = context.replay.region_invariants_closed;
        let statement_index = context.replay.frontier.next_statement_index;
        let (closer_index, closer_source, closer_name, closer_class) =
            if let Some(step) = context.replay.invariant_closer_step {
                (
                    step.tactic_index,
                    step.source_index,
                    "close_invariants",
                    "simple",
                )
            } else if let Some((tactic_index, source_index)) = region_simp {
                (tactic_index, source_index, "simp", "smart")
            } else {
                (tactics.len(), tactics.len(), "assumption", "simple")
            };
        let _timing = crate::instrumentation::enabled().then(|| {
            if crate::instrumentation::starts_enabled() {
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticStarted(
                        crate::instrumentation::TacticEvent {
                            claim: claim_label.clone(),
                            tactic_index: closer_index,
                            tactic_name: closer_name.to_string(),
                            class: closer_class.to_string(),
                            statement_index,
                            source_index: closer_source,
                        },
                    ),
                );
            }
            let timing_context = TimingTacticContext {
                claim_label: claim_label.clone(),
                tactic_index: closer_index,
                source_index: closer_source,
                tactic_name: closer_name.to_string(),
                tactic_class: closer_class.to_string(),
                statement_index,
            };
            push_timing_tactic(timing_context.clone());
            TacticTiming {
                claim_label: claim_label.clone(),
                tactic_index: closer_index,
                source_index: closer_source,
                tactic_name: closer_name.to_string(),
                tactic_class: closer_class,
                statement_index,
                start: std::time::Instant::now(),
                context: timing_context,
            }
        });
        let root = Proof::for_execution_frontier(
            &claim_label,
            0,
            context,
            environment.function_block,
            environment.function,
            environment.parsed_function,
            environment.arguments,
            environment.function_environment,
            environment.resource_environment,
            environment.predicate_environment,
            environment.click_function_environment,
            environment.theorem_environment,
        );
        let checked = if invariant_checks.is_empty() {
            root
        } else {
            root.certify_loop_invariant_bundle(preservation.loop_entry_state(), invariant_checks)
                .map_err(|error| {
                    ClickError::new(format!(
                        "`{claim_label}` (loop {loop_index} invariant bundle preservation): {}",
                        error.message()
                    ))
                })?
        };
        let closer_tactics = if invariant_checks.is_empty() || invariants_already_closed {
            Vec::new()
        } else {
            checked.certificate().to_proof_tactics().to_vec()
        };
        let omitted_frontier_preservation = environment
            .frontier_loop_source
            .is_some_and(|source| source.preserve_source_index.is_none());
        if !omitted_frontier_preservation
            && region_simp.is_some_and(|(_, source_index)| {
                tactic_expansion_capture_matches(
                    expansion_capture.as_deref(),
                    proof_site.as_ref(),
                    source_index,
                )
            })
        {
            let capture = ProofCertificateBuilder {
                steps: ProofCertificate::from_proof_tactics(&closer_tactics)
                    .expect("the loop closer is a simple proof")
                    .steps()
                    .to_vec(),
                ..ProofCertificateBuilder::default()
            };
            // A region whose invariants are already closed has a
            // legitimately empty closer: the selected `simp` contributes no
            // surface tactics and its exact expansion removes it.
            finish_tactic_expansion_capture(
                expansion_capture.as_deref_mut(),
                &capture,
                closer_tactics.is_empty(),
            );
        }
        let prefix = certificate_leaf_for_case_path(&claim_label, &source_tactics, &case_path)?;
        let mut leaf_tactics = prefix.to_proof_tactics().to_vec();
        leaf_tactics.extend(closer_tactics);
        let certificate = ProofCertificate::from_proof_tactics(&leaf_tactics).map_err(|error| {
            ClickError::new(format!(
                "`{claim_label}` produced an invalid preservation leaf certificate: {error:?}"
            ))
        })?;
        certificate_paths.push(PathCertificate {
            case_path: case_path.clone(),
            certificate,
        });
        for (effect_index, ((item_index, item), check)) in
            effect_items.iter().zip(effect_checks).enumerate()
        {
            let effect_certificate = verify_structural_effect_proof(
                expansion_capture.as_deref_mut(),
                loop_index,
                *item_index,
                item,
                check,
                body,
                preservation.state(),
                &case_path,
                &checked,
                environment,
            )?;
            effect_certificate_paths[effect_index].push(PathCertificate {
                case_path: case_path.clone(),
                certificate: effect_certificate,
            });
        }
    }
    let certificate = merge_path_aligned_certificates(&claim_label, certificate_paths)?;
    let effect_certificates = effect_items
        .iter()
        .zip(effect_certificate_paths)
        .map(|((item_index, item), paths)| {
            let site = ProofSite::StructuralItem {
                function_name: environment.function_block.signature().name().to_string(),
                region: CodeRegion::Loop(loop_index),
                item_index: *item_index,
                kind: item.kind(),
            };
            Ok((
                *item_index,
                merge_path_aligned_certificates(&site.description(), paths)?,
            ))
        })
        .collect::<Result<Vec<_>, ClickError>>()?;
    Ok(LoopPreservationProofResult {
        certificate,
        effect_certificates,
    })
}
