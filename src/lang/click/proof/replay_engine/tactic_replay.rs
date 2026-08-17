use super::*;
use crate::kernel::prove_pure_proposition_from_context;

/// Track, in the certificate-generation fact set, the facts a recorded
/// post-execution surface tactic just added to the drain's requirements.
///
/// `surface_certificate_facts` is snapshotted before the drain runs, but
/// the certificate a claim ends up with is `[recorded post tactics ...,
/// closer tactics ...]`. Facts produced by replaying a recorded tactic are
/// therefore in scope when the closer replays; withholding them from
/// generation only makes generation plan against strictly less than the
/// replay judgment accepts.
pub(in crate::lang::click::proof) fn record_certificate_facts_from_replay(
    before: &[Proposition],
    after: &[Proposition],
    surface_certificate_facts: &mut Vec<Proposition>,
) {
    for fact in after {
        if !before.contains(fact) && !surface_certificate_facts.contains(fact) {
            surface_certificate_facts.push(fact.clone());
        }
    }
}

fn tactic_is_deferred_post_execution(tactic: &ProofTactic) -> bool {
    matches!(
        tactic,
        ProofTactic::FoldResource(_)
            | ProofTactic::UnfoldPredicate(_)
            | ProofTactic::ApplyTheorem(_)
            | ProofTactic::ApplyTheoremUsing { .. }
            | ProofTactic::Have(_)
            | ProofTactic::Transport { .. }
            | ProofTactic::TransportUsing { .. }
            | ProofTactic::Witness(_)
            | ProofTactic::Choose(_)
            | ProofTactic::Assumption
            | ProofTactic::Normalize
            | ProofTactic::Rewrite(_)
            | ProofTactic::Simp
            | ProofTactic::FrameUsing {
                region: None | Some(CodeRegionRef::Function),
                ..
            }
    )
}

fn execute_frontier_local_loop(
    expansion_capture: Option<&mut ExpansionCapture>,
    loop_template: &StructuralClause,
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    arguments: &[CExpression],
    claim_label: &str,
    tactic_index: usize,
    source_index: usize,
) -> Result<(), ClickError> {
    if replay.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `loop` requires the execution frontier to be at a loop, but execution has reached function exit"
        )));
    }
    let statement_index = replay.frontier.next_statement_index;
    let source_region = replay.source_layout.statement(statement_index).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `loop` could not resolve source statement({statement_index})"
        ))
    })?;
    let SourceStatementKind::Loop { loop_index } = source_region.kind else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `loop` requires the execution frontier to be at a loop; current frontier is statement({statement_index})"
        )));
    };
    if replay
        .frontier_loop_clauses
        .iter()
        .any(|clause| clause.region() == &CodeRegion::Loop(loop_index))
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: loop({loop_index}) already has a frontier-local proof on this execution path"
        )));
    }
    let function_with_prior_loops =
        function_block.with_bound_frontier_loop_clauses(&replay.frontier_loop_clauses.to_vec());
    let bound_function_block =
        function_with_prior_loops.with_frontier_loop_clause(loop_template, loop_index);
    validate_region_proof_clauses(&bound_function_block, parsed_function)?;

    let initial_state = replay.execution_start_state(state).clone();
    let annotated = annotated_function(
        &bound_function_block,
        parsed_function,
        &initial_state,
        arguments,
        predicate_environment,
        click_function_environment,
        resource_environment,
        false,
    )?;
    if replay.is_at_function_entry() {
        let entry_state = c_function_entry_state(&initial_state, &annotated, arguments)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `loop` could not bind function arguments"
                ))
            })?;
        replay.frontier.execution_start_state = Some(initial_state.clone());
        replay.frontier.point = ProofExecutionPoint::StatementEntry {
            remaining: annotated.body().clone().into(),
        };
        *state = entry_state;
    }
    let mut found_loop_index = 0;
    let current_loop = kernel_loop_by_index(annotated.body(), loop_index, &mut found_loop_index)
        .cloned()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `loop` could not lower loop({loop_index}) at statement({statement_index})"
            ))
        })?;

    let source_layout = SourceExecutionLayout::new(parsed_function.body());
    let loop_certificates = std::cell::RefCell::new(LoopProofCertificates::default());
    let loop_source = FrontierLoopProofSource::new(
        loop_template,
        replay.proof_site.clone(),
        claim_label,
        source_index,
    );
    let proof_environment = ExecutionProofEnvironment {
        initial_state: &initial_state,
        function_block: &bound_function_block,
        parsed_function,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        function: &annotated,
        arguments,
        surface_propositions: &replay.surface_propositions,
        source_layout: &source_layout,
        frontier_loop_certificates: Some(&loop_certificates),
        frontier_loop_source: Some(&loop_source),
    };
    let case_path = replay
        .case_assumptions
        .iter()
        .map(|choice| ProofCaseChoice {
            condition: choice.condition.clone(),
            value: choice.value,
        })
        .collect();
    let mut verified_loop_rules = Vec::new();
    let mut next_statement_index = statement_index;
    let mut next_loop_index = loop_index;
    // `unfold` retains the opaque predicate atom alongside its definition so
    // later surface tactics can still refer to either spelling.  A verified
    // loop rule must not turn that proof-context convenience into an ambient
    // kernel prerequisite: exact contract certification exposes the fully
    // unfolded definition.  Keep every other fact, including the expanded
    // proposition, and omit only predicate atoms whose names have explicitly
    // been unfolded on this path.
    let loop_pure_facts = available_pure_facts
        .iter()
        .filter(|fact| {
            !matches!(
                fact,
                Proposition::Predicate { name, .. }
                    if replay.unfolded_predicates.contains(name)
            )
        })
        .cloned()
        .collect();
    let _exit_contexts = verify_execution_proofs_forward(
        expansion_capture,
        &current_loop,
        vec![ExecutionProofContext {
            state: state.clone(),
            pure_facts: loop_pure_facts,
            surface_propositions: replay.surface_propositions.clone(),
            program_point_states: replay.program_point_states.clone(),
            case_path,
            next_opaque_call: replay.next_opaque_call,
            next_verification_variable: replay.next_verification_variable,
        }],
        &mut next_statement_index,
        &mut next_loop_index,
        &proof_environment,
        &mut verified_loop_rules,
    )?;
    let loop_rule = verified_loop_rules
        .pop()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `loop` did not construct a verified rule for loop({loop_index})"
            ))
        })?
        .with_composite_resource_definitions(
            annotated.composite_resource_definitions().iter().cloned(),
        );
    let loop_exit_condition = match &current_loop {
        CStatement::While { condition, .. } => Some(ClickProposition::Not(Box::new(
            surface_c_condition(condition),
        ))),
        _ => None,
    };
    let certificates = loop_certificates.borrow().clone();
    let mut expanded_loop = loop_template.clone();
    expanded_loop.initialize_proof = Some(SourceProof::Script(
        certificates
            .initialize
            .as_ref()
            .map(|certificate| certificate.to_proof_tactics().to_vec())
            .unwrap_or_else(|| vec![ProofTactic::Assumption]),
    ));
    expanded_loop.preserve_proof = Some(SourceProof::Script(
        certificates
            .preserve
            .as_ref()
            .map(|certificate| certificate.to_proof_tactics().to_vec())
            .unwrap_or_else(|| vec![ProofTactic::Assumption]),
    ));
    for (item_index, item) in expanded_loop.items.iter_mut().enumerate() {
        if !item.is_effect_kind() {
            continue;
        }
        if let Some(certificate) = certificates.effects.get(&item_index) {
            item.proof = SourceProof::Script(certificate.to_proof_tactics().to_vec());
        }
    }
    let local_function_environment = function_environment.clone().with_verified_loop_rules(
        replay
            .frontier_loop_rules
            .iter()
            .cloned()
            .chain(std::iter::once(loop_rule.clone())),
    );

    if let ProofExecutionPoint::StatementEntry { remaining } = &replay.frontier.point {
        let (_, tail) = split_next_source_operation(remaining).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `loop` could not isolate the current source loop: {message}"
                ))
            })?;
        let mut statements = Vec::new();
        statements.push(current_loop);
        if let Some(tail) = tail {
            flatten_top_level_sequence(&tail, &mut statements).map_err(ClickError::new)?;
        }
        replay.frontier.point = ProofExecutionPoint::StatementEntry {
            remaining: sequence_from_statements(&statements)
                .expect("the current loop always contributes one statement")
                .into(),
        };
    }

    let assumptions = assumptions_from_propositions(available_pure_facts);
    execute_step_from_execution_point(
        replay,
        state,
        available_pure_facts,
        &bound_function_block,
        &annotated,
        parsed_function.parameters(),
        arguments,
        &assumptions,
        &local_function_environment,
        claim_label,
        tactic_index,
        "loop",
        StatementPrerequisitePolicy::Exact,
        StatementFactTransportPolicy::Automatic,
        LoopStepPolicy::ApplyVerifiedRule,
        None,
    )?;
    if let Some(exit_condition) = loop_exit_condition {
        let exit_point = ProgramPointRef {
            region: CodeRegionRef::Loop(loop_index),
            kind: ProgramPointKind::Exit,
        };
        let lowered_exit_condition = lower_point_proposition(
            &exit_condition,
            available_pure_facts,
            parsed_function.parameters(),
            arguments,
            &initial_state,
            state,
            None,
            &replay.program_point_states,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not lower loop({loop_index}) exit condition provenance: {message}"
            ))
        })?;
        if available_pure_facts.contains(&lowered_exit_condition) {
            let exit_surface = surface_with_source_site(&exit_condition, &exit_point)?;
            replay
                .surface_propositions
                .record_lowering(&exit_surface, &lowered_exit_condition)?;
        }
    }
    replay
        .frontier_loop_clauses
        .push(loop_template.bound_to_loop(loop_index));
    replay.frontier_loop_rules.push(loop_rule);
    replay
        .proof_certificate_builder
        .push_source_tactic(ProofTactic::Loop(expanded_loop));
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn replay_linear_tactics(
    mut context: ProofReplayContext,
    mut expansion_capture: Option<&mut ExpansionCapture>,
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
    tactics: &[IndexedTactic],
) -> Result<ProofReplayContext, ClickError> {
    let mut chunk_start = 0;
    for (index, indexed_tactic) in tactics.iter().enumerate() {
        let ProofTactic::Loop(loop_clause) = &indexed_tactic.tactic else {
            continue;
        };
        context = replay_linear_tactics_without_frontier_loops(
            context,
            expansion_capture.as_deref_mut(),
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
            &tactics[chunk_start..index],
        )?;
        context = replay_frontier_local_loop_tactic(
            context,
            expansion_capture.as_deref_mut(),
            loop_clause,
            indexed_tactic.index,
            indexed_tactic.source_index,
            function_block,
            parsed_function,
            claim_label,
            function_environment,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            arguments,
        )?;
        chunk_start = index + 1;
    }
    replay_linear_tactics_without_frontier_loops(
        context,
        expansion_capture,
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
        &tactics[chunk_start..],
    )
}

#[allow(clippy::too_many_arguments)]
fn replay_frontier_local_loop_tactic(
    context: ProofReplayContext,
    expansion_capture: Option<&mut ExpansionCapture>,
    loop_clause: &StructuralClause,
    tactic_index: usize,
    source_index: usize,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    arguments: &[CExpression],
) -> Result<ProofReplayContext, ClickError> {
    if crate::instrumentation::deadline_exceeded() {
        return Err(ClickError::new(format!(
            "tactic budget exhausted: {}",
            crate::instrumentation::deadline_context()
        )));
    }
    let ProofReplayContext {
        mut state,
        pure_facts: mut available_pure_facts,
        mut replay,
        branch_path,
    } = context;
    let mut expansion_capture = expansion_capture;
    let mut scope = Some(begin_tactic_surface_scope(&mut replay));
    let capture_this_tactic =
        begin_tactic_expansion_capture(expansion_capture.as_deref_mut(), source_index, &replay);
    let _timing = TacticTiming::new(
        claim_label,
        tactic_index,
        source_index,
        &ProofTactic::Loop(loop_clause.clone()),
        replay.frontier.next_statement_index,
    );
    execute_frontier_local_loop(
        expansion_capture.as_deref_mut(),
        loop_clause,
        &mut replay,
        &mut state,
        &mut available_pure_facts,
        function_block,
        parsed_function,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        arguments,
        claim_label,
        tactic_index,
        source_index,
    )?;
    let slice = end_tactic_surface_scope(&mut replay, scope.take().expect("tactic scope is open"));
    if capture_this_tactic {
        finish_tactic_expansion_capture(expansion_capture, &slice, false);
    }
    Ok(ProofReplayContext {
        state,
        pure_facts: available_pure_facts,
        replay,
        branch_path,
    })
}

/// Migrates point-proof paths supported by the checked proof object: direct
/// and mixed linear smart scripts plus structured logical branches/scopes.
///
/// The premise planner is only a query. The theorem application advances
/// through `Proof::apply_step`, so the returned certificate is the provenance
/// of the semantic work already performed, not a second representation that
/// ordinary verification must replay.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn checked_have_with_proof(
    have: &ProofHave,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    tactic_index: usize,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    replay: &TacticReplayState,
    surface_propositions: &SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    original_requirements: &[Requirement],
    requirement_label_indices: &BTreeMap<String, usize>,
) -> Result<Option<(Proposition, Option<ProofCertificate>)>, ClickError> {
    enum Plan<'a> {
        DirectSmart,
        Script(&'a [ProofTactic]),
    }

    let plan = match &have.proof {
        SourceProof::Default | SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => {
            Plan::DirectSmart
        }
        SourceProof::Script(tactics) => Plan::Script(tactics),
        SourceProof::Tactic(SmartTactic::Frame) => return Ok(None),
    };
    let goal = lower_point_proposition(
        &have.proposition,
        &facts_for_simple_goal_lowering(available),
        parameters,
        arguments,
        pre_state,
        state,
        result,
        &replay.program_point_states,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` have proof {tactic_index}: could not lower pure goal: {message}"
        ))
    })?;
    let proof = Proof::for_point_goal_with_requirements(
        claim_label,
        tactic_index,
        available,
        goal.clone(),
        parameters,
        arguments,
        pre_state,
        state,
        result,
        &replay.program_point_states,
        surface_propositions,
        predicate_environment,
        click_function_environment,
        theorem_environment,
        &replay.unfolded_predicates,
        &replay.effect_facts,
        original_requirements,
        requirement_label_indices,
    );
    let (proof, append_certificate) = match plan {
        Plan::Script(tactics) => {
            if let Some(checked) = proof.try_linear_smart_script(tactics)? {
                (checked, true)
            } else {
                let Ok(certificate) = ProofCertificate::from_proof_tactics(tactics) else {
                    return Ok(None);
                };
                // Preserve legacy failure diagnostics for certificate
                // operations not yet admitted by Proof, or for a rejected
                // source script.
                let Ok(checked) = proof.check_certificate(&certificate) else {
                    return Ok(None);
                };
                (checked, false)
            }
        }
        Plan::DirectSmart => {
            let Some(closed) = proof.try_direct_logical_closure() else {
                return Ok(None);
            };
            (closed, true)
        }
    };
    if !proof.is_complete() {
        return Err(ClickError::new(format!(
            "`{claim_label}` have proof {tactic_index}: checked proof retained an open goal"
        )));
    }
    let certificate = append_certificate.then(|| {
        let body = proof.certificate();
        ProofCertificate::from_steps(vec![SimpleProofStep::Have {
            proposition: have.proposition.clone(),
            proof: Box::new(body),
        }])
    });
    Ok(Some((goal, certificate)))
}

/// Tries the linear smart statement candidate whose complete exact
/// definedness premise set is available through the immutable Proof.
///
/// Keep this operation and its result outlined from the recursive proof
/// executor. The deep pure-case regression is intentionally sensitive to
/// growth in that caller's stack frame.
#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn try_indexed_step_on_proof<'a>(
    state: &mut CState,
    pure_facts: &mut Vec<Proposition>,
    replay: &mut TacticReplayState,
    branch_path: &mut PersistentSequence<String>,
    function_block: &'a FunctionBlock,
    function: &'a CFunction,
    parsed_function: &'a syntax::C0Function,
    arguments: &'a [CExpression],
    function_environment: &'a CExecutionEnvironment,
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    theorem_environment: &'a TheoremEnvironment,
    claim_label: &'a str,
    tactic_index: usize,
) -> Result<bool, ClickError> {
    let context = ProofReplayContext {
        state: std::mem::replace(state, CState::new()),
        pure_facts: std::mem::take(pure_facts),
        replay: std::mem::take(replay),
        branch_path: std::mem::take(branch_path),
    };
    let root = Proof::for_execution_frontier(
        claim_label,
        tactic_index,
        context,
        function_block,
        function,
        parsed_function,
        arguments,
        function_environment,
        predicate_environment,
        click_function_environment,
        theorem_environment,
    );
    match root.try_indexed_statement_step()? {
        Some(proof) => {
            let certificate = proof.certificate();
            let context = proof.into_execution_context()?;
            *state = context.state;
            *pure_facts = context.pure_facts;
            *replay = context.replay;
            *branch_path = context.branch_path;
            for step in certificate.steps() {
                replay.proof_certificate_builder.push_step(step.clone());
            }
            Ok(true)
        }
        None => {
            let context = root.into_execution_context()?;
            *state = context.state;
            *pure_facts = context.pure_facts;
            *replay = context.replay;
            *branch_path = context.branch_path;
            Ok(false)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn replay_linear_tactics_without_frontier_loops(
    context: ProofReplayContext,
    mut expansion_capture: Option<&mut ExpansionCapture>,
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
    tactics: &[IndexedTactic],
) -> Result<ProofReplayContext, ClickError> {
    let ProofReplayContext {
        mut state,
        pure_facts: mut requirement_pure_facts,
        mut replay,
        mut branch_path,
    } = context;
    let mut assumptions = assumptions_from_propositions(&requirement_pure_facts);

    for indexed_tactic in tactics {
        if crate::instrumentation::deadline_exceeded() {
            return Err(ClickError::new(format!(
                "tactic budget exhausted: {}",
                crate::instrumentation::deadline_context()
            )));
        }
        let tactic_index = indexed_tactic.index;
        let source_index = indexed_tactic.source_index;
        let tactic = &indexed_tactic.tactic;
        let deferred_post_execution = replay.ordered_finalization
            && replay.is_at_function_exit()
            && replay.open_scopes == 0
            && tactic_is_deferred_post_execution(tactic);
        let deferred_region_simp = replay.region_proof && matches!(tactic, ProofTactic::Simp);
        let mut scope = Some(begin_tactic_surface_scope(&mut replay));
        let capture_this_tactic =
            begin_tactic_expansion_capture(expansion_capture.as_deref_mut(), source_index, &replay);
        if capture_this_tactic && deferred_post_execution {
            replay.deferred_tactic_capture = Some(DeferredTacticCapture {
                tactic_index,
                source_index,
                post_execution_index: replay.post_execution_tactics.len(),
                branch_skeleton: ProofCertificate::from_steps(
                    replay.proof_certificate_builder.steps.clone(),
                )
                .to_proof_tactics(),
            });
        }
        if !deferred_post_execution {
            let mut construction = std::mem::take(&mut replay.proof_certificate_builder);
            {
                let mut construction_context =
                    ProofCertificateConstructionContext::new(&mut replay, &mut construction);
                append_simple_proof_step_for_operation(
                    &mut construction_context,
                    &state,
                    &requirement_pure_facts,
                    function_block,
                    parsed_function.parameters(),
                    arguments,
                    predicate_environment,
                    click_function_environment,
                    Some(tactic),
                    None,
                    None,
                );
            }
            replay.proof_certificate_builder = construction;
        }
        let _timing = (!(deferred_post_execution
            || replay.region_proof && matches!(tactic, ProofTactic::Simp))
            && has_independent_source_timing(tactic))
        .then(|| {
            TacticTiming::new(
                claim_label,
                tactic_index,
                source_index,
                tactic,
                replay.frontier.next_statement_index,
            )
        })
        .flatten();
        if let ProofTactic::Transport {
            source: surface_source,
            target: surface_target,
        } = tactic
            && !replay.is_at_function_exit()
        {
            if replay.is_at_function_entry() || replay.is_at_function_exit() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a current statement frontier after at least one execution step"
                )));
            }
            let pre_state = replay.old_reference_state(&state).clone();
            let source = lower_point_proposition(
                surface_source,
                &requirement_pure_facts,
                parsed_function.parameters(),
                arguments,
                &pre_state,
                &state,
                None,
                &replay.program_point_states,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport` source: {message}"
                ))
            })?;
            if assumptions.derive_proposition(&source).is_none() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a source derivable from its ambient facts: {}",
                    describe_missing_pure_fact(
                        &source,
                        &requirement_pure_facts,
                        state.resources().facts(),
                        parsed_function.parameters(),
                        arguments,
                        &replay.effect_facts,
                    )
                )));
            }
            let target = lower_point_proposition(
                surface_target,
                &requirement_pure_facts,
                parsed_function.parameters(),
                arguments,
                &pre_state,
                &state,
                None,
                &replay.program_point_states,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport` target: {message}"
                ))
            })?;
            let transition_facts = fact_transport_transition_facts(&replay.effect_facts, &source);
            let premises = plan_explicit_fact_transport(
                surface_source,
                &source,
                &target,
                &requirement_pure_facts,
                &transition_facts,
                parsed_function.parameters(),
                arguments,
                &replay,
                &state,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: {}",
                    fact_transport_planning_failure(
                        surface_source,
                        surface_target,
                        &replay.unfolded_predicates,
                        &error,
                    )
                ))
            })?;
            let proof = Proof::for_point_frontier(
                claim_label,
                tactic_index,
                &requirement_pure_facts,
                parsed_function.parameters(),
                arguments,
                &pre_state,
                &state,
                None,
                &replay.program_point_states,
                &replay.surface_propositions,
                predicate_environment,
                click_function_environment,
                theorem_environment,
                &replay.unfolded_predicates,
                &replay.effect_facts,
            );
            let proof = proof.apply_step(SimpleProofStep::TransportUsing {
                source: surface_source.clone(),
                target: surface_target.clone(),
                premises,
            })?;
            let added_facts = proof.added_facts().to_vec();
            let checked_facts = proof.checked_facts().to_vec();
            let certificate = proof.certificate();
            drop(proof);
            let [checked_source, checked_target] = checked_facts.as_slice() else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: checked transport did not retain its source and target"
                )));
            };
            replay
                .surface_propositions
                .record_lowering(surface_source, checked_source)?;
            replay
                .surface_propositions
                .record_lowering(surface_target, checked_target)?;
            for fact in &added_facts {
                if !requirement_pure_facts.contains(fact) {
                    requirement_pure_facts.push(fact.clone());
                }
            }
            for step in certificate.steps() {
                replay.proof_certificate_builder.push_step(step.clone());
            }
            assumptions = assumptions_from_propositions(&requirement_pure_facts);
            let slice =
                end_tactic_surface_scope(&mut replay, scope.take().expect("tactic scope is open"));
            if capture_this_tactic {
                finish_tactic_expansion_capture(expansion_capture.as_deref_mut(), &slice, false);
            }
            continue;
        }
        if let ProofTactic::ApplyTheorem(application) = tactic
            && !replay.is_at_function_exit()
        {
            if theorem_environment.get(&application.name).is_none() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: unknown theorem `{}`",
                    application.name
                )));
            }
            let proof = Proof::for_execution_frontier(
                claim_label,
                tactic_index,
                ProofReplayContext {
                    state,
                    pure_facts: requirement_pure_facts,
                    replay,
                    branch_path,
                },
                function_block,
                function,
                parsed_function,
                arguments,
                function_environment,
                predicate_environment,
                click_function_environment,
                theorem_environment,
            );
            let step = proof.select_execution_theorem_application_step(application)?;
            let proof = proof.apply_step(step)?;
            let certificate = proof.certificate();
            let result = proof.into_execution_context()?;
            state = result.state;
            requirement_pure_facts = result.pure_facts;
            replay = result.replay;
            branch_path = result.branch_path;
            for step in certificate.steps() {
                replay.proof_certificate_builder.push_step(step.clone());
            }
            assumptions = assumptions_from_propositions(&requirement_pure_facts);
            let slice =
                end_tactic_surface_scope(&mut replay, scope.take().expect("tactic scope is open"));
            if capture_this_tactic {
                finish_tactic_expansion_capture(expansion_capture.as_deref_mut(), &slice, false);
            }
            continue;
        }
        match tactic {
            ProofTactic::Mark(name) => {
                let proof = Proof::for_execution_frontier(
                    claim_label,
                    tactic_index,
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    function,
                    parsed_function,
                    arguments,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                );
                let proof = proof.apply_step(SimpleProofStep::Mark(name.clone()))?;
                let result = proof.into_execution_context()?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
            }
            ProofTactic::UnfoldResource(resource) => {
                if replay.is_at_function_exit() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `unfold` must run before execution reaches function exit"
                    )));
                }
                state = unfold_composite_resource(
                    resource_environment,
                    resource,
                    parsed_function.parameters(),
                    arguments,
                    state,
                    &mut requirement_pure_facts,
                    &mut replay.surface_propositions,
                    predicate_environment,
                    click_function_environment,
                    claim_label,
                    tactic_index,
                    ResourceBodyAccess::Finalize,
                )?
                .state;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ObserveResource(resource) => {
                if replay.is_at_function_exit() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `observe` must run before execution reaches function exit"
                    )));
                }
                state = observe_composite_resource(
                    resource_environment,
                    resource,
                    parsed_function.parameters(),
                    arguments,
                    state,
                    &mut requirement_pure_facts,
                    &mut replay.surface_propositions,
                    &mut replay.function_entry_derivations,
                    &mut replay.function_entry_execution_prerequisites,
                    predicate_environment,
                    click_function_environment,
                    claim_label,
                    tactic_index,
                )?;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::Transport {
                source: surface_source,
                target: surface_target,
            }
            | ProofTactic::TransportUsing {
                source: surface_source,
                target: surface_target,
                ..
            } => {
                if replay.is_at_function_exit() {
                    let premises = match tactic {
                        ProofTactic::TransportUsing { premises, .. } => Some(premises.clone()),
                        ProofTactic::Transport { .. } => None,
                        _ => unreachable!(),
                    };
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Transport {
                            source: surface_source.clone(),
                            target: surface_target.clone(),
                            premises,
                        },
                    );
                    end_tactic_surface_scope(
                        &mut replay,
                        scope.take().expect("tactic scope is open"),
                    );
                    continue;
                }
                if replay.is_at_function_entry() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `transport` requires at least one completed execution step"
                    )));
                }
                let ProofTactic::TransportUsing {
                    premises: surface_premises,
                    ..
                } = tactic
                else {
                    unreachable!("mid-execution `transport` is completed by its pre-pass")
                };
                let proof = Proof::for_execution_frontier(
                    claim_label,
                    tactic_index,
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    function,
                    parsed_function,
                    arguments,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                );
                let proof = proof.apply_step(SimpleProofStep::TransportUsing {
                    source: surface_source.clone(),
                    target: surface_target.clone(),
                    premises: surface_premises.clone(),
                })?;
                let result = proof.into_execution_context()?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::StepUsing(premises) => {
                let proof = Proof::for_execution_frontier(
                    claim_label,
                    tactic_index,
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    function,
                    parsed_function,
                    arguments,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                );
                let proof = proof.apply_step(SimpleProofStep::StepUsing(premises.clone()))?;
                let result = proof.into_execution_context()?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::Step => {
                let proof = Proof::for_execution_frontier(
                    claim_label,
                    tactic_index,
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    function,
                    parsed_function,
                    arguments,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                );
                let proof = proof.apply_step(SimpleProofStep::StepUsing(Vec::new()))?;
                let result = proof.into_execution_context()?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::SmartStep => {
                if try_indexed_step_on_proof(
                    &mut state,
                    &mut requirement_pure_facts,
                    &mut replay,
                    &mut branch_path,
                    function_block,
                    function,
                    parsed_function,
                    arguments,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                    claim_label,
                    tactic_index,
                )? {
                    assumptions = assumptions_from_propositions(&requirement_pure_facts);
                    let slice = end_tactic_surface_scope(
                        &mut replay,
                        scope.take().expect("tactic scope is open"),
                    );
                    if capture_this_tactic {
                        finish_tactic_expansion_capture(
                            expansion_capture.as_deref_mut(),
                            &slice,
                            false,
                        );
                    }
                    continue;
                }

                let mut planning_replay = replay.clone();
                planning_replay.planned_statement_transitions.clear();
                planning_replay.proof_certificate_builder = ProofCertificateBuilder {
                    last_step_entry: replay.proof_certificate_builder.last_step_entry.clone(),
                    certificate_facts: ProofFactStore::from_ordered(requirement_pure_facts.clone()),
                    ..ProofCertificateBuilder::default()
                }
                .into();
                let mut planning_state = state.clone();
                let mut planning_facts = requirement_pure_facts.clone();
                execute_step_from_execution_point(
                    &mut planning_replay,
                    &mut planning_state,
                    &mut planning_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    &assumptions,
                    function_environment,
                    claim_label,
                    tactic_index,
                    "step",
                    StatementPrerequisitePolicy::Planning,
                    StatementFactTransportPolicy::Automatic,
                    LoopStepPolicy::EnterBody,
                    Some(ConstructionEnvironments {
                        predicate_environment,
                        click_function_environment,
                    }),
                )?;
                let construction =
                    std::mem::take(&mut planning_replay.proof_certificate_builder).into_value();
                if construction.blocker.is_none()
                    && !construction.steps.is_empty()
                    && matches!(
                        construction.steps.last(),
                        Some(SimpleProofStep::StepUsing(_))
                    )
                    && construction.steps.iter().all(|step| {
                        matches!(
                            step,
                            SimpleProofStep::UnfoldPredicate(_)
                                | SimpleProofStep::TransportUsing { .. }
                                | SimpleProofStep::StepUsing(_)
                        )
                    })
                {
                    let mut proof = Proof::for_execution_frontier(
                        claim_label,
                        tactic_index,
                        ProofReplayContext {
                            state,
                            pure_facts: requirement_pure_facts,
                            replay,
                            branch_path,
                        },
                        function_block,
                        function,
                        parsed_function,
                        arguments,
                        function_environment,
                        predicate_environment,
                        click_function_environment,
                        theorem_environment,
                    );
                    let checkpoint = proof.checkpoint();
                    for step in &construction.steps {
                        proof = proof.apply_step(step.clone())?;
                    }
                    let certificate = proof.certificate_since(&checkpoint)?;
                    let result = proof.into_execution_context()?;
                    state = result.state;
                    requirement_pure_facts = result.pure_facts;
                    replay = result.replay;
                    branch_path = result.branch_path;
                    for step in certificate.steps() {
                        replay.proof_certificate_builder.push_step(step.clone());
                    }
                    replay.proof_certificate_builder.last_step_entry = construction.last_step_entry;
                    assumptions = assumptions_from_propositions(&requirement_pure_facts);
                    let slice = end_tactic_surface_scope(
                        &mut replay,
                        scope.take().expect("tactic scope is open"),
                    );
                    if capture_this_tactic {
                        finish_tactic_expansion_capture(
                            expansion_capture.as_deref_mut(),
                            &slice,
                            false,
                        );
                    }
                    continue;
                }
                let result = complete_smart_tactic(
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
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
                    construction,
                    false,
                    true,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths => {
                let construction_environments = Some(ConstructionEnvironments {
                    predicate_environment,
                    click_function_environment,
                });
                let planning_builder =
                    |certificate_facts: &[Proposition]| ProofCertificateBuilder {
                        last_step_entry: replay.proof_certificate_builder.last_step_entry.clone(),
                        certificate_facts: ProofFactStore::from_ordered(certificate_facts.to_vec()),
                        ..ProofCertificateBuilder::default()
                    };
                let mut planning_replay = replay.clone();
                planning_replay.planned_statement_transitions.clear();
                planning_replay.proof_certificate_builder =
                    planning_builder(&requirement_pure_facts).into();
                let mut planning_state = state.clone();
                let mut planning_facts = requirement_pure_facts.clone();
                let force_all_paths = matches!(tactic, ProofTactic::SmartExecuteAllPaths);
                let direct_result = (!force_all_paths).then(|| {
                    execute_rest_from_execution_point(
                        &mut planning_replay,
                        &mut planning_state,
                        &mut planning_facts,
                        function_block,
                        function,
                        parsed_function.parameters(),
                        arguments,
                        function_environment,
                        claim_label,
                        tactic_index,
                        construction_environments,
                    )
                });
                if direct_result.is_none_or(|result| result.is_err()) {
                    planning_replay = replay.clone();
                    planning_replay.planned_statement_transitions.clear();
                    planning_replay.proof_certificate_builder =
                        planning_builder(&requirement_pure_facts).into();
                    planning_state = state.clone();
                    planning_facts = requirement_pure_facts.clone();
                    bounded_execute_from_execution_point(
                        &mut planning_replay,
                        &mut planning_state,
                        &mut planning_facts,
                        function_block,
                        function,
                        parsed_function.parameters(),
                        arguments,
                        function_environment,
                        claim_label,
                        tactic_index,
                        StatementPrerequisitePolicy::Planning,
                        construction_environments,
                    )?;
                }
                let construction =
                    std::mem::take(&mut planning_replay.proof_certificate_builder).into_value();
                if construction.blocker.is_none()
                    && !construction.steps.is_empty()
                    && construction.steps.iter().all(|step| {
                        matches!(
                            step,
                            SimpleProofStep::UnfoldPredicate(_)
                                | SimpleProofStep::TransportUsing { .. }
                                | SimpleProofStep::StepUsing(_)
                        )
                    })
                    && construction
                        .steps
                        .iter()
                        .any(|step| matches!(step, SimpleProofStep::StepUsing(_)))
                {
                    let mut proof = Proof::for_execution_frontier(
                        claim_label,
                        tactic_index,
                        ProofReplayContext {
                            state,
                            pure_facts: requirement_pure_facts,
                            replay,
                            branch_path,
                        },
                        function_block,
                        function,
                        parsed_function,
                        arguments,
                        function_environment,
                        predicate_environment,
                        click_function_environment,
                        theorem_environment,
                    );
                    let checkpoint = proof.checkpoint();
                    for step in &construction.steps {
                        proof = proof.apply_step(step.clone())?;
                    }
                    let certificate = proof.certificate_since(&checkpoint)?;
                    let result = proof.into_execution_context()?;
                    state = result.state;
                    requirement_pure_facts = result.pure_facts;
                    replay = result.replay;
                    branch_path = result.branch_path;
                    for step in certificate.steps() {
                        replay.proof_certificate_builder.push_step(step.clone());
                    }
                    replay.proof_certificate_builder.last_step_entry = construction.last_step_entry;
                    assumptions = assumptions_from_propositions(&requirement_pure_facts);
                    let slice = end_tactic_surface_scope(
                        &mut replay,
                        scope.take().expect("tactic scope is open"),
                    );
                    if capture_this_tactic {
                        finish_tactic_expansion_capture(
                            expansion_capture.as_deref_mut(),
                            &slice,
                            false,
                        );
                    }
                    continue;
                }
                let result = complete_smart_tactic(
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
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
                    construction,
                    false,
                    true,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ExecuteUntil(region_ref) => {
                let code_region =
                    resolve_code_region_ref(function_block, region_ref, claim_label, tactic_index)?;
                let CodeRegion::Statement(statement_index) = code_region else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `execute_until` expects a statement region"
                    )));
                };
                let mut planning_replay = replay.clone();
                planning_replay.planned_statement_transitions.clear();
                planning_replay.proof_certificate_builder = ProofCertificateBuilder {
                    last_step_entry: replay.proof_certificate_builder.last_step_entry.clone(),
                    certificate_facts: ProofFactStore::from_ordered(requirement_pure_facts.clone()),
                    ..ProofCertificateBuilder::default()
                }
                .into();
                let mut planning_state = state.clone();
                let mut planning_facts = requirement_pure_facts.clone();
                execute_until_statement(
                    &mut planning_replay,
                    &mut planning_state,
                    &mut planning_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    function_environment,
                    statement_index,
                    claim_label,
                    tactic_index,
                    StatementPrerequisitePolicy::Planning,
                    Some(ConstructionEnvironments {
                        predicate_environment,
                        click_function_environment,
                    }),
                )?;
                let construction =
                    std::mem::take(&mut planning_replay.proof_certificate_builder).into_value();
                if construction.blocker.is_none()
                    && !construction.steps.is_empty()
                    && construction.steps.iter().all(|step| {
                        matches!(
                            step,
                            SimpleProofStep::UnfoldPredicate(_)
                                | SimpleProofStep::TransportUsing { .. }
                                | SimpleProofStep::StepUsing(_)
                        )
                    })
                    && construction
                        .steps
                        .iter()
                        .any(|step| matches!(step, SimpleProofStep::StepUsing(_)))
                {
                    let mut proof = Proof::for_execution_frontier(
                        claim_label,
                        tactic_index,
                        ProofReplayContext {
                            state,
                            pure_facts: requirement_pure_facts,
                            replay,
                            branch_path,
                        },
                        function_block,
                        function,
                        parsed_function,
                        arguments,
                        function_environment,
                        predicate_environment,
                        click_function_environment,
                        theorem_environment,
                    );
                    let checkpoint = proof.checkpoint();
                    for step in &construction.steps {
                        proof = proof.apply_step(step.clone())?;
                    }
                    let certificate = proof.certificate_since(&checkpoint)?;
                    let result = proof.into_execution_context()?;
                    state = result.state;
                    requirement_pure_facts = result.pure_facts;
                    replay = result.replay;
                    branch_path = result.branch_path;
                    for step in certificate.steps() {
                        replay.proof_certificate_builder.push_step(step.clone());
                    }
                    replay.proof_certificate_builder.last_step_entry = construction.last_step_entry;
                    assumptions = assumptions_from_propositions(&requirement_pure_facts);
                    let slice = end_tactic_surface_scope(
                        &mut replay,
                        scope.take().expect("tactic scope is open"),
                    );
                    if capture_this_tactic {
                        finish_tactic_expansion_capture(
                            expansion_capture.as_deref_mut(),
                            &slice,
                            false,
                        );
                    }
                    continue;
                }
                let result = complete_smart_tactic(
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
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
                    construction,
                    false,
                    true,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::SmartFrame(region_ref) => {
                if region_ref.is_some() {
                    let proof = ProofCertificate::from_proof_tactics(&[ProofTactic::FrameUsing {
                        region: region_ref.clone(),
                        premises: Vec::new(),
                    }])
                    .expect("exact frame is a simple tactic");
                    let construction = ProofCertificateBuilder {
                        steps: proof.steps().to_vec(),
                        last_step_entry: replay.proof_certificate_builder.last_step_entry.clone(),
                        ..ProofCertificateBuilder::default()
                    };
                    let result = complete_smart_tactic(
                        ProofReplayContext {
                            state,
                            pure_facts: requirement_pure_facts,
                            replay,
                            branch_path,
                        },
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
                        construction,
                        false,
                        true,
                    )?;
                    state = result.state;
                    requirement_pure_facts = result.pure_facts;
                    replay = result.replay;
                    branch_path = result.branch_path;
                    assumptions = assumptions_from_propositions(&requirement_pure_facts);
                    let slice = end_tactic_surface_scope(
                        &mut replay,
                        scope.take().expect("tactic scope is open"),
                    );
                    if capture_this_tactic {
                        finish_tactic_expansion_capture(
                            expansion_capture.as_deref_mut(),
                            &slice,
                            false,
                        );
                    }
                    continue;
                }
                require_function_exit(&replay, claim_label, tactic_index, "frame")?;
                let Some(effect_claim) = claims
                    .iter()
                    .find(|claim| matches!(claim, FunctionClaimRef::Effect(_, _)))
                else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `frame` has no effect claim to prove"
                    )));
                };
                let FunctionClaimRef::Effect(_, effect_clause) = effect_claim else {
                    unreachable!("selected claim must be an effect claim")
                };
                let execution = replay
                    .execution()
                    .expect("function-exit replay should contain an execution");
                let pre_state = replay.old_reference_state(&state);
                let mut path_derivations = Vec::with_capacity(execution.paths().len());
                for (path_index, path) in execution.paths().iter().enumerate() {
                    if !path.obligations().is_empty() {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `frame` cannot plan from an execution path with unresolved obligations"
                        )));
                    }
                    let mut path_facts = requirement_pure_facts.clone();
                    path_facts.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
                    let mut compatible = true;
                    if !replay.case_assumptions.is_empty() {
                        let CFunctionOutcome::Return {
                            value: result,
                            state: post_state,
                        } = path.outcome()
                        else {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: proof-branch `frame` requires a return outcome"
                            )));
                        };
                        for case in &replay.case_assumptions {
                            let fact = if let Some(fact) = &case.fact {
                                fact.clone()
                            } else {
                                let condition = lower_outcome_proposition_with_program_points(
                                    parsed_function.parameters(),
                                    arguments,
                                    pre_state,
                                    post_state,
                                    result,
                                    &path_facts,
                                    &case.condition,
                                    predicate_environment,
                                    click_function_environment,
                                    &replay.program_point_states,
                                )
                                .map_err(|message| {
                                    ClickError::new(format!(
                                        "`{claim_label}` tactic {tactic_index}: could not align frame path with proof branch: {message}"
                                    ))
                                })?;
                                if case.value {
                                    condition
                                } else {
                                    Proposition::Not(Box::new(condition))
                                }
                            };
                            let mut case_facts = path_facts.clone();
                            case_facts.push(fact.clone());
                            if path_facts
                                .iter()
                                .any(|available| propositions_are_exact_negations(available, &fact))
                                || assumptions_from_propositions(&case_facts)
                                    .derive_proposition(&false_proposition())
                                    .is_some()
                            {
                                compatible = false;
                                break;
                            }
                            path_facts.push(fact);
                        }
                    }
                    if !compatible {
                        // A frame planned inside one proof branch owns only
                        // execution outcomes compatible with that branch.
                        continue;
                    }
                    path_derivations.push(plan_effect_clause_derivations(
                        claim_label,
                        path_index,
                        path.effect_facts(),
                        &path_facts,
                        effect_clause.effect(),
                        parsed_function.parameters(),
                        arguments,
                        pre_state,
                        path.outcome(),
                    )?);
                }
                // A contextual frame certificate is constructed against the
                // current context; construction-time surface recordings are
                // transient, so they run on a clone whose builder is seeded
                // with the current surface branch skeleton.
                let mut construction_replay = replay.clone();
                construction_replay.proof_certificate_builder = ProofCertificateBuilder {
                    steps: surface_branch_skeleton(&replay.proof_certificate_builder.steps),
                    last_step_entry: replay.proof_certificate_builder.last_step_entry.clone(),
                    certificate_facts: ProofFactStore::from_ordered(requirement_pure_facts.clone()),
                    ..ProofCertificateBuilder::default()
                }
                .into();
                construct_simple_step_for_planned_operation(
                    &mut construction_replay,
                    &state,
                    function_block,
                    parsed_function.parameters(),
                    arguments,
                    ConstructionEnvironments {
                        predicate_environment,
                        click_function_environment,
                    },
                    &ConstructionEvidence::CertifiedFrame(path_derivations),
                );
                let construction =
                    std::mem::take(&mut construction_replay.proof_certificate_builder).into_value();
                // A branched contextual frame merges its synthesized branch
                // with the existing surface branch here, and a frame inside
                // an `open { ... }` block merges so its steps are captured
                // into the block's nested proof. A flat top-level exit frame
                // is recorded by the drain instead: its independent replay
                // defers the frame work, the deferrals carry into this
                // replay, and the drain spells the same steps in deferral
                // order — merging here would misplace them before every
                // earlier deferred tactic.
                let merge_construction = replay.open_scopes > 0
                    || matches!(construction.steps.as_slice(), [SimpleProofStep::If { .. }]);
                // The construction is still the tactic's own standalone
                // expansion even when the drain records the claim-level
                // steps; a selected `frame()` capture takes it directly.
                let capture_construction =
                    (!merge_construction && capture_this_tactic).then(|| construction.clone());
                let result = complete_smart_tactic(
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
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
                    construction,
                    true,
                    merge_construction,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
                if let Some(construction) = capture_construction {
                    finish_tactic_expansion_capture(
                        expansion_capture.as_deref_mut(),
                        &construction,
                        false,
                    );
                }
            }
            ProofTactic::FrameUsing {
                region: region_ref,
                premises: surface_premises,
            } => {
                let mut frame_facts = Vec::new();
                if !surface_premises.is_empty() {
                    let all_pure_facts = requirement_pure_facts.clone();
                    let pre_state = replay.old_reference_state(&state).clone();
                    let deferred_ordered_exit =
                        replay.ordered_finalization && replay.is_at_function_exit();
                    for surface_premise in surface_premises {
                        let premise = if let Some(recorded) = replay
                            .surface_propositions
                            .available_kernel_matching(surface_premise, |kernel| {
                                assumptions.contains_assumed_exact(kernel)
                            }) {
                            recorded.clone()
                        } else {
                            lower_point_proposition(
                                surface_premise,
                                &all_pure_facts,
                                parsed_function.parameters(),
                                arguments,
                                &pre_state,
                                &state,
                                None,
                                &replay.program_point_states,
                                predicate_environment,
                                click_function_environment,
                            )
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "`{claim_label}` tactic {tactic_index}: could not lower `frame using` premise `{}`: {message}",
                                    super::printing::source_click_proposition(surface_premise)
                                ))
                            })?
                        };
                        replay
                            .surface_propositions
                            .record_lowering(surface_premise, &premise)?;
                        if !deferred_ordered_exit
                            && !exact_fact_is_available_across_effects(
                                &premise,
                                &all_pure_facts,
                                &replay.effect_facts,
                            )
                            && materialization_equivalent_available_fact(&premise, &all_pure_facts)
                                .is_none()
                        {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `frame using` requires an exact premise: {}",
                                describe_missing_pure_fact(
                                    &premise,
                                    &all_pure_facts,
                                    state.resources().facts(),
                                    parsed_function.parameters(),
                                    arguments,
                                    &replay.effect_facts,
                                )
                            )));
                        }
                        if !frame_facts.contains(&premise) {
                            frame_facts.push(premise);
                        }
                    }
                } else {
                    frame_facts = requirement_pure_facts.clone();
                }
                let mut loop_effect_facts = frame_facts.clone();
                loop_effect_facts.extend(
                    replay
                        .effect_facts
                        .iter()
                        .map(|fact| fact.proposition().clone()),
                );
                loop_effect_facts.sort();
                loop_effect_facts.dedup();
                if let Some(goal) = replay.loop_effect_goal.as_mut() {
                    if region_ref.is_some() {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: a structural effect proof must use unqualified `frame()`"
                        )));
                    }
                    if goal.closed {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: the structural effect goal was closed more than once"
                        )));
                    }
                    c_loop_effects_hold_at_back_edge(
                        &goal.before_state,
                        &state,
                        std::slice::from_ref(&goal.check),
                        &loop_effect_facts,
                        &assumptions_from_propositions(&loop_effect_facts),
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `frame()` failed: {message}"
                        ))
                    })?;
                    goal.closed = true;
                    end_tactic_surface_scope(
                        &mut replay,
                        scope.take().expect("tactic scope is open"),
                    );
                    continue;
                }
                require_function_exit(&replay, claim_label, tactic_index, "frame")?;
                // A code region qualifying `frame` refers to loop effect
                // clauses, which current syntax declares only through
                // frontier-local `loop` tactics earlier in this proof; bind
                // them so region resolution and validation see them.
                let frame_function_block = (!replay.frontier_loop_clauses.is_empty()).then(|| {
                    function_block
                        .with_bound_frontier_loop_clauses(&replay.frontier_loop_clauses.to_vec())
                });
                let frame_function_block = frame_function_block.as_ref().unwrap_or(function_block);
                let code_region = region_ref
                    .as_ref()
                    .map(|region_ref| {
                        resolve_code_region_ref(
                            frame_function_block,
                            region_ref,
                            claim_label,
                            tactic_index,
                        )
                    })
                    .transpose()?;
                if replay.ordered_finalization
                    && replay.is_at_function_exit()
                    && matches!(code_region, None | Some(CodeRegion::Function))
                {
                    if !replay.grouped_contract {
                        validate_frame_code_region(
                            frame_function_block,
                            parsed_function,
                            code_region,
                            &claims[0],
                            claim_label,
                            tactic_index,
                        )?;
                    }
                    let Some(effect_claim) = claims
                        .iter()
                        .find(|claim| matches!(claim, FunctionClaimRef::Effect(_, _)))
                    else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `frame()` has no effect claim to prove"
                        )));
                    };
                    validate_frame_code_region(
                        frame_function_block,
                        parsed_function,
                        code_region,
                        effect_claim,
                        claim_label,
                        tactic_index,
                    )?;
                    let deferred = if surface_premises.is_empty() {
                        PostExecutionTactic::Frame
                    } else {
                        PostExecutionTactic::FrameUsing {
                            region: region_ref.clone(),
                            premises: surface_premises.clone(),
                        }
                    };
                    replay.defer_post_execution(tactic_index, source_index, deferred);
                    end_tactic_surface_scope(
                        &mut replay,
                        scope.take().expect("tactic scope is open"),
                    );
                    continue;
                }
                let effect_claims = claims
                    .iter()
                    .filter(|claim| matches!(claim, FunctionClaimRef::Effect(_, _)))
                    .collect::<Vec<_>>();
                if effect_claims.is_empty() {
                    validate_frame_code_region(
                        frame_function_block,
                        parsed_function,
                        code_region,
                        &claims[0],
                        claim_label,
                        tactic_index,
                    )?;
                }
                for claim in effect_claims {
                    validate_frame_code_region(
                        frame_function_block,
                        parsed_function,
                        code_region,
                        claim,
                        claim_label,
                        tactic_index,
                    )?;
                    match code_region {
                        None | Some(CodeRegion::Function) => {
                            validate_function_frame_tactic(
                                replay.execution().expect("execution should exist"),
                                claim,
                                claim_label,
                                tactic_index,
                                parsed_function.parameters(),
                                arguments,
                                &state,
                                &frame_facts,
                            )?;
                        }
                        Some(CodeRegion::Loop(_)) => {}
                        Some(CodeRegion::Statement(_)) => {}
                    }
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    let region = region_ref.clone().ok_or_else(|| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: contextual function `frame()` should have been deferred earlier"
                        ))
                    })?;
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::FrameRegion(region),
                    );
                }
            }
            ProofTactic::UnfoldPredicate(name) => {
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::UnfoldPredicate(name.clone()),
                    );
                    end_tactic_surface_scope(
                        &mut replay,
                        scope.take().expect("tactic scope is open"),
                    );
                    continue;
                }
                let proof = Proof::for_execution_frontier(
                    claim_label,
                    tactic_index,
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    function,
                    parsed_function,
                    arguments,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                );
                let proof = proof.apply_step(SimpleProofStep::UnfoldPredicate(name.clone()))?;
                let result = proof.into_execution_context()?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ApplyTheorem(application) => {
                // A mid-execution smart `apply` is planned into an explicit
                // `apply using` and checked through `complete_smart_tactic`
                // before this match (see the `ApplyTheorem` pre-pass above),
                // so only the function-exit form reaches this arm.
                if theorem_environment.get(&application.name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unknown theorem `{}`",
                        application.name
                    )));
                }
                debug_assert!(replay.is_at_function_exit());
                if replay.ordered_finalization {
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Apply(application.clone()),
                    );
                } else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: post-execution `apply` is not available in this region proof"
                    )));
                }
            }
            ProofTactic::ApplyTheoremUsing {
                application,
                premises,
            } => {
                if theorem_environment.get(&application.name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unknown theorem `{}`",
                        application.name
                    )));
                }
                if replay.is_at_function_exit() {
                    if replay.ordered_finalization {
                        replay.defer_post_execution(
                            tactic_index,
                            source_index,
                            PostExecutionTactic::ApplyUsing {
                                application: application.clone(),
                                premises: premises.clone(),
                            },
                        );
                        end_tactic_surface_scope(
                            &mut replay,
                            scope.take().expect("tactic scope is open"),
                        );
                        continue;
                    }
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: post-execution `apply using` is not available in this region proof"
                    )));
                }
                let proof = Proof::for_execution_frontier(
                    claim_label,
                    tactic_index,
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    function,
                    parsed_function,
                    arguments,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                );
                let proof = proof.apply_step(SimpleProofStep::ApplyTheoremUsing {
                    application: application.clone(),
                    premises: premises.clone(),
                })?;
                let result = proof.into_execution_context()?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::FoldResource(resource) => {
                if replay.is_at_function_exit() {
                    if replay.ordered_finalization {
                        replay.defer_post_execution(
                            tactic_index,
                            source_index,
                            PostExecutionTactic::Fold(resource.clone()),
                        );
                    } else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: post-execution `fold` is not available in this region proof"
                        )));
                    }
                } else {
                    let pre_state = replay.old_reference_state(&state).clone();
                    state = fold_composite_resource_at_current_point(
                        resource_environment,
                        resource,
                        claim_label,
                        tactic_index,
                        &requirement_pure_facts,
                        parsed_function.parameters(),
                        arguments,
                        &pre_state,
                        state,
                        predicate_environment,
                        click_function_environment,
                        &replay.unfolded_predicates,
                    )?;
                }
            }
            ProofTactic::Have(have) => {
                if replay.is_at_function_exit() {
                    if replay.ordered_finalization {
                        replay.defer_post_execution(
                            tactic_index,
                            source_index,
                            PostExecutionTactic::Have(have.clone()),
                        );
                    } else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: post-execution `have` is not available in this region proof"
                        )));
                    }
                    end_tactic_surface_scope(
                        &mut replay,
                        scope.take().expect("tactic scope is open"),
                    );
                    continue;
                }
                let _have_span = crate::instrumentation::OperationTiming::new(
                    "have",
                    claim_label,
                    "contract have replay",
                );
                let mut have_facts = requirement_pure_facts.clone();
                have_facts.extend(
                    replay
                        .effect_facts
                        .iter()
                        .map(|fact| fact.proposition().clone()),
                );
                for fact in replay.surface_propositions.kernel_facts() {
                    if !have_facts.contains(fact) {
                        have_facts.push(fact.clone());
                    }
                }
                let checked_proof_result = checked_have_with_proof(
                    have,
                    theorem_environment,
                    claim_label,
                    tactic_index,
                    &have_facts,
                    parsed_function.parameters(),
                    arguments,
                    replay.old_reference_state(&state),
                    &state,
                    None,
                    &replay,
                    &replay.surface_propositions,
                    predicate_environment,
                    click_function_environment,
                    function_block.requires(),
                    function_block.requirement_label_indices(),
                )?;
                let smart_unfolds = smart_simp_unfold_prefix(&have.proof);
                // Smart search and certificate construction are one event:
                // the goal is proved exactly when its evidence has been
                // spelled as a replayable ProofCertificate.
                let smart_result = match (&checked_proof_result, &smart_unfolds) {
                    (Some(_), _) => None,
                    (None, Some(unfolded_predicates)) => Some(construct_smart_have_certificate(
                        &mut replay,
                        &state,
                        &have_facts,
                        parsed_function.parameters(),
                        arguments,
                        predicate_environment,
                        click_function_environment,
                        have,
                        claim_label,
                        tactic_index,
                        unfolded_predicates,
                    )?),
                    (None, None) => None,
                };
                let (fact, surface_certificate, certificate_already_checked) =
                    match (checked_proof_result, smart_result) {
                        (Some((fact, certificate)), _) => (fact, certificate, true),
                        (None, Some((fact, certificate))) => (fact, Some(certificate), false),
                        (None, None) => {
                            let fact = prove_have_at_current_point(
                                have,
                                theorem_environment,
                                claim_label,
                                tactic_index,
                                &have_facts,
                                &replay.effect_facts,
                                parsed_function.parameters(),
                                arguments,
                                replay.old_reference_state(&state),
                                &state,
                                &replay.program_point_states,
                                &replay.surface_propositions,
                                predicate_environment,
                                click_function_environment,
                                function_block.requires(),
                            )?;
                            let certificate = surface_smart_apply_have_certificate(
                                &mut replay,
                                &state,
                                &have_facts,
                                parsed_function.parameters(),
                                arguments,
                                predicate_environment,
                                click_function_environment,
                                theorem_environment,
                                claim_label,
                                tactic_index,
                                have,
                                &fact,
                            )?;
                            (fact, certificate, false)
                        }
                    };
                // A body that is neither simple nor covered by the smart
                // lowerings above (for example, a richer proof-level `if`
                // whose cases close through unsupported smart search) must
                // still yield a replayed simple certificate; otherwise the
                // tactic fails instead of silently losing the enclosing
                // proof's expansion.
                let surface_certificate = match surface_certificate {
                    Some(certificate) => Some(certificate),
                    None if ProofCertificate::from_proof_tactics(std::slice::from_ref(tactic))
                        .is_err() =>
                    {
                        Some(certify_general_smart_have(
                            have,
                            &fact,
                            theorem_environment,
                            claim_label,
                            tactic_index,
                            &have_facts,
                            &replay.effect_facts,
                            parsed_function.parameters(),
                            arguments,
                            replay.old_reference_state(&state),
                            &state,
                            &replay.program_point_states,
                            &replay.surface_propositions,
                            predicate_environment,
                            click_function_environment,
                            function_block.requires(),
                        )?)
                    }
                    None => None,
                };
                if let Some(certificate) = surface_certificate {
                    if !certificate_already_checked {
                        let replay_certificate = |certificate: &ProofCertificate| {
                            replay_proof_certificate(
                                ProofReplayContext {
                                    state: state.clone(),
                                    // Replay from the same certified context
                                    // used to plan the smart `have`. In
                                    // particular, field-derived loadability may
                                    // depend on previously established surface
                                    // facts or exact execution effects that are
                                    // not part of the function's requirements.
                                    pure_facts: have_facts.clone(),
                                    replay: replay.clone(),
                                    branch_path: branch_path.clone(),
                                },
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
                                certificate,
                            )
                        };
                        pure_goal_proof_certificate_gateway(
                            claim_label,
                            || Ok(certificate.clone()),
                            replay_certificate,
                        )?;
                    }
                    for step in certificate.steps() {
                        replay.proof_certificate_builder.push_step(step.clone());
                    }
                }
                // `have ... by { apply(...) using { ... } }` replays its
                // nested certificate on a clone, so carry the kernel-issued
                // standard-theorem authority back to the enclosing entry
                // replay explicitly. The proved fact itself is recorded only
                // after the nested certificate has passed the gateway below.
                if replay
                    .frontier
                    .execution_start_state
                    .as_ref()
                    .is_none_or(|start| start == &state)
                    && let SourceProof::Script(have_tactics) = &have.proof
                {
                    for have_tactic in have_tactics {
                        let ProofTactic::ApplyTheoremUsing { application, .. } = have_tactic else {
                            continue;
                        };
                        if let Some(derivation) =
                            kernel_standard_theorem_derivation_at_current_point(
                                theorem_environment,
                                application,
                                parsed_function.parameters(),
                                arguments,
                                replay.old_reference_state(&state),
                                &state,
                                &replay.program_point_states,
                                predicate_environment,
                                click_function_environment,
                                &have_facts,
                            )?
                        {
                            let mut conclusion = derivation.proposition();
                            while let Proposition::Implies(_, body) = conclusion {
                                conclusion = body;
                            }
                            replay
                                .function_entry_execution_prerequisites
                                .insert(conclusion.clone());
                            replay.function_entry_derivations.insert(derivation);
                        }
                    }
                }
                // Do not teach certificate replay the search-time lowering of
                // this goal until the generated surface certificate has
                // independently replayed. Otherwise a richer planner
                // materialization can make a nontrivial snapshot equality
                // appear reflexive and circularly validate `normalize()`.
                replay
                    .surface_propositions
                    .record_lowering(&have.proposition, &fact)?;
                replay
                    .proof_certificate_builder
                    .certificate_facts
                    .insert(fact.clone());
                if replay
                    .frontier
                    .execution_start_state
                    .as_ref()
                    .is_none_or(|start| start == &state)
                    && let Some(derivation) = prove_pure_proposition_from_context(
                        &assumptions_from_propositions(&have_facts),
                        &fact,
                    )
                {
                    replay
                        .function_entry_execution_prerequisites
                        .insert(fact.clone());
                    replay.function_entry_derivations.insert(derivation);
                }
                if !requirement_pure_facts.contains(&fact) {
                    requirement_pure_facts.push(fact.clone());
                    assumptions = assumptions.assume_proposition(fact);
                }
            }
            ProofTactic::If(_) | ProofTactic::Branch(_) | ProofTactic::Open(_) => {
                unreachable!("structured tactics are represented by internal proof nodes")
            }
            ProofTactic::Loop(_) => {
                unreachable!("frontier-local loops are replayed between linear tactic chunks")
            }
            ProofTactic::Witness(_) => {
                if replay.grouped_contract {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: top-level `witness` is not available in a grouped proof; use it inside `have proposition by {{ ... }}`"
                    )));
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    let ProofTactic::Witness(witness) = tactic else {
                        unreachable!()
                    };
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Witness(witness.clone()),
                    );
                    end_tactic_surface_scope(
                        &mut replay,
                        scope.take().expect("tactic scope is open"),
                    );
                    continue;
                }
                require_function_exit(&replay, claim_label, tactic_index, "witness")?;
            }
            ProofTactic::Choose(_) => {
                if replay.grouped_contract {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: top-level `choose` is not available in a grouped proof; use it inside `have proposition by {{ ... }}`"
                    )));
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    let ProofTactic::Choose(choice) = tactic else {
                        unreachable!()
                    };
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Choose(choice.clone()),
                    );
                    end_tactic_surface_scope(
                        &mut replay,
                        scope.take().expect("tactic scope is open"),
                    );
                    continue;
                }
                require_function_exit(&replay, claim_label, tactic_index, "choose")?;
            }
            ProofTactic::Assumption | ProofTactic::Normalize | ProofTactic::Rewrite(_) => {
                if !replay.region_proof {
                    require_function_exit(&replay, claim_label, tactic_index, tactic_name(tactic))?;
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    let post_tactic = match tactic {
                        ProofTactic::Assumption => PostExecutionTactic::Assumption,
                        ProofTactic::Normalize => PostExecutionTactic::Normalize,
                        ProofTactic::Rewrite(equality) => {
                            PostExecutionTactic::Rewrite(equality.clone())
                        }
                        _ => unreachable!(),
                    };
                    replay.defer_post_execution(tactic_index, source_index, post_tactic);
                }
            }
            ProofTactic::Intro
            | ProofTactic::Extract(_)
            | ProofTactic::InstantiateUsing { .. }
            | ProofTactic::Split
            | ProofTactic::Left
            | ProofTactic::Right
            | ProofTactic::Enumerate
            | ProofTactic::Cases(_)
            | ProofTactic::Contradiction(_)
            | ProofTactic::SimpUsing(_) => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{}` is only available while proving a pure goal, such as inside `have ... by`",
                    tactic_name(tactic)
                )));
            }
            ProofTactic::CloseInvariants => {
                let proof = Proof::for_execution_frontier(
                    claim_label,
                    tactic_index,
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    function,
                    parsed_function,
                    arguments,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                );
                let proof = proof.apply_step(SimpleProofStep::CloseInvariants)?;
                let result = proof.into_execution_context()?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                replay.invariant_closer_step = Some(InvariantCloserStep {
                    tactic_index,
                    source_index,
                    statement_index: replay.frontier.next_statement_index,
                });
            }
            ProofTactic::Induct { .. }
            | ProofTactic::ApplyInduction { .. }
            | ProofTactic::CloseInduction => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{}` is available only in a pure theorem proof",
                    tactic_name(tactic)
                )));
            }
            ProofTactic::Simp => {
                if !replay.region_proof {
                    require_function_exit(&replay, claim_label, tactic_index, "simp")?;
                }
                if replay.region_proof {
                    replay.region_simp = Some((tactic_index, source_index));
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Simp,
                    );
                }
            }
        }
        let slice =
            end_tactic_surface_scope(&mut replay, scope.take().expect("tactic scope is open"));
        if capture_this_tactic && !deferred_post_execution && !deferred_region_simp {
            finish_tactic_expansion_capture(expansion_capture.as_deref_mut(), &slice, false);
        }
    }

    if crate::instrumentation::deadline_exceeded() {
        return Err(ClickError::new(format!(
            "tactic budget exhausted: {}",
            crate::instrumentation::deadline_context()
        )));
    }

    Ok(ProofReplayContext {
        state,
        pure_facts: requirement_pure_facts,
        replay,
        branch_path,
    })
}
