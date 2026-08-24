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
    let sentinel = CStatement::Return(CExpression::Value(int32(0)));
    let remaining = c_seq(body.clone(), sentinel.clone());
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
                remaining: remaining.into(),
            },
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
        let at_back_edge = matches!(
            &context.replay.frontier.point,
            ProofExecutionPoint::StatementEntry { remaining } if remaining.as_ref() == &sentinel
        ) && context.replay.frontier.continuations.is_empty();
        if at_back_edge {
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

#[allow(clippy::too_many_arguments)]
fn verify_structural_effect_proof(
    _expansion_capture: Option<&mut ExpansionCapture>,
    loop_index: usize,
    item_index: usize,
    item: &StructuralItem,
    check: &CLoopEffectCheck,
    body: &CStatement,
    before_state: &CState,
    context: &ProofReplayContext,
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
    let case_path = context
        .replay
        .case_assumptions
        .iter()
        .map(|choice| ProofCaseChoice {
            condition: choice.condition.clone(),
            value: choice.value,
        })
        .collect::<Vec<_>>();
    // Structural effects are checked once per already-certified preservation
    // path. The source cursor selects that path's syntactic leaf; it owns no
    // facts or successor state. Every selected operation still advances the
    // path's Proof, and the caller reconstructs the structured Surface tree
    // from the checked leaf provenance after all paths complete.
    let certificate = certificate_leaf_for_case_path(
        &claim_label,
        &source_certificate.to_proof_tactics(),
        &case_path,
    )?;
    // The exact linear subset is checked transactionally on one Proof. Smart
    // frame syntax selects its bounded explicit premises from that Proof;
    // explicit scripts are authoritative, including an empty `using` block.
    // Only structurally unsupported scripts retain compatibility replay.
    let proof_steps_supported = certificate.steps().iter().all(|step| {
        matches!(
            step,
            SimpleProofStep::Mark(_)
                | SimpleProofStep::ApplyTheoremUsing { .. }
                | SimpleProofStep::TransportUsing { .. }
                | SimpleProofStep::UnfoldPredicate(_)
                | SimpleProofStep::UnfoldResource(_)
                | SimpleProofStep::FoldResource(_)
                | SimpleProofStep::ObserveResource(_)
                | SimpleProofStep::FrameUsing { .. }
        )
    });
    if proof_steps_supported {
        let mut replay = context.replay.clone();
        replay.proof_site = Some(site.clone());
        replay.loop_effect_goal = Some(LoopEffectReplayGoal {
            before_state: before_state.clone(),
            check: check.clone(),
            closed: false,
        });
        replay.proof_certificate_builder = ProofCertificateBuilder::default().into();
        let root = Proof::for_execution_frontier_with_effect_goals(
            &claim_label,
            0,
            ProofReplayContext {
                state: context.state.clone(),
                pure_facts: context.pure_facts.clone(),
                replay,
                branch_path: context.branch_path.clone(),
            },
            EffectGoalSelection::None,
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
        let checked = if smart_frame {
            root.try_smart_loop_effect_frame_at(body, 0, effect_source_index)?
        } else {
            let mut checked = root;
            for (tactic_index, step) in certificate.steps().iter().enumerate() {
                checked = checked.apply_step_at(
                    step.clone(),
                    tactic_index,
                    effect_source_index + tactic_index,
                )?;
            }
            Some(checked)
        };
        if let Some(checked) = checked {
            if !checked.is_complete() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` structural-effect proof did not close its checked Proof goal"
                )));
            }
            return Ok(checked.certificate());
        }
    }
    let program = build_internal_proof_from_source_index(
        &certificate.to_proof_tactics(),
        effect_source_index,
    )?;
    let mut replay = context.replay.clone();
    replay.proof_site = Some(site);
    replay.loop_effect_goal = Some(LoopEffectReplayGoal {
        before_state: before_state.clone(),
        check: check.clone(),
        closed: false,
    });
    replay.proof_certificate_builder = ProofCertificateBuilder::default().into();
    let replayed = execute_internal_proof(
        &program,
        ProofReplayContext {
            state: context.state.clone(),
            pure_facts: context.pure_facts.clone(),
            replay,
            branch_path: context.branch_path.clone(),
        },
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
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` structural-effect certificate failed ordinary replay:\n{}\n{}",
            format_proof_certificate(&certificate),
            error.message()
        ))
    })?;
    if replayed.is_empty()
        || replayed.iter().any(|context| {
            !context
                .replay
                .loop_effect_goal
                .as_ref()
                .is_some_and(|goal| goal.closed)
        })
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` structural-effect certificate did not close every replay path:\n{}\n  replay paths: {}\n  closed paths: {}",
            format_proof_certificate(&certificate),
            replayed.len(),
            replayed
                .iter()
                .filter(|context| context
                    .replay
                    .loop_effect_goal
                    .as_ref()
                    .is_some_and(|goal| goal.closed))
                .count(),
        )));
    }
    Ok(certificate)
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
    // Positive closer results from the planner half, keyed by the certificate
    // path that produced them. Replay starts from the same loop-entry context
    // and checks every deterministic leaf tactic, so reaching the same case
    // path reproduces the closer inputs without an expensive deep comparison
    // of snapshot-rich states and proposition sets.
    let mut verified_closer_paths: Vec<Vec<ProofCaseChoice>> = Vec::new();
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
    let sentinel = CStatement::Return(CExpression::Value(int32(0)));
    let remaining = c_seq(body.clone(), sentinel.clone());
    let source_layout = SourceExecutionLayout::new(environment.parsed_function.body());
    let loop_body_statement_index = source_layout.loop_body_entry(loop_index).ok_or_else(|| {
        ClickError::new(format!("`{claim_label}` has no source loop({loop_index})"))
    })?;
    let mut replay = TacticReplayState {
        proof_site: Some(preserve_site),
        frontier: ExecutionFrontier {
            point: ProofExecutionPoint::StatementEntry {
                remaining: remaining.into(),
            },
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
    let replay_start = replay.clone();
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
    let mut certificate_paths = Vec::new();
    for context in &contexts {
        let at_back_edge = matches!(
            &context.replay.frontier.point,
            ProofExecutionPoint::StatementEntry { remaining } if remaining.as_ref() == &sentinel
        ) && context.replay.frontier.continuations.is_empty();
        if !at_back_edge {
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
        let (closer_index, closer_source, closer_name, closer_class) =
            if let Some((tactic_index, source_index)) = context.replay.region_simp {
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
                            statement_index: context.replay.frontier.next_statement_index,
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
                statement_index: context.replay.frontier.next_statement_index,
            };
            push_timing_tactic(timing_context.clone());
            TacticTiming {
                claim_label: claim_label.clone(),
                tactic_index: closer_index,
                source_index: closer_source,
                tactic_name: closer_name.to_string(),
                tactic_class: closer_class,
                statement_index: context.replay.frontier.next_statement_index,
                start: std::time::Instant::now(),
                context: timing_context,
            }
        });
        let closer_tactics = if invariant_checks.is_empty()
            || context.replay.region_invariants_closed
        {
            Vec::new()
        } else {
            let mut closer_facts = context.pure_facts.clone();
            closer_facts.extend(
                context
                    .replay
                    .effect_facts
                    .iter()
                    .map(|fact| fact.proposition().clone()),
            );
            closer_facts.extend(crate::kernel::certified_store_equations(
                &context.replay.effect_facts,
            ));
            if let Err(message) = c_loop_invariants_hold_at_back_edge_using(
                &context.state,
                preservation.loop_entry_state(),
                invariant_checks,
                &assumptions_from_propositions(&closer_facts),
            ) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` (loop {loop_index} invariant bundle preservation) could not certify every guarded invariant-lowering path: {message}"
                )));
            }
            verified_closer_paths.push(case_path.clone());
            vec![ProofTactic::CloseInvariants]
        };
        let omitted_frontier_preservation = environment
            .frontier_loop_source
            .is_some_and(|source| source.preserve_source_index.is_none());
        if !omitted_frontier_preservation
            && context.replay.region_simp.is_some_and(|(_, source_index)| {
                tactic_expansion_capture_matches(
                    expansion_capture.as_deref(),
                    context.replay.proof_site.as_ref(),
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
        let surface_tactics =
            ProofCertificate::from_steps(context.replay.proof_certificate_builder.steps.clone())
                .to_proof_tactics();
        let prefix = certificate_leaf_for_case_path(&claim_label, &surface_tactics, &case_path)?;
        let mut leaf_tactics = prefix.to_proof_tactics().to_vec();
        leaf_tactics.extend(closer_tactics);
        let certificate = ProofCertificate::from_proof_tactics(&leaf_tactics).map_err(|error| {
            ClickError::new(format!(
                "`{claim_label}` produced an invalid preservation leaf certificate: {error:?}"
            ))
        })?;
        certificate_paths.push(PathCertificate {
            case_path,
            certificate,
        });
    }
    let certificate = merge_path_aligned_certificates(&claim_label, certificate_paths)?;
    let certificate_program = build_internal_proof(&certificate.to_proof_tactics(), &claim_label)?;
    // This is a detached, deterministic replay of the certificate just
    // produced above. Its local tactic indices start at zero and are not
    // source occurrences in the enclosing proof, so no expansion capture is
    // routed into it: certificate tactic 1 must not be mistaken for enclosing
    // source tactic 1.
    let replayed = execute_internal_proof(
        &certificate_program,
        ProofReplayContext {
            state: preservation.state().clone(),
            pure_facts: pure_facts.to_vec(),
            replay: Box::new(replay_start),
            branch_path: PersistentSequence::default(),
        },
        None,
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
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` preservation certificate failed ordinary replay:\n{}\n{}",
            format_proof_certificate(&certificate),
            error.message()
        ))
    })?;
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
    let mut effect_certificate_paths = vec![Vec::new(); effect_items.len()];
    for context in replayed {
        let at_back_edge = matches!(
            &context.replay.frontier.point,
            ProofExecutionPoint::StatementEntry { remaining } if remaining.as_ref() == &sentinel
        ) && context.replay.frontier.continuations.is_empty();
        if !at_back_edge {
            return Err(ClickError::new(format!(
                "`{claim_label}` replayed certificate did not finish at the loop back edge"
            )));
        }
        if context.replay.region_invariants_closed == invariant_checks.is_empty() {
            return Err(ClickError::new(format!(
                "`{claim_label}` replayed the wrong number of invariant-bundle closers"
            )));
        }
        if !invariant_checks.is_empty() {
            // `close_invariants` only sets a flag while the certificate
            // replays; this is where the bundle is actually re-derived, so
            // this is where that tactic's time is spent. Time it against the
            // tactic's own identity and let `source_tactic_class` classify it.
            let _timing = context.replay.invariant_closer_step.and_then(|step| {
                TacticTiming::new(
                    &claim_label,
                    step.tactic_index,
                    step.source_index,
                    &ProofTactic::CloseInvariants,
                    step.statement_index,
                )
            });
            let case_path = context
                .replay
                .case_assumptions
                .iter()
                .map(|choice| ProofCaseChoice {
                    condition: choice.condition.clone(),
                    value: choice.value,
                })
                .collect::<Vec<_>>();
            let planner_already_verified = std::env::var_os("CLICK_DISABLE_CLOSER_REUSE").is_none()
                && verified_closer_paths.contains(&case_path);
            if !planner_already_verified {
                let mut closer_facts = context.pure_facts.clone();
                closer_facts.extend(
                    context
                        .replay
                        .effect_facts
                        .iter()
                        .map(|fact| fact.proposition().clone()),
                );
                closer_facts.extend(crate::kernel::certified_store_equations(
                    &context.replay.effect_facts,
                ));
                c_loop_invariants_hold_at_back_edge_using(
                    &context.state,
                    preservation.loop_entry_state(),
                    invariant_checks,
                    &assumptions_from_propositions(&closer_facts),
                )
                .map_err(|message| {
                    ClickError::new(format!("`{claim_label}` invariant bundle: {message}"))
                })?;
            }
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
                &context,
                environment,
            )?;
            effect_certificate_paths[effect_index].push(PathCertificate {
                case_path: case_path.clone(),
                certificate: effect_certificate,
            });
        }
    }
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
