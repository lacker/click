use super::*;

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
        function_block.with_bound_frontier_loop_clauses(&replay.frontier_loop_clauses);
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
            remaining: annotated.body().clone(),
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
    expanded_loop.initialize_proof = Some(Proof::Script(
        certificates
            .initialize
            .as_ref()
            .map(|certificate| certificate.to_proof_tactics().to_vec())
            .unwrap_or_else(|| vec![ProofTactic::Assumption]),
    ));
    expanded_loop.preserve_proof = Some(Proof::Script(
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
            item.proof = Proof::Script(certificate.to_proof_tactics().to_vec());
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
                .expect("the current loop always contributes one statement"),
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
        &[],
        None,
        StatementPrerequisitePolicy::Exact,
        StatementFactTransportPolicy::Automatic,
        LoopStepPolicy::ApplyVerifiedRule,
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
        .simple_proof_builder
        .push_source_tactic(ProofTactic::Loop(expanded_loop));
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn replay_linear_tactics(
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
    tactics: &[IndexedTactic],
) -> Result<ProofReplayContext, ClickError> {
    let mut chunk_start = 0;
    for (index, indexed_tactic) in tactics.iter().enumerate() {
        let ProofTactic::Loop(loop_clause) = &indexed_tactic.tactic else {
            continue;
        };
        context = replay_linear_tactics_without_frontier_loops(
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
            &tactics[chunk_start..index],
        )?;
        context = replay_frontier_local_loop_tactic(
            context,
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
    let capture_this_tactic = begin_tactic_expansion_capture(
        source_index,
        &ProofTactic::Loop(loop_clause.clone()),
        &mut replay,
    )
    .is_some();
    let _timing = TacticTiming::new(
        claim_label,
        tactic_index,
        source_index,
        &ProofTactic::Loop(loop_clause.clone()),
        replay.frontier.next_statement_index,
    );
    execute_frontier_local_loop(
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
    if capture_this_tactic {
        return Err(finish_tactic_expansion_capture(
            &replay.simple_proof_builder,
            false,
        ));
    }
    Ok(ProofReplayContext {
        state,
        pure_facts: available_pure_facts,
        replay,
        branch_path,
    })
}

#[allow(clippy::too_many_arguments)]
fn replay_linear_tactics_without_frontier_loops(
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
            && tactic_is_deferred_post_execution(tactic);
        let deferred_region_simp = replay.region_proof && matches!(tactic, ProofTactic::Simp);
        let pre_capture_branch_skeleton =
            begin_tactic_expansion_capture(source_index, tactic, &mut replay);
        let capture_this_tactic = pre_capture_branch_skeleton.is_some();
        if let Some(branch_skeleton) = pre_capture_branch_skeleton
            && deferred_post_execution
        {
            replay.deferred_tactic_capture = Some(DeferredTacticCapture {
                tactic_index,
                source_index,
                post_execution_index: replay.post_execution_tactics.len(),
                branch_skeleton,
            });
        }
        if !deferred_post_execution {
            append_simple_proof_step_for_internal_tactic(
                &mut replay,
                &state,
                &requirement_pure_facts,
                function_block,
                parsed_function.parameters(),
                arguments,
                predicate_environment,
                click_function_environment,
                tactic,
                None,
            );
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
            let pre_state = replay.old_reference_state(&state);
            let source = lower_point_proposition(
                surface_source,
                &requirement_pure_facts,
                parsed_function.parameters(),
                arguments,
                pre_state,
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
                pre_state,
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
            let plan = InternalProofPlan::from_planned_tactics(&[ProofTactic::TransportUsing {
                source: surface_source.clone(),
                target: surface_target.clone(),
                premises,
            }])
            .expect("explicit fact transport is a simple tactic");
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
                &plan,
            )?;
            state = result.state;
            requirement_pure_facts = result.pure_facts;
            replay = result.replay;
            branch_path = result.branch_path;
            assumptions = assumptions_from_propositions(&requirement_pure_facts);
            if capture_this_tactic {
                return Err(finish_tactic_expansion_capture(
                    &replay.simple_proof_builder,
                    false,
                ));
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
            let premises = plan_explicit_theorem_application(
                theorem_environment,
                application,
                claim_label,
                tactic_index,
                &requirement_pure_facts,
                parsed_function.parameters(),
                arguments,
                &replay,
                &state,
                predicate_environment,
                click_function_environment,
            )?;
            let plan = InternalProofPlan::from_planned_tactics(&[ProofTactic::ApplyTheoremUsing {
                application: application.clone(),
                premises,
            }])
            .expect("explicit theorem application is a simple tactic");
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
                &plan,
            )?;
            state = result.state;
            requirement_pure_facts = result.pure_facts;
            replay = result.replay;
            branch_path = result.branch_path;
            assumptions = assumptions_from_propositions(&requirement_pure_facts);
            if capture_this_tactic {
                return Err(finish_tactic_expansion_capture(
                    &replay.simple_proof_builder,
                    false,
                ));
            }
            continue;
        }
        match tactic {
            ProofTactic::Mark(name) => {
                let point = ProgramPointRef {
                    region: CodeRegionRef::Mark(name.clone()),
                    kind: ProgramPointKind::Entry,
                };
                if replay.program_point_states.contains_key(&point) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: duplicate proof mark `{name}`"
                    )));
                }
                replay.program_point_states.insert(point, state.clone());
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
                    continue;
                }
                if replay.is_at_function_entry() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `transport` requires at least one completed execution step"
                    )));
                }
                let pre_state = replay.old_reference_state(&state).clone();
                let surface_premises = match tactic {
                    ProofTactic::TransportUsing { premises, .. } => Some(premises),
                    ProofTactic::Transport { .. } => None,
                    _ => unreachable!(),
                };
                let mut explicit_premises = Vec::new();
                if let Some(surface_premises) = surface_premises {
                    for surface_premise in surface_premises {
                        let premise = if let Some(recorded) = replay
                            .surface_propositions
                            .available_kernel(surface_premise, &requirement_pure_facts)
                        {
                            recorded.clone()
                        } else {
                            lower_point_proposition(
                                surface_premise,
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
                                    "`{claim_label}` tactic {tactic_index}: could not lower `transport using` premise: {message}"
                                ))
                            })?
                        };
                        if !exact_fact_is_available(&premise, &requirement_pure_facts) {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `transport using` requires an exact premise: {}",
                                describe_missing_pure_fact(
                                    &premise,
                                    &requirement_pure_facts,
                                    state.resources().facts(),
                                    parsed_function.parameters(),
                                    arguments,
                                    &replay.effect_facts,
                                )
                            )));
                        }
                        if !explicit_premises.contains(&premise) {
                            explicit_premises.push(premise);
                        }
                    }
                }
                // Lowering memory expressions uses the already-validated
                // ambient resource/loadability context. The proof search
                // below is still restricted to explicit premises plus
                // certified frame context.
                let lowering_facts = requirement_pure_facts.as_slice();
                let mut direct_lowering_facts =
                    facts_for_direct_surface_lowering(&requirement_pure_facts);
                for premise in &explicit_premises {
                    if !direct_lowering_facts.contains(premise) {
                        direct_lowering_facts.push(premise.clone());
                    }
                }
                let source = if let Some(recorded) = replay
                    .surface_propositions
                    .available_kernel(surface_source, &requirement_pure_facts)
                {
                    recorded.clone()
                } else {
                    lower_point_proposition(
                        surface_source,
                        lowering_facts,
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
                    })?
                };
                replay
                    .surface_propositions
                    .record_lowering(surface_source, &source)?;
                let selected_assumptions = if surface_premises.is_some() {
                    let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
                    let resource_facts = state
                        .resources()
                        .observable_facts_assuming_valid(&explicit_assumptions);
                    requirement_pure_facts
                        .iter()
                        .filter(|fact| is_implicit_fact_transport_context(fact))
                        .cloned()
                        .chain(resource_facts)
                        .fold(explicit_assumptions, |assumptions, fact| {
                            assumptions.assume_proposition(fact)
                        })
                } else {
                    assumptions.clone()
                };
                // A transport source spelled at a later program point than
                // its listed fact is the same fact when the kernel proves the
                // snapshots agree at the loaded pointers. Candidates still
                // come only from the explicit premises, so the transport must
                // still list the fact; the recorded effects and the selected
                // assumptions only supply the frame evidence.
                if !exact_fact_is_available(&source, &explicit_premises)
                    && !snapshot_bridged_fact_is_available_under(
                        &source,
                        &explicit_premises,
                        &selected_assumptions,
                        &replay.effect_facts,
                    )
                    && selected_assumptions
                        .derive_atomic_proposition(&source)
                        .is_none()
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `transport{}` requires a source derivable from its {}facts: {}",
                        if surface_premises.is_some() {
                            " using"
                        } else {
                            ""
                        },
                        if surface_premises.is_some() {
                            "explicit "
                        } else {
                            "ambient "
                        },
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
                    &direct_lowering_facts,
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
                replay
                    .surface_propositions
                    .record_lowering(surface_target, &target)?;
                // The target can already be present under a different snapshot
                // spelling; candidates come from the ambient facts, so the
                // bridge only re-spells a fact that is genuinely available.
                if exact_fact_is_available_across_effects(
                    &target,
                    &requirement_pure_facts,
                    &replay.effect_facts,
                ) || materialization_equivalent_available_fact(&target, &requirement_pure_facts)
                    .is_some()
                {
                    if !requirement_pure_facts.contains(&target) {
                        requirement_pure_facts.push(target.clone());
                        assumptions = assumptions.assume_proposition(target);
                    }
                    continue;
                }
                let transition_facts =
                    fact_transport_transition_facts(&replay.effect_facts, &source);
                if surface_premises.is_none() {
                    match plan_explicit_fact_transport(
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
                    ) {
                        Ok(premises) => {
                            replay.simple_proof_builder.push_step(
                                SimpleProofStep::TransportUsing {
                                    source: surface_source.clone(),
                                    target: surface_target.clone(),
                                    premises,
                                },
                            );
                        }
                        Err(error) => {
                            replay
                                .simple_proof_builder
                                .block(fact_transport_planning_failure(
                                    surface_source,
                                    surface_target,
                                    &replay.unfolded_predicates,
                                    &error,
                                ))
                        }
                    }
                }
                let transport_assumptions = transition_facts
                    .iter()
                    .fold(selected_assumptions, |assumptions, fact| {
                        assumptions.assume_proposition(fact.proposition().clone())
                    })
                    .assume_proposition(source.clone());
                if !certified_fact_transport_reaches_through(
                    &source,
                    &target,
                    state.memory(),
                    &transport_assumptions,
                    &transition_facts,
                ) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: no certified frame transport applies to the exact source fact\n  source: {source:?}\n  current memory: {:?}\n  effect facts: {:?}",
                        state.memory(),
                        replay.effect_facts
                    )));
                }
                if !requirement_pure_facts.contains(&target) {
                    requirement_pure_facts.push(target.clone());
                    assumptions = assumptions.assume_proposition(target);
                }
            }
            ProofTactic::StepUsing(premises) => {
                let all_pure_facts = requirement_pure_facts.clone();
                let tactic_name = "step() using";
                let prerequisite_policy = StatementPrerequisitePolicy::Explicit;
                let loop_step_policy = LoopStepPolicy::EnterBody;
                let pre_state = replay.old_reference_state(&state).clone();
                let mut explicit_premises = Vec::new();
                for surface_premise in premises {
                    let recorded = replay
                        .surface_propositions
                        .available_kernel(surface_premise, &all_pure_facts);
                    let recorded_is_constant_truth =
                        recorded.is_some_and(|premise| match premise {
                            Proposition::ConditionIs(ConditionTerm::Constant(true), true) => true,
                            Proposition::ConditionIs(
                                ConditionTerm::Bitvector32SignedLessThan(left, right)
                                | ConditionTerm::Bitvector32SignedLessEqual(left, right)
                                | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
                                | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
                                | ConditionTerm::Bitvector32Equal(left, right),
                                true,
                            ) => matches!(
                                (left.as_ref(), right.as_ref()),
                                (Bitvector32Term::Constant(_), Bitvector32Term::Constant(_))
                            ),
                            _ => false,
                        });
                    let lower_at_current = || {
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
                    };
                    let current_indexed = proposition_contains_at_expression(surface_premise)
                        .then(|| lower_at_current().ok())
                        .flatten()
                        .filter(|current| {
                            exact_fact_is_available_across_effects(
                                current,
                                &all_pure_facts,
                                &replay.effect_facts,
                            ) || materialization_equivalent_available_fact(current, &all_pure_facts)
                                .is_some()
                        });
                    // Prefer an explicit program-point lowering when it names
                    // an exact available fact. Fall back to the checked cache
                    // when a partial expansion has not replayed that point, or
                    // when the cache records an equivalent polarity spelling
                    // such as `not (a < b)` versus `a >= b`.
                    let premise = if let Some(current) = current_indexed {
                        current
                    } else if recorded_is_constant_truth {
                        match lower_at_current() {
                            Ok(current)
                                if !Assumptions::new().proves(&current)
                                    && (exact_fact_is_available_across_effects(
                                        &current,
                                        &all_pure_facts,
                                        &replay.effect_facts,
                                    ) || materialization_equivalent_available_fact(
                                        &current,
                                        &all_pure_facts,
                                    )
                                    .is_some()) =>
                            {
                                current
                            }
                            _ => recorded.expect("checked recorded truth").clone(),
                        }
                    } else if (proposition_contains_at_expression(surface_premise)
                        || proposition_contains_old_expression(surface_premise))
                        && let Some(recorded) = recorded
                    {
                        recorded.clone()
                    } else {
                        lower_at_current().map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: could not lower `{tactic_name}` premise `{}`: {message}",
                                super::printing::source_click_proposition(surface_premise)
                            ))
                        })?
                    };
                    replay
                        .surface_propositions
                        .record_lowering(surface_premise, &premise)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: could not record `{tactic_name}` premise: {}",
                                error.message()
                            ))
                        })?;
                    let entry_point = ProgramPointRef {
                        region: CodeRegionRef::Statement(replay.frontier.next_statement_index),
                        kind: ProgramPointKind::Entry,
                    };
                    let source_surface = surface_with_source_site(surface_premise, &entry_point)?;
                    replay
                        .surface_propositions
                        .record_lowering(&source_surface, &premise)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: could not record `{tactic_name}` premise source site: {}",
                                error.message()
                            ))
                        })?;
                    // Loadability premises additionally transport across
                    // snapshot spellings and recorded effects: the recorded
                    // fact and the premise print identically but embed
                    // different memory snapshots.
                    let premise_is_available =
                        exact_fact_is_available_across_effects(
                            &premise,
                            &all_pure_facts,
                            &replay.effect_facts,
                        ) || materialization_equivalent_available_fact(&premise, &all_pure_facts)
                            .is_some()
                            || crate::kernel::loadable_covered_by_fact(&assumptions, &premise);
                    if !premise_is_available {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires an exact premise: {}",
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
                    if !explicit_premises.contains(&premise) {
                        explicit_premises.push(premise);
                    }
                }
                for case in &replay.case_assumptions {
                    let branch_fact = if let Some(fact) = &case.fact {
                        fact.clone()
                    } else {
                        let proposition = lower_point_proposition(
                            &case.condition,
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
                    if exact_fact_is_available(&branch_fact, &all_pure_facts)
                        && !explicit_premises.contains(&branch_fact)
                    {
                        explicit_premises.push(branch_fact);
                    }
                }
                let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
                for resource_fact in state
                    .resources()
                    .observable_facts_assuming_valid(&explicit_assumptions)
                {
                    if !explicit_premises.contains(&resource_fact) {
                        explicit_premises.push(resource_fact);
                    }
                }
                let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
                execute_step_from_execution_point(
                    &mut replay,
                    &mut state,
                    &mut explicit_premises,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    &explicit_assumptions,
                    function_environment,
                    claim_label,
                    tactic_index,
                    tactic_name,
                    &[],
                    None,
                    prerequisite_policy,
                    // `using` deliberately selects the exact context that may
                    // cross this statement boundary. Transport only those
                    // listed facts through the certified statement effect;
                    // ambient facts are restored below at their original
                    // snapshots.
                    StatementFactTransportPolicy::Selected,
                    loop_step_policy,
                )?;
                for fact in all_pure_facts {
                    if !explicit_premises.contains(&fact) {
                        explicit_premises.push(fact);
                    }
                }
                requirement_pure_facts = explicit_premises;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::Step
            | ProofTactic::CertifiedStatementStep { .. }
            | ProofTactic::CertifiedLoopSummaryStep { .. } => {
                let (prerequisite_policy, certified_prerequisites, loop_step_policy) = match tactic
                {
                    ProofTactic::Step => (
                        StatementPrerequisitePolicy::Exact,
                        &[][..],
                        LoopStepPolicy::EnterBody,
                    ),
                    ProofTactic::CertifiedStatementStep {
                        prerequisite_derivations,
                        ..
                    } => (
                        StatementPrerequisitePolicy::Certified,
                        prerequisite_derivations.as_slice(),
                        LoopStepPolicy::EnterBody,
                    ),
                    ProofTactic::CertifiedLoopSummaryStep {
                        prerequisite_derivations,
                        ..
                    } => (
                        StatementPrerequisitePolicy::Certified,
                        prerequisite_derivations.as_slice(),
                        LoopStepPolicy::ApplyVerifiedRule,
                    ),
                    _ => unreachable!(),
                };
                let planned_transition = match tactic {
                    ProofTactic::CertifiedStatementStep {
                        planned_transition: Some(index),
                        ..
                    }
                    | ProofTactic::CertifiedLoopSummaryStep {
                        planned_transition: Some(index),
                        ..
                    } => replay.planned_statement_transitions.get(*index).cloned(),
                    _ => None,
                };
                execute_step_from_execution_point(
                    &mut replay,
                    &mut state,
                    &mut requirement_pure_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    &assumptions,
                    function_environment,
                    claim_label,
                    tactic_index,
                    tactic_name(tactic),
                    certified_prerequisites,
                    planned_transition.as_ref(),
                    prerequisite_policy,
                    StatementFactTransportPolicy::None,
                    loop_step_policy,
                )?;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::CertifiedPathAssumption { facts, theorem, .. } => {
                if !matches!(
                    implication_body(theorem.proposition()),
                    Proposition::CConditionEvaluates { .. }
                ) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: certified path assumption is not backed by a condition-evaluation theorem"
                    )));
                }
                for fact in facts {
                    if !requirement_pure_facts.contains(fact) {
                        requirement_pure_facts.push(fact.clone());
                    }
                }
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::CertifiedAlternatives(alternatives) => {
                let outer_simple_proof = replay.simple_proof_builder.clone();
                let base = ProofReplayContext {
                    state: state.clone(),
                    pure_facts: requirement_pure_facts.clone(),
                    replay: replay.clone(),
                    branch_path: branch_path.clone(),
                };
                let mut completed = Vec::new();
                let mut surface_paths = Vec::new();
                for alternative in alternatives {
                    let mut alternative_base = base.clone();
                    alternative_base.replay.simple_proof_builder = SimpleProofBuilder::default();
                    let result = replay_internal_plan(
                        alternative_base,
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
                        alternative,
                    )?;
                    surface_paths.push(result.replay.simple_proof_builder.clone());
                    completed.push(BoundedProofFrontier {
                        replay: result.replay,
                        state: result.state,
                        pure_facts: result.pure_facts,
                    });
                }
                merge_bounded_execution_frontiers(
                    &mut replay,
                    &mut state,
                    &mut requirement_pure_facts,
                    function,
                    arguments,
                    completed,
                    claim_label,
                    tactic_index,
                )?;
                replay.simple_proof_builder = outer_simple_proof;
                match synthesize_surface_alternatives(surface_paths) {
                    Ok(steps) => {
                        for step in steps {
                            replay.simple_proof_builder.push_step(step);
                        }
                    }
                    Err(message) => replay.simple_proof_builder.block(format!(
                        "could not lower certified branch alternatives: {message}"
                    )),
                }
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::SmartStep => {
                let mut planning_replay = replay.clone();
                planning_replay.planned_tactics.clear();
                planning_replay.planned_statement_transitions.clear();
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
                    &[],
                    None,
                    StatementPrerequisitePolicy::Planning,
                    StatementFactTransportPolicy::Automatic,
                    LoopStepPolicy::EnterBody,
                )?;
                let certificate =
                    InternalProofPlan::from_planned_tactics(&planning_replay.planned_tactics)
                        .map(|plan| {
                            plan.with_statement_transitions(
                                planning_replay.planned_statement_transitions.clone(),
                            )
                        })
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `step` planned a non-certificate tactic {:?}",
                                error.smart_tactic()
                            ))
                        })?;
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
                    &certificate,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths => {
                let mut planning_replay = replay.clone();
                planning_replay.planned_tactics.clear();
                planning_replay.planned_statement_transitions.clear();
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
                    )
                });
                if direct_result.is_none_or(|result| result.is_err()) {
                    planning_replay = replay.clone();
                    planning_replay.planned_tactics.clear();
                    planning_replay.planned_statement_transitions.clear();
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
                    )?;
                }
                let certificate =
                    InternalProofPlan::from_planned_tactics(&planning_replay.planned_tactics)
                        .map(|plan| {
                            plan.with_statement_transitions(
                                planning_replay.planned_statement_transitions.clone(),
                            )
                        })
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `execute` planned a non-certificate tactic {:?}",
                                error.smart_tactic()
                            ))
                        })?;
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
                    &certificate,
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
                planning_replay.planned_tactics.clear();
                planning_replay.planned_statement_transitions.clear();
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
                )?;
                let certificate =
                    InternalProofPlan::from_planned_tactics(&planning_replay.planned_tactics)
                        .map(|plan| {
                            plan.with_statement_transitions(
                                planning_replay.planned_statement_transitions.clone(),
                            )
                        })
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `execute_until` planned a non-certificate tactic {:?}",
                                error.smart_tactic()
                            ))
                        })?;
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
                    &certificate,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::SmartFrame(region_ref) => {
                if region_ref.is_some() {
                    let certificate =
                        InternalProofPlan::from_planned_tactics(&[ProofTactic::FrameUsing {
                            region: region_ref.clone(),
                            premises: Vec::new(),
                        }])
                        .expect("exact frame is a simple tactic");
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
                        &certificate,
                    )?;
                    state = result.state;
                    requirement_pure_facts = result.pure_facts;
                    replay = result.replay;
                    branch_path = result.branch_path;
                    assumptions = assumptions_from_propositions(&requirement_pure_facts);
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
                let certificate =
                    InternalProofPlan::from_planned_tactics(&[ProofTactic::CertifiedFrame(
                        path_derivations,
                    )])
                    .expect("certified frame is a simple tactic");
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
                    &certificate,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::FrameUsing {
                region: region_ref,
                premises: surface_premises,
            } => {
                let mut frame_facts = Vec::new();
                if !surface_premises.is_empty() {
                    let all_pure_facts = requirement_pure_facts.clone();
                    let pre_state = replay.old_reference_state(&state).clone();
                    for surface_premise in surface_premises {
                        let premise = if let Some(recorded) = replay
                            .surface_propositions
                            .available_kernel(surface_premise, &all_pure_facts)
                        {
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
                        if !(exact_fact_is_available_across_effects(
                            &premise,
                            &all_pure_facts,
                            &replay.effect_facts,
                        ) || replay.ordered_finalization && replay.is_at_function_exit())
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
                    continue;
                }
                require_function_exit(&replay, claim_label, tactic_index, "frame")?;
                let code_region = region_ref
                    .as_ref()
                    .map(|region_ref| {
                        resolve_code_region_ref(
                            function_block,
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
                            function_block,
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
                        function_block,
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
                            facts: frame_facts,
                        }
                    };
                    replay.defer_post_execution(tactic_index, source_index, deferred);
                    replay.frames.insert(region_ref.clone());
                    continue;
                }
                let effect_claims = claims
                    .iter()
                    .filter(|claim| matches!(claim, FunctionClaimRef::Effect(_, _)))
                    .collect::<Vec<_>>();
                if effect_claims.is_empty() {
                    validate_frame_code_region(
                        function_block,
                        parsed_function,
                        code_region,
                        &claims[0],
                        claim_label,
                        tactic_index,
                    )?;
                }
                for claim in effect_claims {
                    validate_frame_code_region(
                        function_block,
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
                replay.frames.insert(region_ref.clone());
            }
            ProofTactic::CertifiedFrame(path_derivations) => {
                require_function_exit(&replay, claim_label, tactic_index, "certified_frame")?;
                replay.defer_post_execution(
                    tactic_index,
                    source_index,
                    PostExecutionTactic::CertifiedFrame(path_derivations.clone()),
                );
            }
            ProofTactic::UnfoldPredicate(name) => {
                if predicate_environment.get(name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unknown predicate `{name}`"
                    )));
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::UnfoldPredicate(name.clone()),
                    );
                    continue;
                }
                if !replay.unfolded_predicates.contains(name) {
                    replay.unfolded_predicates.push(name.clone());
                }
                let surface_unfoldings = requirement_pure_facts
                    .iter()
                    .filter_map(|kernel| {
                        let Proposition::Predicate {
                            name: kernel_name, ..
                        } = kernel
                        else {
                            return None;
                        };
                        if kernel_name != name {
                            return None;
                        }
                        let ClickProposition::PredicateCall {
                            name: surface_name,
                            arguments: surface_arguments,
                        } = replay.surface_propositions.surface(kernel).ok()?
                        else {
                            return None;
                        };
                        let definition = predicate_environment.get(surface_name)?;
                        let surface =
                            instantiate_click_predicate_definition(definition, surface_arguments)
                                .ok()?;
                        let unfolded = unfold_predicates_in_proposition(
                            predicate_environment,
                            click_function_environment,
                            std::slice::from_ref(name),
                            kernel,
                            &assumptions,
                        )
                        .ok()?;
                        Some((surface, unfolded))
                    })
                    .collect::<Vec<_>>();
                requirement_pure_facts = unfold_available_predicate_facts(
                    predicate_environment,
                    click_function_environment,
                    std::slice::from_ref(name),
                    &requirement_pure_facts,
                )
                .map_err(|message| {
                    ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
                })?;
                for (surface, kernel) in surface_unfoldings {
                    replay
                        .surface_propositions
                        .record_lowering(&surface, &kernel)?;
                }
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ApplyTheorem(application) => {
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
                            PostExecutionTactic::Apply(application.clone()),
                        );
                    } else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: post-execution `apply` is not available in this region proof"
                        )));
                    }
                } else {
                    match plan_explicit_theorem_application(
                        theorem_environment,
                        application,
                        claim_label,
                        tactic_index,
                        &requirement_pure_facts,
                        parsed_function.parameters(),
                        arguments,
                        &replay,
                        &state,
                        predicate_environment,
                        click_function_environment,
                    ) {
                        Ok(premises) => {
                            replay.simple_proof_builder.push_step(
                                SimpleProofStep::ApplyTheoremUsing {
                                    application: application.clone(),
                                    premises,
                                },
                            );
                        }
                        Err(error) => replay.simple_proof_builder.block(format!(
                            "could not make theorem application premises explicit: {}",
                            error.message()
                        )),
                    }
                    requirement_pure_facts = apply_theorem_at_current_point(
                        theorem_environment,
                        application,
                        claim_label,
                        tactic_index,
                        requirement_pure_facts,
                        parsed_function.parameters(),
                        arguments,
                        replay.old_reference_state(&state),
                        &state,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
                        &replay.unfolded_predicates,
                        None,
                    )?;
                    assumptions = assumptions_from_propositions(&requirement_pure_facts);
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
                        continue;
                    }
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: post-execution `apply using` is not available in this region proof"
                    )));
                }
                let all_pure_facts = requirement_pure_facts.clone();
                let mut lowering_facts = all_pure_facts.clone();
                append_resource_context_observable_facts(state.resources(), &mut lowering_facts);
                let pre_state = replay.old_reference_state(&state).clone();
                let mut explicit_premises = Vec::new();
                for surface_premise in premises {
                    let premise = if let Some(recorded) = replay
                        .surface_propositions
                        .available_kernel(surface_premise, &all_pure_facts)
                    {
                        recorded.clone()
                    } else {
                        lower_point_proposition(
                            surface_premise,
                            &lowering_facts,
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
                                "`{claim_label}` tactic {tactic_index}: could not lower `apply using` premise: {message}"
                            ))
                        })?
                    };
                    if !exact_fact_is_available(&premise, &all_pure_facts)
                        && materialization_equivalent_available_fact(&premise, &all_pure_facts)
                            .is_none()
                    {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `apply using` requires an exact premise: {}",
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
                    if !explicit_premises.contains(&premise) {
                        explicit_premises.push(premise);
                    }
                }
                let mut applied = apply_theorem_at_current_point(
                    theorem_environment,
                    application,
                    claim_label,
                    tactic_index,
                    explicit_premises,
                    parsed_function.parameters(),
                    arguments,
                    &pre_state,
                    &state,
                    &replay.program_point_states,
                    predicate_environment,
                    click_function_environment,
                    &replay.unfolded_predicates,
                    Some(&lowering_facts),
                )?;
                for fact in all_pure_facts {
                    if !applied.contains(&fact) {
                        applied.push(fact);
                    }
                }
                requirement_pure_facts = applied;
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
                    continue;
                }
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
                let smart_unfolds = smart_simp_unfold_prefix(&have.proof);
                let smart_plan = if let Some(unfolded_predicates) = &smart_unfolds {
                    let (fact, plan) = plan_smart_have_at_current_point(
                        have,
                        claim_label,
                        tactic_index,
                        &have_facts,
                        parsed_function.parameters(),
                        arguments,
                        replay.old_reference_state(&state),
                        &state,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
                        unfolded_predicates,
                        None,
                    )?;
                    Some((fact, plan))
                } else {
                    None
                };
                let fact = match &smart_plan {
                    Some((fact, _)) => fact.clone(),
                    None => prove_have_at_current_point(
                        have,
                        theorem_environment,
                        claim_label,
                        tactic_index,
                        &have_facts,
                        parsed_function.parameters(),
                        arguments,
                        replay.old_reference_state(&state),
                        &state,
                        &replay.program_point_states,
                        &replay.surface_propositions,
                        predicate_environment,
                        click_function_environment,
                        function_block.requires(),
                    )?,
                };
                let surface_certificate = if let Some((_, plan)) = &smart_plan {
                    Some(surface_smart_have_certificate(
                        &mut replay,
                        &state,
                        &have_facts,
                        parsed_function.parameters(),
                        arguments,
                        predicate_environment,
                        click_function_environment,
                        have,
                        plan,
                        smart_unfolds.as_deref().unwrap_or(&[]),
                    )?)
                } else {
                    surface_smart_apply_have_certificate(
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
                    )?
                };
                if let Some(mut certificate) = surface_certificate {
                    let replay_certificate = |certificate: &SimpleProof| {
                        replay_simple_proof(
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
                    let initial_replay = pure_goal_simple_proof_gateway(
                        claim_label,
                        || Ok(certificate.clone()),
                        replay_certificate,
                    );
                    if let Err(initial_error) = initial_replay {
                        let fallback = smart_plan.as_ref().and_then(|_| {
                            surface_smart_have_derivation_certificate(
                                &replay,
                                &state,
                                &have_facts,
                                parsed_function.parameters(),
                                arguments,
                                predicate_environment,
                                click_function_environment,
                                have,
                            )
                        });
                        let Some(fallback) = fallback else {
                            return Err(initial_error);
                        };
                        pure_goal_simple_proof_gateway(
                            claim_label,
                            || Ok(fallback.clone()),
                            replay_certificate,
                        )?;
                        certificate = fallback;
                    }
                    replay
                        .simple_proof_builder
                        .steps
                        .extend(certificate.steps().iter().cloned());
                }
                // Do not teach certificate replay the search-time lowering of
                // this goal until the generated surface certificate has
                // independently replayed. Otherwise a richer planner
                // materialization can make a nontrivial snapshot equality
                // appear reflexive and circularly validate `normalize()`.
                replay
                    .surface_propositions
                    .record_lowering(&have.proposition, &fact)?;
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
            | ProofTactic::Split
            | ProofTactic::Left
            | ProofTactic::Right
            | ProofTactic::Contradiction(_)
            | ProofTactic::Derive(_)
            | ProofTactic::SimpUsing(_) => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{}` is only available while proving a pure goal, such as inside `have ... by`",
                    tactic_name(tactic)
                )));
            }
            ProofTactic::ExactPropositionDerivation(derivation) => {
                if !derivation.replay(&assumptions) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: proposition derivation did not replay"
                    )));
                }
                if !requirement_pure_facts.contains(derivation.conclusion()) {
                    requirement_pure_facts.push(derivation.conclusion().clone());
                    assumptions = assumptions_from_propositions(&requirement_pure_facts);
                }
            }
            ProofTactic::CertifiedFactTransport {
                source,
                target,
                theorem,
            } => {
                let Some(available_source) =
                    materialization_equivalent_available_fact(source, &requirement_pure_facts)
                else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: certified fact transport is missing exact source {source:?}"
                    )));
                };
                if available_source != *source && !requirement_pure_facts.contains(source) {
                    requirement_pure_facts.retain(|fact| fact != &available_source);
                    requirement_pure_facts.push(source.clone());
                }
                let Proposition::Implies(theorem_source, theorem_target) = theorem.proposition()
                else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: certified fact transport theorem is not an implication"
                    )));
                };
                if theorem_source.as_ref() != source || theorem_target.as_ref() != target {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: certified fact transport theorem does not match its source and target"
                    )));
                }
                if !requirement_pure_facts.contains(target) {
                    requirement_pure_facts.push(target.clone());
                }
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::FinishCertifiedFactTransports(sources) => {
                requirement_pure_facts.retain(|fact| !sources.contains(fact));
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::CloseInvariants => {
                if !replay.loop_invariant_region {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `close_invariants` is only available in a loop-region proof"
                    )));
                }
                if replay.region_invariants_closed {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: the invariant bundle was closed more than once on one path"
                    )));
                }
                replay.region_invariants_closed = true;
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
        if capture_this_tactic && !deferred_post_execution && !deferred_region_simp {
            return Err(finish_tactic_expansion_capture(
                &replay.simple_proof_builder,
                false,
            ));
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
