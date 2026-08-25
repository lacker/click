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

/// The one mid-execution `have` law: checked point proof first, generated
/// smart plan second, direct derivation last, with the entry-prerequisite,
/// surface-lowering, and certificate-fact recording every caller shares.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn check_mid_execution_have(
    have: &ProofHave,
    replay: &mut TacticReplayState,
    state: &CState,
    pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    tactic_index: usize,
) -> Result<Option<ProofCertificate>, ClickError> {
    let _have_span =
        crate::instrumentation::OperationTiming::new("have", claim_label, "contract have replay");
    let mut have_facts = pure_facts.clone();
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
        None,
        &replay,
        &replay.surface_propositions,
        predicate_environment,
        click_function_environment,
        function_block.requires(),
        function_block.requirement_label_indices(),
        None,
    )?;
    let smart_unfolds = smart_simp_unfold_prefix(&have.proof);
    // Search may materialize a Surface-expressible operation
    // plan, but the goal is proved only when those operations
    // advance the checked point Proof below.
    let smart_result = match (&checked_proof_result, &smart_unfolds) {
        (Some(_), _) => None,
        (None, Some(unfolded_predicates)) => Some(construct_smart_have_plan(
            &replay,
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
    let (fact, surface_certificate) = match (checked_proof_result, smart_result) {
        (Some((fact, certificate)), _) => (fact, certificate),
        (None, Some((fact, proof))) => {
            let checked = checked_have_with_proof(
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
                        None,
                        &replay,
                        &replay.surface_propositions,
                        predicate_environment,
                        click_function_environment,
                        function_block.requires(),
                        function_block.requirement_label_indices(),
                        Some((&fact, &proof)),
                    )?
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "`{claim_label}` have proof {tactic_index}: generated smart operations did not produce a checked Proof"
                        ))
                    })?;
            (checked.0, checked.1)
        }
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
            (fact, None)
        }
    };
    let retained_certificate = surface_certificate.clone();
    if let Some(certificate) = surface_certificate {
        for step in certificate.steps() {
            replay.proof_certificate_builder.push_step(step.clone());
        }
    }
    // Carry any kernel-issued standard-theorem authority selected
    // inside the point Proof back to the enclosing entry proof.
    if replay
        .frontier
        .execution_start_state
        .as_ref()
        .is_none_or(|start| start == state)
        && let SourceProof::Script(have_tactics) = &have.proof
    {
        for have_tactic in have_tactics {
            let ProofTactic::ApplyTheoremUsing { application, .. } = have_tactic else {
                continue;
            };
            if let Some(derivation) = kernel_standard_theorem_derivation_at_current_point(
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
            )? {
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
    // Record the search-time lowering only after the selected
    // Surface operations have closed the checked Proof. Recording
    // it earlier could make a nontrivial snapshot equality appear
    // reflexive and circularly validate `normalize()`.
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
        .is_none_or(|start| start == state)
        && let Some(derivation) =
            prove_pure_proposition_from_context(&assumptions_from_propositions(&have_facts), &fact)
    {
        replay
            .function_entry_execution_prerequisites
            .insert(fact.clone());
        replay.function_entry_derivations.insert(derivation);
    }
    if !pure_facts.contains(&fact) {
        pure_facts.push(fact.clone());
    }
    Ok(retained_certificate)
}

pub(in crate::lang::click::proof) fn execute_frontier_local_loop(
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
) -> Result<StructuralClause, ClickError> {
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
    // later surface tactics can still refer to either form.  A verified
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
            next_kernel_variable: replay.next_kernel_variable,
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
        .push_source_tactic(ProofTactic::Loop(expanded_loop.clone()));
    Ok(expanded_loop)
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn replay_linear_tactics<'a>(
    context: ProofReplayContext,
    expansion_capture: Option<&mut ExpansionCapture>,
    function_block: &'a FunctionBlock,
    parsed_function: &'a syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &'a str,
    function_environment: &'a CExecutionEnvironment,
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    resource_environment: &'a ResourceEnvironment,
    theorem_environment: &'a TheoremEnvironment,
    function: &'a CFunction,
    arguments: &'a [CExpression],
    tactics: &[IndexedTactic],
) -> Result<ProofReplayContext, ClickError> {
    // Transitional function-boundary wrap (`issues/replay-smell.md`, phase
    // 1): the node interpreter still hands linear segments over as a replay
    // context. The segment itself runs on one threaded Proof.
    let proof = Proof::for_execution_frontier(
        claim_label,
        tactics.first().map_or(0, |indexed| indexed.index),
        context,
        function_block,
        function,
        parsed_function,
        arguments,
        function_environment,
        resource_environment,
        predicate_environment,
        click_function_environment,
        theorem_environment,
    );
    replay_linear_tactics_on_proof(
        proof,
        expansion_capture,
        function_block,
        parsed_function,
        claims,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        theorem_environment,
        function,
        arguments,
        tactics,
    )?
    .into_execution_context()
}

/// The one linear source driver: applies a linear tactic segment to the
/// threaded Proof. Frontier-local `loop` tactics are single checked
/// operations between the linear chunks they separate.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn replay_linear_tactics_on_proof<'a>(
    mut proof: Proof<'a>,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    function_block: &'a FunctionBlock,
    parsed_function: &'a syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &'a str,
    function_environment: &'a CExecutionEnvironment,
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    theorem_environment: &'a TheoremEnvironment,
    function: &'a CFunction,
    arguments: &'a [CExpression],
    tactics: &[IndexedTactic],
) -> Result<Proof<'a>, ClickError> {
    let mut chunk_start = 0;
    for (index, indexed_tactic) in tactics.iter().enumerate() {
        let ProofTactic::Loop(loop_clause) = &indexed_tactic.tactic else {
            continue;
        };
        proof = replay_linear_tactics_without_frontier_loops(
            proof,
            expansion_capture.as_deref_mut(),
            function_block,
            parsed_function,
            claims,
            claim_label,
            function_environment,
            predicate_environment,
            click_function_environment,
            theorem_environment,
            function,
            arguments,
            &tactics[chunk_start..index],
        )?;
        if crate::instrumentation::deadline_exceeded() {
            return Err(ClickError::new(format!(
                "tactic budget exhausted: {}",
                crate::instrumentation::deadline_context()
            )));
        }
        proof = proof.start_source_tactic()?.apply_frontier_local_loop(
            expansion_capture.as_deref_mut(),
            loop_clause,
            indexed_tactic.index,
            indexed_tactic.source_index,
        )?;
        chunk_start = index + 1;
    }
    replay_linear_tactics_without_frontier_loops(
        proof,
        expansion_capture,
        function_block,
        parsed_function,
        claims,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        theorem_environment,
        function,
        arguments,
        &tactics[chunk_start..],
    )
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
    premise_anchor: Option<&ProgramPointRef>,
    replay: &TacticReplayState,
    surface_propositions: &SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    original_requirements: &[Requirement],
    requirement_label_indices: &BTreeMap<String, usize>,
    generated_plan: Option<(&Proposition, &SourceProof)>,
) -> Result<Option<(Proposition, Option<ProofCertificate>)>, ClickError> {
    enum Plan<'a> {
        DirectSmart,
        Script(&'a [ProofTactic]),
        GeneratedScript(&'a [ProofTactic]),
    }

    let (goal, plan) = match generated_plan {
        Some((goal, SourceProof::Script(tactics))) => {
            (goal.clone(), Plan::GeneratedScript(tactics))
        }
        Some((_, _)) => {
            return Err(ClickError::new(format!(
                "`{claim_label}` have proof {tactic_index}: generated smart proof was not an explicit script"
            )));
        }
        None => {
            let plan = match &have.proof {
                SourceProof::Default
                | SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => Plan::DirectSmart,
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
            (goal, plan)
        }
    };
    let proof = Proof::for_point_surface_goal_with_requirements(
        claim_label,
        tactic_index,
        available,
        goal.clone(),
        have.proposition.clone(),
        parameters,
        arguments,
        pre_state,
        state,
        result,
        premise_anchor,
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
    let proof = match plan {
        Plan::Script(tactics) => {
            let Some(checked) = proof.try_linear_script(tactics)? else {
                return Ok(None);
            };
            checked
        }
        Plan::DirectSmart => {
            let Some(closed) = proof.try_simp_closure()? else {
                return Ok(None);
            };
            closed
        }
        Plan::GeneratedScript(tactics) => {
            let Some(checked) = proof.try_planned_linear_script(tactics)? else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` have proof {tactic_index}: generated smart operations did not close the checked Proof"
                )));
            };
            checked
        }
    };
    if !proof.is_complete() {
        return Err(ClickError::new(format!(
            "`{claim_label}` have proof {tactic_index}: checked proof retained an open goal"
        )));
    }
    let body = proof.certificate();
    let certificate = ProofCertificate::from_steps(vec![SimpleProofStep::Have {
        proposition: have.proposition.clone(),
        proof: Box::new(body),
    }]);
    Ok(Some((goal, Some(certificate))))
}

/// Schedules one ordered outcome operation on the threaded interpreter
/// Proof. This is cursor metadata only: finalization applies the operation
/// to each typed outcome goal. A tactic that contributes nothing further to
/// its surface scope closes it here as well, skipping the interpreter's
/// ordinary epilogue.
fn defer_post_execution_on_proof<'a>(
    proof: Proof<'a>,
    tactic_index: usize,
    source_index: usize,
    tactic: PostExecutionTactic,
    close_scope: Option<TacticSurfaceScope>,
) -> Result<Proof<'a>, ClickError> {
    let (proof, ()) = proof.edit_replay_cursor(|replay, _, _| {
        replay.defer_post_execution(tactic_index, source_index, tactic);
        if let Some(scope) = close_scope {
            end_tactic_surface_scope(replay, scope);
        }
    })?;
    Ok(proof)
}

#[allow(clippy::too_many_arguments)]
fn replay_linear_tactics_without_frontier_loops<'a>(
    mut proof: Proof<'a>,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    function_block: &'a FunctionBlock,
    parsed_function: &'a syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &'a str,
    function_environment: &'a CExecutionEnvironment,
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    theorem_environment: &'a TheoremEnvironment,
    function: &'a CFunction,
    arguments: &'a [CExpression],
    tactics: &[IndexedTactic],
) -> Result<Proof<'a>, ClickError> {
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
        let (
            deferred_post_execution,
            proof_owned_smart_frame_deferred,
            deferred_region_simp,
            frontier_region,
            at_function_exit,
            at_function_entry,
            statement_index,
        ) = {
            let replay = proof.replay_cursor()?;
            (
                replay.frontier.region == ExecutionRegionKind::Function
                    && replay.is_at_function_exit()
                    && replay.open_scopes == 0
                    && tactic_is_deferred_post_execution(tactic),
                replay.frontier.region == ExecutionRegionKind::Function
                    && replay.is_at_function_exit()
                    && replay.open_scopes == 0
                    && matches!(
                        tactic,
                        ProofTactic::SmartFrame(None | Some(CodeRegionRef::Function))
                    ),
                replay.frontier.region == ExecutionRegionKind::LoopBody
                    && matches!(tactic, ProofTactic::Simp),
                replay.frontier.region,
                replay.is_at_function_exit(),
                replay.is_at_function_entry(),
                replay.frontier.next_statement_index,
            )
        };
        let (prepared, (scope, capture_this_tactic)) =
            proof.begin_source_tactic(tactic_index, |replay, state, facts| {
                let scope = begin_tactic_surface_scope(replay);
                let capture_this_tactic = begin_tactic_expansion_capture(
                    expansion_capture.as_deref_mut(),
                    source_index,
                    replay,
                );
                if capture_this_tactic
                    && (deferred_post_execution || proof_owned_smart_frame_deferred)
                {
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
                            ProofCertificateConstructionContext::new(replay, &mut construction);
                        append_simple_proof_step_for_operation(
                            &mut construction_context,
                            state,
                            &facts.to_vec(),
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
                (scope, capture_this_tactic)
            })?;
        proof = prepared;
        let mut scope = Some(scope);
        let _timing = (!(deferred_post_execution || deferred_region_simp)
            && has_independent_source_timing(tactic))
        .then(|| {
            TacticTiming::new(
                claim_label,
                tactic_index,
                source_index,
                tactic,
                statement_index,
            )
        })
        .flatten();
        if let ProofTactic::Transport {
            source: surface_source,
            target: surface_target,
        } = tactic
            && !at_function_exit
        {
            if at_function_entry || at_function_exit {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a current statement frontier after at least one execution step"
                )));
            }
            // Premise planning reads the frontier; the checked transition is
            // the explicit `transport using` law on the threaded Proof, which
            // records the checker-owned lowerings itself.
            let premises = {
                let view = proof.finalization_view()?;
                let (state, replay, facts) = (view.state, view.replay, &view.facts);
                let assumptions = assumptions_from_propositions(facts);
                let pre_state = replay.old_reference_state(state);
                let source = lower_point_proposition(
                    surface_source,
                    facts,
                    parsed_function.parameters(),
                    arguments,
                    pre_state,
                    state,
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
                            facts,
                            state.resources().facts(),
                            parsed_function.parameters(),
                            arguments,
                            &replay.effect_facts,
                        )
                    )));
                }
                let target = lower_point_proposition(
                    surface_target,
                    facts,
                    parsed_function.parameters(),
                    arguments,
                    pre_state,
                    state,
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
                let transition_facts =
                    fact_transport_transition_facts(&replay.effect_facts, &source);
                plan_explicit_fact_transport(
                    surface_source,
                    &source,
                    &target,
                    facts,
                    &transition_facts,
                    parsed_function.parameters(),
                    arguments,
                    replay,
                    state,
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
                })?
            };
            let checkpoint = proof.checkpoint();
            let transported = proof.apply_step(SimpleProofStep::TransportUsing {
                source: surface_source.clone(),
                target: surface_target.clone(),
                premises,
            })?;
            let certificate = transported.certificate_since(&checkpoint)?;
            let (next, slice) = transported
                .record_surface_steps(certificate.steps())?
                .edit_replay_cursor(|replay, _, _| {
                    end_tactic_surface_scope(replay, scope.take().expect("tactic scope is open"))
                })?;
            proof = next;
            if capture_this_tactic {
                finish_tactic_expansion_capture(expansion_capture.as_deref_mut(), &slice, false);
            }
            continue;
        }
        if let ProofTactic::ApplyTheorem(application) = tactic
            && !at_function_exit
        {
            if theorem_environment.get(&application.name).is_none() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: unknown theorem `{}`",
                    application.name
                )));
            }
            let checkpoint = proof.checkpoint();
            let applied = proof.apply_theorem_application(application)?;
            let certificate = applied.certificate_since(&checkpoint)?;
            let (next, slice) = applied
                .record_surface_steps(certificate.steps())?
                .edit_replay_cursor(|replay, _, _| {
                    end_tactic_surface_scope(replay, scope.take().expect("tactic scope is open"))
                })?;
            proof = next;
            if capture_this_tactic {
                finish_tactic_expansion_capture(expansion_capture.as_deref_mut(), &slice, false);
            }
            continue;
        }
        match tactic {
            ProofTactic::Mark(name) => {
                proof = proof.apply_step(SimpleProofStep::Mark(name.clone()))?;
            }
            ProofTactic::UnfoldResource(resource) => {
                proof = proof.apply_step(SimpleProofStep::UnfoldResource(resource.clone()))?;
            }
            ProofTactic::ObserveResource(resource) => {
                proof = proof.apply_step(SimpleProofStep::ObserveResource(resource.clone()))?;
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
                if at_function_exit {
                    let premises = match tactic {
                        ProofTactic::TransportUsing { premises, .. } => Some(premises.clone()),
                        ProofTactic::Transport { .. } => None,
                        _ => unreachable!(),
                    };
                    proof = defer_post_execution_on_proof(
                        proof,
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Transport {
                            source: surface_source.clone(),
                            target: surface_target.clone(),
                            premises,
                        },
                        scope.take(),
                    )?;
                    continue;
                }
                if at_function_entry {
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
                proof = proof.apply_step(SimpleProofStep::TransportUsing {
                    source: surface_source.clone(),
                    target: surface_target.clone(),
                    premises: surface_premises.clone(),
                })?;
            }
            ProofTactic::StepUsing(premises) => {
                proof = proof.apply_step(SimpleProofStep::StepUsing(premises.clone()))?;
            }
            ProofTactic::Step => {
                proof = proof.apply_step(SimpleProofStep::Step)?;
            }
            ProofTactic::SmartStep => {
                // Exact selection first, then the shared planner law; the
                // checked delta is pushed into this tactic's surface scope.
                let checkpoint = proof.checkpoint();
                let stepped = match proof.try_smart_step()? {
                    Some(stepped) => stepped,
                    None => proof.apply_planned_smart_step(tactic_index)?,
                };
                let certificate = stepped.certificate_since(&checkpoint)?;
                proof = stepped.record_surface_steps(certificate.steps())?;
            }
            ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths => {
                // Exact selection first, then the shared planner law; the
                // checked delta is pushed into this tactic's surface scope.
                let checkpoint = proof.checkpoint();
                let executed = match proof.try_exact_execute_to_exit()? {
                    Some(executed) => executed,
                    None => {
                        let force_all_paths = matches!(tactic, ProofTactic::SmartExecuteAllPaths);
                        proof.apply_planned_smart_execute(force_all_paths, tactic_index)?
                    }
                };
                let certificate = executed.certificate_since(&checkpoint)?;
                proof = executed.record_surface_steps(certificate.steps())?;
            }
            ProofTactic::ExecuteUntil(region_ref) => {
                let checkpoint = proof.checkpoint();
                if let Some(executed) = proof.try_linear_execute_until(region_ref)? {
                    let certificate = executed.certificate_since(&checkpoint)?;
                    proof = executed.record_surface_steps(certificate.steps())?;
                } else {
                    // The planner constructs the explicit checked operations
                    // from a scratch copy of the frontier; this Proof then
                    // applies exactly those operations.
                    let code_region = resolve_code_region_ref(
                        function_block,
                        region_ref,
                        claim_label,
                        tactic_index,
                    )?;
                    let CodeRegion::Statement(target_statement_index) = code_region else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `execute_until` expects a statement region"
                        )));
                    };
                    let (mut planning_replay, mut planning_state, mut planning_facts) = {
                        let view = proof.finalization_view()?;
                        let mut planning_replay = view.replay.clone();
                        planning_replay.planned_statement_transitions.clear();
                        planning_replay.proof_certificate_builder = ProofCertificateBuilder {
                            last_step_entry: view
                                .replay
                                .proof_certificate_builder
                                .last_step_entry
                                .clone(),
                            certificate_facts: ProofFactStore::from_ordered(view.facts.clone()),
                            ..ProofCertificateBuilder::default()
                        }
                        .into();
                        (planning_replay, view.state.clone(), view.facts)
                    };
                    execute_until_statement(
                        &mut planning_replay,
                        &mut planning_state,
                        &mut planning_facts,
                        function_block,
                        function,
                        parsed_function.parameters(),
                        arguments,
                        function_environment,
                        target_statement_index,
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
                                SimpleProofStep::Have { .. }
                                    | SimpleProofStep::UnfoldPredicate(_)
                                    | SimpleProofStep::TransportUsing { .. }
                                    | SimpleProofStep::StepUsing(_)
                            )
                        })
                        && construction
                            .steps
                            .iter()
                            .any(|step| matches!(step, SimpleProofStep::StepUsing(_)))
                    {
                        let mut executed = proof;
                        for step in &construction.steps {
                            executed = executed.apply_step(step.clone())?;
                        }
                        let certificate = executed.certificate_since(&checkpoint)?;
                        let (recorded, ()) = executed.edit_replay_cursor(|replay, _, _| {
                            for step in certificate.steps() {
                                replay.proof_certificate_builder.push_step(step.clone());
                            }
                            replay.proof_certificate_builder.last_step_entry =
                                construction.last_step_entry;
                        })?;
                        proof = recorded;
                    } else if let Some(blocker) = construction.blocker {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `execute_until` could not construct checked Proof operations: {blocker}"
                        )));
                    } else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `execute_until` found no checked Proof candidate"
                        )));
                    }
                }
            }
            ProofTactic::SmartFrame(region_ref) => {
                let ordered_deferred = frontier_region == ExecutionRegionKind::Function
                    && at_function_exit
                    && proof.replay_cursor()?.open_scopes == 0;
                let checkpoint = proof.checkpoint();
                let Some(framed) =
                    proof.try_smart_frame_at(region_ref.as_ref(), tactic_index, source_index)?
                else {
                    require_function_exit(
                        proof.replay_cursor()?,
                        claim_label,
                        tactic_index,
                        "frame",
                    )?;
                    if !claims
                        .iter()
                        .any(|claim| matches!(claim, FunctionClaimRef::Effect(_, _)))
                    {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `frame` has no effect claim to prove"
                        )));
                    }
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `frame` found no checked Proof candidate"
                    )));
                };
                let certificate = framed.certificate_since(&checkpoint)?;
                let (framed, recorded) = framed.edit_replay_cursor(|replay, _, _| {
                    let mut ordered_region_frame = false;
                    if ordered_deferred {
                        let mut deferred = replay.post_execution_tactics.pop().ok_or_else(|| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: Proof-owned frame retained no ordered deferral"
                            ))
                        })?;
                        ordered_region_frame =
                            matches!(deferred.tactic, PostExecutionTactic::FrameRegion(_));
                        if !ordered_region_frame {
                            let PostExecutionTactic::CheckedFrameUsing {
                                surface_tactics, ..
                            } = &mut deferred.tactic
                            else {
                                return Err(ClickError::new(format!(
                                    "`{claim_label}` tactic {tactic_index}: Proof-owned frame retained the wrong ordered operation"
                                )));
                            };
                            // Finalization still owns the outcome transition,
                            // but it must print this complete checked
                            // contribution at the deferred source position.
                            // Contextual frame premises can be established
                            // by leading `have` scopes.
                            *surface_tactics = Some(certificate.to_proof_tactics());
                            deferred.surface_recorded = false;
                        }
                        replay.post_execution_tactics.push(deferred);
                    }
                    // Function frames are recorded by their checked ordered
                    // drain. A region frame contributes facts at that drain
                    // but its exact simple form is already owned by this
                    // Proof, so retain the node now just as the former
                    // construction path did.
                    if !ordered_deferred || ordered_region_frame {
                        for step in certificate.steps() {
                            replay.proof_certificate_builder.push_step(step.clone());
                        }
                    }
                    Ok::<(), ClickError>(())
                })?;
                recorded?;
                let (next, slice) = framed.edit_replay_cursor(|replay, _, _| {
                    end_tactic_surface_scope(replay, scope.take().expect("tactic scope is open"))
                })?;
                proof = next;
                if capture_this_tactic && !proof_owned_smart_frame_deferred {
                    finish_tactic_expansion_capture(
                        expansion_capture.as_deref_mut(),
                        &slice,
                        false,
                    );
                }
                continue;
            }
            ProofTactic::FrameUsing {
                region: region_ref,
                premises: surface_premises,
            } => {
                // The one function-exit frame law: a qualified frame, or an
                // unqualified frame arriving as the first ordered outcome
                // operation while the frontier still owns its effect goal,
                // is a checked step on that goal. Any other unqualified
                // frame is an ordered outcome operation for the drain, which
                // re-lowers its premises after the deferred `have`s that
                // establish them.
                let cursor = proof.replay_cursor()?;
                let direct_function_frame = frontier_region == ExecutionRegionKind::Function
                    && at_function_exit
                    && cursor.open_scopes == 0
                    && (region_ref.is_some()
                        || cursor.post_execution_tactics.is_empty()
                            && proof.frontier_owns_effect_goal()
                            && proof.supports_checked_frame_using(None, surface_premises)?);
                if direct_function_frame {
                    // Premise lowering and exact availability are part of
                    // the simple transition; the ordered outcome drain
                    // receives only the resulting checked region-frame
                    // authority and never reinterprets the premise list.
                    let checkpoint = proof.checkpoint();
                    let framed = proof.apply_step_at(
                        SimpleProofStep::FrameUsing {
                            region: region_ref.clone(),
                            premises: surface_premises.to_vec(),
                        },
                        tactic_index,
                        source_index,
                    )?;
                    let certificate = framed.certificate_since(&checkpoint)?;
                    let (next, slice) = framed
                        .record_surface_steps(certificate.steps())?
                        .edit_replay_cursor(|replay, _, _| {
                            end_tactic_surface_scope(
                                replay,
                                scope.take().expect("tactic scope is open"),
                            )
                        })?;
                    proof = next;
                    if capture_this_tactic {
                        finish_tactic_expansion_capture(
                            expansion_capture.as_deref_mut(),
                            &slice,
                            false,
                        );
                    }
                    continue;
                }
                // Premise lowering records surface lowerings in the cursor;
                // a structural effect goal is closed by the same edit.
                let (checked, framed) = proof.edit_replay_cursor(|replay, state, facts| {
                    let all_pure_facts = facts.to_vec();
                    let mut frame_facts = Vec::new();
                    if !surface_premises.is_empty() {
                        let assumptions = assumptions_from_propositions(&all_pure_facts);
                        let pre_state = replay.old_reference_state(state).clone();
                        let deferred_ordered_exit =
                            frontier_region == ExecutionRegionKind::Function && at_function_exit;
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
                                    state,
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
                                && !exact_fact_is_available(&premise, &all_pure_facts)
                                && exactly_available_fact(&premise, &all_pure_facts).is_none()
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
                        frame_facts = all_pure_facts;
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
                            state,
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
                            replay,
                            scope.take().expect("tactic scope is open"),
                        );
                        return Ok((frame_facts, true));
                    }
                    Ok::<_, ClickError>((frame_facts, false))
                })?;
                proof = checked;
                let (frame_facts, closed_loop_effect_goal) = framed?;
                if closed_loop_effect_goal {
                    continue;
                }
                require_function_exit(proof.replay_cursor()?, claim_label, tactic_index, "frame")?;
                let view = proof.finalization_view()?;
                let replay = view.replay;
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
                if frontier_region == ExecutionRegionKind::Function
                    && at_function_exit
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
                    proof = defer_post_execution_on_proof(
                        proof,
                        tactic_index,
                        source_index,
                        deferred,
                        scope.take(),
                    )?;
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
                                view.state,
                                &frame_facts,
                            )?;
                        }
                        Some(CodeRegion::Loop(_)) => {}
                        Some(CodeRegion::Statement(_)) => {}
                    }
                }
                if frontier_region == ExecutionRegionKind::Function && at_function_exit {
                    let region = region_ref.clone().ok_or_else(|| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: contextual function `frame()` should have been deferred earlier"
                        ))
                    })?;
                    proof = defer_post_execution_on_proof(
                        proof,
                        tactic_index,
                        source_index,
                        PostExecutionTactic::FrameRegion(region),
                        None,
                    )?;
                }
            }
            ProofTactic::UnfoldPredicate(name) => {
                if frontier_region == ExecutionRegionKind::Function && at_function_exit {
                    proof = defer_post_execution_on_proof(
                        proof,
                        tactic_index,
                        source_index,
                        PostExecutionTactic::UnfoldPredicate(name.clone()),
                        scope.take(),
                    )?;
                    continue;
                }
                proof = proof.apply_step(SimpleProofStep::UnfoldPredicate(name.clone()))?;
            }
            ProofTactic::ApplyTheorem(application) => {
                // A mid-execution smart `apply` is selected as an explicit
                // `apply using` and applied directly to `Proof` before this
                // match (see the `ApplyTheorem` pre-pass above), so only the
                // function-exit form reaches this arm.
                if theorem_environment.get(&application.name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unknown theorem `{}`",
                        application.name
                    )));
                }
                debug_assert!(at_function_exit);
                if frontier_region == ExecutionRegionKind::Function {
                    proof = defer_post_execution_on_proof(
                        proof,
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Apply(application.clone()),
                        None,
                    )?;
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
                if at_function_exit {
                    if frontier_region == ExecutionRegionKind::Function {
                        proof = defer_post_execution_on_proof(
                            proof,
                            tactic_index,
                            source_index,
                            PostExecutionTactic::ApplyUsing {
                                application: application.clone(),
                                premises: premises.clone(),
                            },
                            scope.take(),
                        )?;
                        continue;
                    }
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: post-execution `apply using` is not available in this region proof"
                    )));
                }
                proof = proof.apply_step(SimpleProofStep::ApplyTheoremUsing {
                    application: application.clone(),
                    premises: premises.clone(),
                })?;
            }
            ProofTactic::FoldResource(resource) => {
                if at_function_exit {
                    if frontier_region == ExecutionRegionKind::Function {
                        proof = defer_post_execution_on_proof(
                            proof,
                            tactic_index,
                            source_index,
                            PostExecutionTactic::Fold(resource.clone()),
                            None,
                        )?;
                    } else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: post-execution `fold` is not available in this region proof"
                        )));
                    }
                } else {
                    proof = proof.apply_step(SimpleProofStep::FoldResource(resource.clone()))?;
                }
            }
            ProofTactic::Have(have) => {
                if at_function_exit {
                    if frontier_region == ExecutionRegionKind::Function {
                        proof = defer_post_execution_on_proof(
                            proof,
                            tactic_index,
                            source_index,
                            PostExecutionTactic::Have(have.clone()),
                            scope.take(),
                        )?;
                        continue;
                    }
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: post-execution `have` is not available in this region proof"
                    )));
                }
                // The one mid-execution `have` law: the nested Proof scope is
                // authoritative for every shape it supports, so an explicit
                // script that fails is an error and is never search-rescued;
                // the shared law checks only the shapes the scope declines.
                // The interpreter's prelude and epilogue own this tactic's
                // surface scope and expansion capture, so neither law
                // captures on its own; a smart body's checked delta is
                // recorded into the scope here.
                let checkpoint = proof.checkpoint();
                let nested =
                    solve_nested_have(proof.begin_have(have.proposition.clone())?, have, true)?;
                proof = match nested {
                    Some(selected) => {
                        let joined = selected.join()?;
                        // The prelude recorded a fully simple `have` as its
                        // own source tactic; any other body's checked delta
                        // is recorded here.
                        let recorded_by_prelude = ProofCertificate::from_proof_tactics(
                            std::slice::from_ref(&ProofTactic::Have(have.clone())),
                        )
                        .is_ok();
                        if recorded_by_prelude {
                            joined
                        } else {
                            let certificate = joined.certificate_since(&checkpoint)?;
                            joined.record_surface_steps(certificate.steps())?
                        }
                    }
                    None => {
                        proof.apply_mid_execution_have(None, have, tactic_index, source_index)?
                    }
                };
            }
            ProofTactic::If(_) | ProofTactic::Branch(_) | ProofTactic::Open(_) => {
                unreachable!("structured tactics are represented by internal proof nodes")
            }
            ProofTactic::Loop(_) => {
                unreachable!("frontier-local loops are replayed between linear tactic chunks")
            }
            ProofTactic::Witness(_) => {
                if frontier_region == ExecutionRegionKind::Function && at_function_exit {
                    let ProofTactic::Witness(witness) = tactic else {
                        unreachable!()
                    };
                    proof = defer_post_execution_on_proof(
                        proof,
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Witness(witness.clone()),
                        scope.take(),
                    )?;
                    continue;
                }
                require_function_exit(
                    proof.replay_cursor()?,
                    claim_label,
                    tactic_index,
                    "witness",
                )?;
            }
            ProofTactic::Choose(_) => {
                if frontier_region == ExecutionRegionKind::Function && at_function_exit {
                    let ProofTactic::Choose(choice) = tactic else {
                        unreachable!()
                    };
                    proof = defer_post_execution_on_proof(
                        proof,
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Choose(choice.clone()),
                        scope.take(),
                    )?;
                    continue;
                }
                require_function_exit(proof.replay_cursor()?, claim_label, tactic_index, "choose")?;
            }
            ProofTactic::Assumption | ProofTactic::Normalize | ProofTactic::Rewrite(_) => {
                if frontier_region != ExecutionRegionKind::LoopBody {
                    require_function_exit(
                        proof.replay_cursor()?,
                        claim_label,
                        tactic_index,
                        tactic_name(tactic),
                    )?;
                }
                if frontier_region == ExecutionRegionKind::Function && at_function_exit {
                    let post_tactic = match tactic {
                        ProofTactic::Assumption => PostExecutionTactic::Assumption,
                        ProofTactic::Normalize => PostExecutionTactic::Normalize,
                        ProofTactic::Rewrite(equality) => {
                            PostExecutionTactic::Rewrite(equality.clone())
                        }
                        _ => unreachable!(),
                    };
                    proof = defer_post_execution_on_proof(
                        proof,
                        tactic_index,
                        source_index,
                        post_tactic,
                        None,
                    )?;
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
                proof = proof
                    .apply_step(SimpleProofStep::CloseInvariants)?
                    .record_invariant_closer(tactic_index, source_index)?;
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
                if frontier_region != ExecutionRegionKind::LoopBody {
                    require_function_exit(
                        proof.replay_cursor()?,
                        claim_label,
                        tactic_index,
                        "simp",
                    )?;
                }
                if frontier_region == ExecutionRegionKind::LoopBody {
                    let (recorded, ()) = proof.edit_replay_cursor(|replay, _, _| {
                        replay.region_simp = Some((tactic_index, source_index));
                    })?;
                    proof = recorded;
                }
                if frontier_region == ExecutionRegionKind::Function && at_function_exit {
                    proof = defer_post_execution_on_proof(
                        proof,
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Simp,
                        None,
                    )?;
                }
            }
        }
        let (next, slice) = proof.edit_replay_cursor(|replay, _, _| {
            end_tactic_surface_scope(replay, scope.take().expect("tactic scope is open"))
        })?;
        proof = next;
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

    Ok(proof)
}
