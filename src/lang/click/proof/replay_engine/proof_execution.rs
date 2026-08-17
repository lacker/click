use super::*;

fn linear_execution_simple_steps(node: &InternalProofNode) -> Option<Vec<SimpleProofStep>> {
    match node {
        InternalProofNode::Done => Some(Vec::new()),
        InternalProofNode::Linear {
            tactics,
            continuation,
        } if matches!(continuation.as_ref(), InternalProofNode::Done) => {
            let mut steps = Vec::with_capacity(tactics.len());
            for indexed in tactics {
                let certificate =
                    ProofCertificate::from_proof_tactics(std::slice::from_ref(&indexed.tactic))
                        .ok()?;
                let [step] = certificate.steps() else {
                    return None;
                };
                if !matches!(
                    step,
                    SimpleProofStep::Mark(_)
                        | SimpleProofStep::Step
                        | SimpleProofStep::StepUsing(_)
                        | SimpleProofStep::TransportUsing { .. }
                        | SimpleProofStep::UnfoldPredicate(_)
                        | SimpleProofStep::UnfoldResource(_)
                        | SimpleProofStep::FoldResource(_)
                        | SimpleProofStep::ObserveResource(_)
                        | SimpleProofStep::ApplyTheoremUsing { .. }
                        | SimpleProofStep::CloseInvariants
                ) {
                    return None;
                }
                steps.push(step.clone());
            }
            Some(steps)
        }
        _ => None,
    }
}

/// Checks one linear all-simple `open` body on the same Proof that owns its
/// entry and close transitions. Kept out of the recursive structural driver
/// frame for the same stack-bound reason as the resource-step adapter.
#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn execute_linear_open_scope<'a>(
    context: ProofReplayContext,
    resource: ResourceClause,
    source_index: usize,
    steps: &[SimpleProofStep],
    function_block: &'a FunctionBlock,
    parsed_function: &'a syntax::C0Function,
    claim_label: &'a str,
    function_environment: &'a CExecutionEnvironment,
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    resource_environment: &'a ResourceEnvironment,
    theorem_environment: &'a TheoremEnvironment,
    function: &'a CFunction,
    arguments: &'a [CExpression],
    tactic_index: usize,
) -> Result<ProofReplayContext, ClickError> {
    let root = Proof::for_execution_frontier(
        claim_label,
        tactic_index,
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
    let mut scope = root.begin_open(resource, source_index)?;
    for step in steps {
        scope = scope.apply_step(step.clone())?;
    }
    let proof = scope.join()?;
    let certificate = proof.certificate();
    let mut context = proof.into_execution_context()?;
    for step in certificate.steps() {
        context
            .replay
            .proof_certificate_builder
            .push_step(step.clone());
    }
    Ok(context)
}

#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn try_execute_linear_open_scope<'a>(
    context: &ProofReplayContext,
    body: &InternalProofNode,
    resource: ResourceClause,
    source_index: usize,
    function_block: &'a FunctionBlock,
    parsed_function: &'a syntax::C0Function,
    claim_label: &'a str,
    function_environment: &'a CExecutionEnvironment,
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    resource_environment: &'a ResourceEnvironment,
    theorem_environment: &'a TheoremEnvironment,
    function: &'a CFunction,
    arguments: &'a [CExpression],
    tactic_index: usize,
) -> Result<Option<ProofReplayContext>, ClickError> {
    let Some(steps) = linear_execution_simple_steps(body) else {
        return Ok(None);
    };
    execute_linear_open_scope(
        context.clone(),
        resource,
        source_index,
        &steps,
        function_block,
        parsed_function,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        function,
        arguments,
        tactic_index,
    )
    .map(Some)
}

#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn try_execute_linear_open_scope_and_continue<'a>(
    context: &ProofReplayContext,
    body: &InternalProofNode,
    continuation: &InternalProofNode,
    resource: ResourceClause,
    source_index: usize,
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
    tactic_index: usize,
) -> Result<Option<Vec<ProofReplayContext>>, ClickError> {
    let Some(context) = try_execute_linear_open_scope(
        context,
        body,
        resource,
        source_index,
        function_block,
        parsed_function,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        function,
        arguments,
        tactic_index,
    )?
    else {
        return Ok(None);
    };
    execute_internal_proof(
        continuation,
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
    )
    .map(Some)
}

// Keep the alternative structural join temporaries out of the recursively
// evaluated `execute_internal_proof` frame. The deep pure-case regression is
// deliberately sensitive to even small growth in that frame.
#[inline(never)]
fn join_linear_execution_branches<'a>(
    branches: ExecutionProofBranches<'a>,
    empty: bool,
) -> Result<Proof<'a>, ClickError> {
    if branches.both_arms_at_function_exit() {
        branches.join_terminal()
    } else if empty {
        branches.join_empty()
    } else {
        branches.join()
    }
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn execute_internal_proof(
    node: &InternalProofNode,
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
) -> Result<Vec<ProofReplayContext>, ClickError> {
    match node {
        InternalProofNode::Done => Ok(vec![context]),
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => {
            let branch_path = context.branch_path.clone();
            let context = replay_linear_tactics(
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
                tactics,
            )
            .map_err(|error| add_proof_branch_path(error, &branch_path))?;
            execute_internal_proof(
                continuation,
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
            )
        }
        InternalProofNode::Open {
            index,
            source_index,
            resource,
            body,
            continuation,
        } => {
            if expansion_capture.is_none() {
                let linear = try_execute_linear_open_scope_and_continue(
                    &context,
                    body,
                    continuation,
                    resource.clone(),
                    *source_index,
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
                    *index,
                )?;
                if let Some(contexts) = linear {
                    return Ok(contexts);
                }
            }
            let mut opened = context;
            if opened.replay.is_at_function_exit() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {index}: `open` must begin before execution reaches function exit"
                )));
            }
            let surface_start = opened.replay.proof_certificate_builder.steps.len();
            opened.replay.open_scopes += 1;
            let unfolded = unfold_composite_resource(
                resource_environment,
                resource,
                parsed_function.parameters(),
                arguments,
                opened.state,
                &mut opened.pure_facts,
                &mut opened.replay.surface_propositions,
                predicate_environment,
                click_function_environment,
                claim_label,
                *index,
                ResourceBodyAccess::Open,
            )?;
            opened.state = unfolded.state;
            let preserve_exposed_body = unfolded.body_was_already_exposed;
            let opened_contexts = execute_internal_proof(
                body,
                opened,
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
            )?;
            let mut contexts = Vec::new();
            for mut closed in opened_contexts {
                closed.replay.open_scopes = closed.replay.open_scopes.saturating_sub(1);
                if closed.replay.is_at_function_exit() {
                    closed.replay.defer_post_execution(
                        *index,
                        *source_index,
                        PostExecutionTactic::CloseOpen {
                            resource: resource.clone(),
                            preserve_exposed_body,
                        },
                    );
                } else {
                    let pre_state = closed.replay.old_reference_state(&closed.state).clone();
                    closed.state = close_open_resource_at_current_point(
                        resource_environment,
                        resource,
                        claim_label,
                        *index,
                        &closed.pure_facts,
                        parsed_function.parameters(),
                        arguments,
                        &pre_state,
                        closed.state,
                        predicate_environment,
                        click_function_environment,
                        &closed.replay.unfolded_predicates,
                        preserve_exposed_body,
                    )?;
                }
                let nested = closed
                    .replay
                    .proof_certificate_builder
                    .steps
                    .split_off(surface_start);
                closed
                    .replay
                    .proof_certificate_builder
                    .steps
                    .push(SimpleProofStep::Open {
                        resource: resource.clone(),
                        proof: Box::new(ProofCertificate::from_steps(nested)),
                    });
                let mut continued = execute_internal_proof(
                    continuation,
                    closed,
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
                )?;
                contexts.append(&mut continued);
            }
            Ok(contexts)
        }
        InternalProofNode::If {
            index,
            condition,
            then_branch,
            else_branch,
            continuation,
        } => {
            let mut context = context;
            // A mid-execution case condition may name the current statement's
            // entry snapshot (`at(statement(N).entry, ...)`) before any step
            // has crossed that statement; record it so the spelling lowers.
            record_current_statement_entry(
                &mut context.replay,
                &context.state,
                function_block,
                function,
                arguments,
                claim_label,
                *index,
                "if",
            )?;
            let condition_text = describe_click_proposition(condition);
            let mut contexts = Vec::new();
            for (branch_name, value, branch) in [
                ("then", true, then_branch.as_ref()),
                ("else", false, else_branch.as_ref()),
            ] {
                let mut branch_context = context.clone();
                let branch_description =
                    format!("{branch_name} branch of proof `if {condition_text}`");
                branch_context.branch_path.push(branch_description);
                let feasible = introduce_proof_case_assumption(
                    &mut branch_context,
                    condition,
                    value,
                    *index,
                    parsed_function.parameters(),
                    arguments,
                    predicate_environment,
                    click_function_environment,
                    claim_label,
                )
                .map_err(|error| add_proof_branch_path(error, &branch_context.branch_path))?;
                if !feasible {
                    continue;
                }
                // Record where this proof-level case split sits in the claim's
                // surface record. Cross-context synthesis reassembles the
                // whole-claim certificate at exactly these recorded choices,
                // so the tactics a case runs are spelled inside its surface
                // `if` branch instead of leaking into sibling paths.
                if branch_context
                    .replay
                    .proof_certificate_builder
                    .blocker
                    .is_none()
                {
                    let tactic_offset = branch_context.replay.proof_certificate_builder.steps.len();
                    branch_context
                        .replay
                        .proof_certificate_builder
                        .path_choices
                        .push(SurfacePathChoice {
                            occurrence: *index,
                            condition: condition.clone(),
                            value,
                            tactic_offset,
                        });
                }
                let branch_contexts = execute_internal_proof(
                    branch,
                    branch_context,
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
                )?;
                for branch_context in branch_contexts {
                    let mut continued = execute_internal_proof(
                        continuation,
                        branch_context,
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
                    )?;
                    contexts.append(&mut continued);
                }
            }
            Ok(contexts)
        }
        InternalProofNode::Branch {
            index,
            ensuring,
            then_branch,
            else_branch,
            continuation,
        } => {
            // Ordinary linear simple arms advance only through the checked
            // execution Proof container. Expansion capture continues through
            // the legacy path until selected-source offsets migrate into the
            // same structural container.
            if expansion_capture.is_none()
                && ensuring.is_none()
                && let Some(then_steps) = linear_execution_simple_steps(then_branch)
                && let Some(else_steps) = linear_execution_simple_steps(else_branch)
            {
                let proof = Proof::for_execution_frontier(
                    claim_label,
                    *index,
                    context.clone(),
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
                let checkpoint = proof.checkpoint();
                let mut branches = proof.begin_execution_branch()?;
                if branches.has_both_feasible_arms() {
                    let empty = then_steps.is_empty() && else_steps.is_empty();
                    for step in then_steps {
                        branches = branches.apply_step(true, step)?;
                    }
                    for step in else_steps {
                        branches = branches.apply_step(false, step)?;
                    }
                    let proof = join_linear_execution_branches(branches, empty)?;
                    let certificate = proof.certificate_since(&checkpoint)?;
                    let mut joined_context = proof.into_execution_context()?;
                    for step in certificate.steps() {
                        joined_context
                            .replay
                            .proof_certificate_builder
                            .push_step(step.clone());
                    }
                    return execute_internal_proof(
                        continuation,
                        joined_context,
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
                    );
                }
            }
            let mut context = context;
            let statement_index = context.replay.frontier.next_statement_index;
            // The branch condition is spelled against the branch statement's
            // entry snapshot; record it so both the recorded surface choice
            // and a replayed `at(statement(N).entry, ...)` condition lower.
            record_current_statement_entry(
                &mut context.replay,
                &context.state,
                function_block,
                function,
                arguments,
                claim_label,
                *index,
                "branch",
            )?;
            let source_region = context
                .replay
                .source_layout
                .statement(statement_index)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {index}: `branch` could not resolve source statement({statement_index})"
                    ))
                })?;
            if !matches!(source_region.kind, SourceStatementKind::If { .. }) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {index}: `branch` requires a C `if` at the execution frontier, but statement({statement_index}) is not an `if`"
                )));
            }
            let continuation_index = source_region.continuation_node;
            let initial_continuation_depth = context.replay.frontier.continuations.len();
            let selected_source_index = context.replay.proof_site.as_ref().and_then(|site| {
                selected_tactic_index_for_site(expansion_capture.as_deref(), site)
            });
            let capture_in_continuation = selected_source_index
                .is_some_and(|wanted| internal_proof_contains_source_index(continuation, wanted));
            let branch_surface_condition = {
                let (_, _, statement, _) = next_top_level_statement_from_execution_point(
                    &context.replay,
                    &context.state,
                    function,
                    arguments,
                    claim_label,
                    *index,
                    "branch",
                )?;
                let CStatement::If { condition, .. } = statement else {
                    unreachable!("source branch was checked as an if above")
                };
                surface_with_source_site(
                    &surface_c_condition(&condition),
                    &ProgramPointRef {
                        region: CodeRegionRef::Statement(statement_index),
                        kind: ProgramPointKind::Entry,
                    },
                )?
            };
            let capture_condition = (selected_source_index.is_some() && !capture_in_continuation)
                .then(|| branch_surface_condition.clone());
            let branch_surface_start = context.replay.proof_certificate_builder.steps.len();
            let prior_choice_count = context.replay.proof_certificate_builder.path_choices.len();
            let branch_entry_snapshot = context
                .replay
                .program_point_states
                .get(&ProgramPointRef {
                    region: CodeRegionRef::Statement(statement_index),
                    kind: ProgramPointKind::Entry,
                })
                .cloned();
            // Spells a proof-`if` case around a context's arm record: the
            // branch decision as a surface path choice at the branch point,
            // and the C `if` entry (plus an empty arm's immediate completion)
            // as explicit steps. Used for contexts that do not rejoin — their
            // certificates replay the branch as a decided case.
            let retrofit_branch_case =
                |context: &mut ProofReplayContext, take_then: bool, empty_arm: bool| {
                    let builder = &mut context.replay.proof_certificate_builder;
                    if builder.blocker.is_some() {
                        return;
                    }
                    let entry_steps = 1 + usize::from(empty_arm);
                    for choice in builder.path_choices.iter_mut().skip(prior_choice_count) {
                        if choice.tactic_offset >= branch_surface_start {
                            choice.tactic_offset += entry_steps;
                        }
                    }
                    builder.path_choices.insert(
                        prior_choice_count,
                        SurfacePathChoice {
                            occurrence: statement_index,
                            condition: branch_surface_condition.clone(),
                            value: take_then,
                            tactic_offset: branch_surface_start,
                        },
                    );
                    let entry_step =
                        ProofCertificate::from_proof_tactics(&[ProofTactic::StepUsing(Vec::new())])
                            .expect("a plain step is a simple tactic")
                            .steps()[0]
                            .clone();
                    for _ in 0..entry_steps {
                        let insertion = branch_surface_start.min(builder.steps.len());
                        builder.steps.insert(insertion, entry_step.clone());
                    }
                };
            let mut completed_contexts = Vec::new();
            let mut continuing_contexts = Vec::new();
            let mut continuing_arm_values = Vec::new();
            for (branch_name, take_then, branch) in [
                ("then", true, then_branch.as_ref()),
                ("else", false, else_branch.as_ref()),
            ] {
                let mut branch_context = context.clone();
                branch_context.branch_path.push(format!(
                    "{branch_name} arm of C `if` at statement({statement_index})"
                ));
                let entered = execute_branch_step_from_execution_point(
                    &mut branch_context.replay,
                    &mut branch_context.state,
                    &mut branch_context.pure_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    claim_label,
                    *index,
                    "branch",
                    Some(take_then),
                    StatementPrerequisitePolicy::Contextual,
                    BranchStepPolicy::Explore,
                    true,
                    None,
                )
                .map_err(|error| add_proof_branch_path(error, &branch_context.branch_path))?;
                if !entered {
                    continue;
                }
                branch_context.replay.has_structured_branch_history = true;
                if let Some(condition) = &capture_condition {
                    branch_context
                        .replay
                        .deferred_expansion_path_choices
                        .push(SurfacePathChoice {
                            occurrence: statement_index,
                            condition: condition.clone(),
                            value: take_then,
                            // The path is attached to the selected tactic's
                            // standalone certificate, whose prefix starts at
                            // offset zero after capture resets surface replay.
                            tactic_offset: 0,
                        });
                }
                let empty_arm = branch_context
                    .replay
                    .completed_branch_regions
                    .contains(&statement_index);
                let branch_contexts = execute_internal_proof(
                    branch,
                    branch_context,
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
                )?;
                for mut branch_context in branch_contexts {
                    let returned = branch_context.replay.is_at_function_exit();
                    let reached_continuation = branch_context
                        .replay
                        .completed_branch_regions
                        .contains(&statement_index)
                        && branch_context.replay.frontier.continuations.len()
                            <= initial_continuation_depth;
                    if !reached_continuation {
                        return Err(add_proof_branch_path(
                            ClickError::new(format!(
                                "`{claim_label}` tactic {index}: `{branch_name}` arm of `branch` must stop at the shared continuation statement({continuation_index}); its frontier is statement({})",
                                branch_context.replay.frontier.next_statement_index
                            )),
                            &branch_context.branch_path,
                        ));
                    }
                    if returned {
                        // A context that finished inside the arm never
                        // rejoins; its certificate replays the branch as a
                        // decided proof case.
                        retrofit_branch_case(&mut branch_context, take_then, empty_arm);
                        completed_contexts.push(branch_context);
                        continue;
                    }
                    continuing_contexts.push(branch_context);
                    continuing_arm_values.push((take_then, empty_arm));
                }
            }
            if completed_contexts.is_empty() && continuing_contexts.is_empty() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {index}: `branch` found no feasible C `if` arm"
                )));
            }
            if continuing_contexts.is_empty() {
                return Ok(completed_contexts);
            }

            // Rebuild the claim-level surface record across the joining arms
            // before their contexts merge, so neither arm's execution record
            // is silently dropped from the claim certificate. A join records
            // the branch tactic itself — its join (and, under `ensuring`,
            // its interface abstraction) is part of the proof, and replaying
            // a concretized `if` would not reproduce the joined context. A
            // single surviving arm replays as a decided proof case instead.
            let joined_surface_builder = if completed_contexts.is_empty()
                && (ensuring.is_some() || continuing_contexts.len() > 1)
            {
                let mut then_builders = Vec::new();
                let mut else_builders = Vec::new();
                let mut arm_blocker = None;
                for ((take_then, _), arm_context) in
                    continuing_arm_values.iter().zip(&continuing_contexts)
                {
                    let builder = &arm_context.replay.proof_certificate_builder;
                    if let Some(message) = &builder.blocker {
                        arm_blocker.get_or_insert_with(|| message.clone());
                        continue;
                    }
                    let mut arm_builder = builder.clone();
                    let steps = if arm_builder.steps.len() >= branch_surface_start {
                        arm_builder.steps.split_off(branch_surface_start)
                    } else {
                        Vec::new()
                    };
                    let mut choices = if arm_builder.path_choices.len() >= prior_choice_count {
                        arm_builder.path_choices.split_off(prior_choice_count)
                    } else {
                        Vec::new()
                    };
                    for choice in &mut choices {
                        choice.tactic_offset =
                            choice.tactic_offset.saturating_sub(branch_surface_start);
                    }
                    let arm_builder = ProofCertificateBuilder {
                        steps,
                        path_choices: choices,
                        ..ProofCertificateBuilder::default()
                    };
                    if *take_then {
                        then_builders.push(arm_builder);
                    } else {
                        else_builders.push(arm_builder);
                    }
                }
                let mut merged = continuing_contexts[0]
                    .replay
                    .proof_certificate_builder
                    .clone()
                    .into_value();
                merged.steps.truncate(branch_surface_start);
                merged.path_choices.truncate(prior_choice_count);
                if let Some(message) = arm_blocker {
                    merged.block(message);
                } else {
                    let arm_proof = |builders: Vec<ProofCertificateBuilder>| {
                        if builders.is_empty() {
                            Ok(ProofCertificate::from_steps(Vec::new()))
                        } else {
                            synthesize_surface_paths(builders).map(ProofCertificate::from_steps)
                        }
                    };
                    match (arm_proof(then_builders), arm_proof(else_builders)) {
                        (Ok(then_proof), Ok(else_proof)) => {
                            merged.steps.push(SimpleProofStep::Branch {
                                ensuring: ensuring.clone(),
                                then_proof: Box::new(then_proof),
                                else_proof: Box::new(else_proof),
                            });
                        }
                        (Err(message), _) | (_, Err(message)) => merged.block(format!(
                            "could not synthesize `branch` arm surface record: {message}"
                        )),
                    }
                }
                Some(merged)
            } else {
                // Some arm returned (or only one arm survives): every
                // context replays the branch as a decided proof case, and
                // cross-context synthesis rebuilds the surface `if` from the
                // retrofitted choices.
                for ((take_then, empty_arm), context) in continuing_arm_values
                    .iter()
                    .zip(continuing_contexts.iter_mut())
                {
                    retrofit_branch_case(context, *take_then, *empty_arm);
                }
                (continuing_contexts.len() > 1).then(|| {
                    let builders = continuing_contexts
                        .iter()
                        .map(|context| {
                            context
                                .replay
                                .proof_certificate_builder
                                .clone()
                                .into_value()
                        })
                        .collect::<Vec<_>>();
                    let mut merged = builders[0].clone();
                    merged.path_choices.truncate(prior_choice_count);
                    match synthesize_surface_alternatives(builders) {
                        Ok(steps) => merged.steps = steps,
                        Err(message) => merged.block(format!(
                            "could not synthesize `branch` arms into one surface record: {message}"
                        )),
                    }
                    merged
                })
            };

            let mut joined_context = if let Some(assertions) = ensuring {
                let mut common_pure_facts = continuing_contexts[0].pure_facts.clone();
                common_pure_facts.retain(|fact| {
                    continuing_contexts
                        .iter()
                        .skip(1)
                        .all(|context| context.pure_facts.contains(fact))
                });
                let mut common_resource_facts =
                    continuing_contexts[0].state.resources().facts().to_vec();
                common_resource_facts.retain(|fact| {
                    continuing_contexts
                        .iter()
                        .skip(1)
                        .all(|context| context.state.resources().facts().contains(fact))
                });
                let mut stable_join_locals = continuing_contexts[0]
                    .state
                    .locals()
                    .object_values()
                    .map(|(name, value)| (name.to_string(), value.clone()))
                    .collect::<BTreeMap<_, _>>();
                stable_join_locals.retain(|name, value| {
                    continuing_contexts
                        .iter()
                        .skip(1)
                        .all(|context| context.state.locals().get(name) == Some(value))
                });
                let joined_frontier = continuing_contexts[0].replay.frontier.next_statement_index;
                if continuing_contexts
                    .iter()
                    .skip(1)
                    .any(|context| context.replay.frontier.next_statement_index != joined_frontier)
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {index}: `branch` arms did not reach one common execution frontier"
                    )));
                }
                let target = ProgramPointRef {
                    region: CodeRegionRef::Statement(joined_frontier),
                    kind: ProgramPointKind::Entry,
                };
                let needs_abstraction = continuing_contexts.len() > 1;
                let mut joined: Option<ProofReplayContext> = None;
                for mut branch_context in continuing_contexts {
                    apply_branch_interface(
                        &target,
                        assertions,
                        *index,
                        &mut branch_context.replay,
                        &mut branch_context.state,
                        &mut branch_context.pure_facts,
                        parsed_function.parameters(),
                        arguments,
                        predicate_environment,
                        click_function_environment,
                        resource_environment,
                        claim_label,
                        &stable_join_locals,
                        needs_abstraction,
                    )
                    .map_err(|error| add_proof_branch_path(error, &branch_context.branch_path))?;
                    for fact in &common_pure_facts {
                        if !branch_context.pure_facts.contains(fact) {
                            branch_context.pure_facts.push(fact.clone());
                        }
                    }
                    let assumptions = assumptions_from_propositions(&branch_context.pure_facts);
                    let additional_common_resources = common_resource_facts
                        .iter()
                        .filter(|fact| !branch_context.state.resources().facts().contains(fact))
                        .cloned()
                        .collect::<Vec<_>>();
                    let resources = branch_context
                        .state
                        .resources()
                        .clone()
                        .try_compose_with_facts(additional_common_resources, &assumptions)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {index}: invalid automatic common `branch` resource interface: {error:?}"
                            ))
                        })?;
                    branch_context.state = branch_context.state.with_resource_context(resources);
                    if let Some(joined_context) = &mut joined {
                        append_execution_effect_facts(
                            &mut joined_context.replay.effect_facts,
                            &branch_context.replay.effect_facts,
                        );
                    } else {
                        joined = Some(branch_context);
                    }
                }
                joined.expect("at least one continuing branch context")
            } else if continuing_contexts.len() == 1 {
                continuing_contexts.remove(0)
            } else {
                let common_state = continuing_contexts[0].state.clone();
                if continuing_contexts
                    .iter()
                    .skip(1)
                    .any(|context| context.state != common_state)
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {index}: `branch` arms reach the common frontier with different states; add an `ensuring` block describing the facts and resources needed afterward"
                    )));
                }
                let mut joined = continuing_contexts.remove(0);
                joined.pure_facts.retain(|fact| {
                    continuing_contexts
                        .iter()
                        .all(|context| context.pure_facts.contains(fact))
                });
                joined.replay.program_point_states.retain(|point, state| {
                    continuing_contexts.iter().all(|context| {
                        context.replay.program_point_states.get(point) == Some(state)
                    })
                });
                for context in &continuing_contexts {
                    append_execution_effect_facts(
                        &mut joined.replay.effect_facts,
                        &context.replay.effect_facts,
                    );
                }
                joined
            };
            if let Some(builder) = joined_surface_builder {
                joined_context.replay.proof_certificate_builder = builder.into();
            }
            // Branch abstraction discards source-boundary snapshots, but the
            // recorded surface branch choice is spelled against the branch
            // statement's own entry snapshot — pre-branch history the claim
            // certificate must still be able to lower at function exit.
            let branch_entry_point = ProgramPointRef {
                region: CodeRegionRef::Statement(statement_index),
                kind: ProgramPointKind::Entry,
            };
            if let Some(snapshot) = branch_entry_snapshot
                && !joined_context
                    .replay
                    .program_point_states
                    .contains_key(&branch_entry_point)
            {
                joined_context
                    .replay
                    .program_point_states
                    .insert(branch_entry_point, snapshot);
            }
            joined_context.branch_path.clear();
            joined_context.replay.case_assumptions.clear();
            let mut continued = execute_internal_proof(
                continuation,
                joined_context,
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
            )?;
            completed_contexts.append(&mut continued);
            Ok(completed_contexts)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn introduce_proof_case_assumption(
    context: &mut ProofReplayContext,
    condition: &ClickProposition,
    value: bool,
    tactic_index: usize,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
) -> Result<bool, ClickError> {
    if context.replay.is_at_function_exit()
        && context.replay.has_structured_branch_history
        && proof_case_is_stable_program_point_condition(condition)
    {
        // A source-qualified condition can still be lowered without choosing
        // one return outcome. Use it immediately when possible so a logical
        // certificate nested under an already selected C path does not
        // manufacture its contradictory sibling at function exit. Conditions
        // involving `result` or the post-state retain the deferred per-outcome
        // handling below.
        if let Ok(proposition) = lower_point_proposition(
            condition,
            &context.pure_facts,
            parameters,
            arguments,
            context.replay.old_reference_state(&context.state),
            &context.state,
            None,
            &context.replay.program_point_states,
            predicate_environment,
            click_function_environment,
        ) {
            let surface_fact = if value {
                condition.clone()
            } else {
                negate_click_proposition(condition)
            };
            let kernel_fact = if value {
                proposition
            } else {
                match proposition {
                    Proposition::ConditionIs(condition, value) => {
                        Proposition::ConditionIs(condition, !value)
                    }
                    Proposition::Not(body) => *body,
                    proposition => Proposition::Not(Box::new(proposition)),
                }
            };
            if context
                .pure_facts
                .iter()
                .any(|available| propositions_are_exact_negations(available, &kernel_fact))
            {
                return Ok(false);
            }
            context
                .replay
                .surface_propositions
                .record_lowering(&surface_fact, &kernel_fact)?;
            context.pure_facts.push(kernel_fact.clone());
            context.replay.case_assumptions.push(ReplayCaseAssumption {
                tactic_index,
                condition: condition.clone(),
                value,
                fact: Some(kernel_fact),
                at_function_entry: false,
            });
            return Ok(true);
        }
    }
    if context.replay.is_at_function_exit() {
        context.replay.case_assumptions.push(ReplayCaseAssumption {
            tactic_index,
            condition: condition.clone(),
            value,
            fact: None,
            at_function_entry: false,
        });
        return Ok(true);
    }
    let at_function_entry = context.replay.is_at_function_entry();
    let proposition = lower_point_proposition(
        condition,
        &context.pure_facts,
        parameters,
        arguments,
        context.replay.old_reference_state(&context.state),
        &context.state,
        None,
        &context.replay.program_point_states,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not lower `if` condition: {message}"
        ))
    })?;
    let surface_fact = if value {
        condition.clone()
    } else {
        negate_click_proposition(condition)
    };
    let kernel_fact = if value {
        proposition
    } else {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                Proposition::ConditionIs(condition, !value)
            }
            Proposition::Not(body) => *body,
            proposition => Proposition::Not(Box::new(proposition)),
        }
    };
    if context
        .pure_facts
        .iter()
        .any(|available| propositions_are_exact_negations(available, &kernel_fact))
    {
        return Ok(false);
    }
    context
        .replay
        .surface_propositions
        .record_lowering(&surface_fact, &kernel_fact)?;
    context.pure_facts.push(kernel_fact.clone());
    context.replay.case_assumptions.push(ReplayCaseAssumption {
        tactic_index,
        condition: condition.clone(),
        value,
        fact: Some(kernel_fact),
        at_function_entry,
    });
    Ok(true)
}

fn proof_case_is_stable_program_point_condition(proposition: &ClickProposition) -> bool {
    let expression_is_stable = |expression: &ContractExpression| {
        matches!(
            expression,
            ContractExpression::At {
                selector: VisitSelector::ProgramPoint(_),
                ..
            } | ContractExpression::Old(_)
        )
    };
    fn stable(
        proposition: &ClickProposition,
        expression_is_stable: &impl Fn(&ContractExpression) -> bool,
    ) -> bool {
        match proposition {
            ClickProposition::Comparison { left, right, .. } => {
                expression_is_stable(left) && expression_is_stable(right)
            }
            ClickProposition::Defined { expression } => expression_is_stable(expression),
            ClickProposition::At {
                selector: VisitSelector::ProgramPoint(_),
                ..
            } => true,
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                stable(left, expression_is_stable) && stable(right, expression_is_stable)
            }
            ClickProposition::Not(body) => stable(body, expression_is_stable),
            ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. }
            | ClickProposition::ForAll { .. }
            | ClickProposition::Exists { .. }
            | ClickProposition::RangeAll { .. }
            | ClickProposition::RangeAny { .. }
            | ClickProposition::PredicateCall { .. } => false,
        }
    }
    stable(proposition, &expression_is_stable)
}

fn add_proof_branch_context(error: ClickError, branch: &str) -> ClickError {
    ClickError::new(format!("in {branch}:\n{}", error.message()))
}

pub(in crate::lang::click::proof) fn add_proof_branch_path(
    mut error: ClickError,
    branch_path: &PersistentSequence<String>,
) -> ClickError {
    for branch in branch_path.iter().rev() {
        error = add_proof_branch_context(error, branch);
    }
    error
}
