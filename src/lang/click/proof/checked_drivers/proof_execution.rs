use super::*;

thread_local! {
    /// The source location of the most recent driver decline, so the terminal
    /// "shape not accepted" diagnostic can say which driver rule declined.
    static DRIVER_DECLINES: std::cell::RefCell<Vec<&'static std::panic::Location<'static>>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Declines the current shape and records where, for the terminal diagnostic.
#[track_caller]
fn decline<T>() -> Result<Option<T>, ClickError> {
    let location = std::panic::Location::caller();
    DRIVER_DECLINES.with(|declines| declines.borrow_mut().push(location));
    Ok(None)
}

/// Takes the recorded decline locations, in order.
pub(in crate::lang::click::proof) fn take_driver_declines()
-> Vec<&'static std::panic::Location<'static>> {
    DRIVER_DECLINES.with(|declines| std::mem::take(&mut *declines.borrow_mut()))
}

/// The explicit proof step written by a simple tactic in an execution arm. A
/// source `step()` is the bare statement step; the other simple tactic forms
/// map as themselves.
fn arm_proof_step(tactic: &ProofTactic) -> Option<ProofStep> {
    match tactic {
        ProofTactic::Step => Some(ProofStep::Step),
        tactic => linear_execution_proof_step(tactic),
    }
}

fn linear_execution_proof_step(tactic: &ProofTactic) -> Option<ProofStep> {
    match tactic {
        ProofTactic::Mark(name) => Some(ProofStep::Mark(name.clone())),
        ProofTactic::Step => Some(ProofStep::Step),
        ProofTactic::TransportUsing {
            source,
            target,
            premises,
        } => Some(ProofStep::TransportUsing {
            source: source.clone(),
            target: target.clone(),
            premises: premises.clone(),
        }),
        ProofTactic::UnfoldPredicate(name) => Some(ProofStep::UnfoldPredicate(name.clone())),
        ProofTactic::UnfoldResource(resource) => Some(ProofStep::UnfoldResource(resource.clone())),
        ProofTactic::FoldResource(resource) => Some(ProofStep::FoldResource(resource.clone())),
        ProofTactic::ObserveResource(resource) => {
            Some(ProofStep::ObserveResource(resource.clone()))
        }
        ProofTactic::ApplyTheoremUsing {
            application,
            premises,
        } => Some(ProofStep::ApplyTheoremUsing {
            application: application.clone(),
            premises: premises.clone(),
        }),
        ProofTactic::FrameUsing { region, premises } => Some(ProofStep::FrameUsing {
            region: region.clone(),
            premises: premises.clone(),
        }),
        ProofTactic::CloseInvariants => Some(ProofStep::CloseInvariants),
        _ => None,
    }
}

fn expanded_execution_arm_supported(steps: &[ProofStep]) -> bool {
    steps.is_empty()
        || (matches!(steps.first(), Some(ProofStep::Step))
            && matches!(steps.last(), Some(ProofStep::Step)))
}

fn linear_execution_tactics(node: &InternalProofNode) -> Option<&[IndexedTactic]> {
    match node {
        InternalProofNode::Done => Some(&[]),
        InternalProofNode::Linear {
            tactics,
            continuation,
        } if matches!(continuation.as_ref(), InternalProofNode::Done) => Some(tactics),
        _ => None,
    }
}

pub(in crate::lang::click::proof) fn internal_proof_first_index(
    node: &InternalProofNode,
) -> Option<usize> {
    match node {
        InternalProofNode::Done => None,
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => tactics
            .first()
            .map(|indexed| indexed.index)
            .or_else(|| internal_proof_first_index(continuation)),
        InternalProofNode::Open { index, .. }
        | InternalProofNode::If { index, .. }
        | InternalProofNode::Branch { index, .. } => Some(*index),
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum CheckedExecutionRegionEnd {
    SharedContinuation,
    FunctionExit,
}

// The source interpreter applies the same bound below. The direct structural
// driver enforces it before recursive descent so nested explicit branches do
// not reserve an unbounded Rust stack either.
const MAX_CHECKED_EXECUTION_REGION_DEPTH: usize = 12;

fn checked_execution_arm_tactics_end(
    tactics: &[IndexedTactic],
    initial: CheckedExecutionRegionEnd,
) -> Option<CheckedExecutionRegionEnd> {
    let mut at_function_exit = initial == CheckedExecutionRegionEnd::FunctionExit;
    // A `step()` may execute a `return`; a post-execution tactic after one
    // classifies the arm as reaching function exit. The driver checks the
    // actual frontier.
    let mut may_exit = false;
    for indexed in tactics {
        if at_function_exit {
            flat_post_execution_tactic(&indexed.tactic)?;
            continue;
        }
        if matches!(
            indexed.tactic,
            ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths
        ) {
            at_function_exit = true;
            continue;
        }
        if matches!(indexed.tactic, ProofTactic::Step) {
            may_exit = true;
            continue;
        }
        if linear_execution_proof_step(&indexed.tactic).is_none()
            && !matches!(
                indexed.tactic,
                ProofTactic::ApplyTheorem(_) | ProofTactic::Transport { .. } | ProofTactic::Have(_)
            )
        {
            if may_exit && flat_post_execution_tactic(&indexed.tactic).is_some() {
                at_function_exit = true;
                continue;
            }
            return None;
        }
    }
    Some(if at_function_exit {
        CheckedExecutionRegionEnd::FunctionExit
    } else {
        CheckedExecutionRegionEnd::SharedContinuation
    })
}

/// Classifies the supported execution-region grammar used inside a checked
/// branch arm. Linear prefixes and nested execution branches are accepted;
/// every sibling pair must agree on whether it returns to a shared frontier
/// or completes at function exit.
fn checked_execution_region_end(node: &InternalProofNode) -> Option<CheckedExecutionRegionEnd> {
    checked_execution_region_end_at(node, 0, CheckedExecutionRegionEnd::SharedContinuation)
}

fn checked_execution_region_end_at(
    node: &InternalProofNode,
    depth: usize,
    initial: CheckedExecutionRegionEnd,
) -> Option<CheckedExecutionRegionEnd> {
    if depth >= MAX_CHECKED_EXECUTION_REGION_DEPTH {
        return None;
    }
    match node {
        InternalProofNode::Done => Some(initial),
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => checked_execution_region_end_at(
            continuation,
            depth + 1,
            checked_execution_arm_tactics_end(tactics, initial)?,
        ),
        InternalProofNode::Branch {
            then_branch,
            else_branch,
            continuation,
            ..
        } => {
            if initial == CheckedExecutionRegionEnd::FunctionExit {
                return None;
            }
            let then_end = checked_execution_region_end_at(then_branch, depth + 1, initial)?;
            let else_end = checked_execution_region_end_at(else_branch, depth + 1, initial)?;
            if then_end != else_end {
                return None;
            }
            checked_execution_region_end_at(continuation, depth + 1, then_end)
        }
        InternalProofNode::Open {
            body, continuation, ..
        } => {
            if initial == CheckedExecutionRegionEnd::FunctionExit {
                return None;
            }
            let body_end = checked_execution_region_end_at(body, depth + 1, initial)?;
            checked_execution_region_end_at(continuation, depth + 1, body_end)
        }
        InternalProofNode::If {
            then_branch,
            else_branch,
            continuation,
            ..
        } => {
            let then_end = checked_execution_region_end_at(then_branch, depth + 1, initial)?;
            let else_end = checked_execution_region_end_at(else_branch, depth + 1, initial)?;
            (then_end == CheckedExecutionRegionEnd::FunctionExit
                && else_end == CheckedExecutionRegionEnd::FunctionExit
                && matches!(continuation.as_ref(), InternalProofNode::Done))
            .then_some(CheckedExecutionRegionEnd::FunctionExit)
        }
    }
}

fn checked_execution_region_pair(
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
) -> Option<CheckedExecutionRegionEnd> {
    let then_end = checked_execution_region_end(then_branch)?;
    (checked_execution_region_end(else_branch)? == then_end).then_some(then_end)
}

/// A `branch` whose arms end differently: one returns, the other reaches
/// the shared continuation. The driver runs the continuation inside the
/// continuing arm and joins both arms terminally.
fn checked_execution_region_pair_is_mixed(
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
) -> bool {
    matches!(
        (
            checked_execution_region_end(then_branch),
            checked_execution_region_end(else_branch),
        ),
        (Some(then_end), Some(else_end)) if then_end != else_end
    )
}

fn checked_execution_region_is_empty(node: &InternalProofNode) -> bool {
    match node {
        InternalProofNode::Done => true,
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => tactics.is_empty() && checked_execution_region_is_empty(continuation),
        _ => false,
    }
}

fn checked_execution_region_contains_source(node: &InternalProofNode, source_index: usize) -> bool {
    checked_execution_region_contains_source_at(node, source_index, 0)
}

fn checked_execution_region_contains_source_at(
    node: &InternalProofNode,
    source_index: usize,
    depth: usize,
) -> bool {
    if depth >= MAX_CHECKED_EXECUTION_REGION_DEPTH {
        return false;
    }
    match node {
        InternalProofNode::Done => false,
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => {
            tactics
                .iter()
                .any(|indexed| indexed.source_index == source_index)
                || checked_execution_region_contains_source_at(
                    continuation,
                    source_index,
                    depth + 1,
                )
        }
        InternalProofNode::Branch {
            source_index: branch_source_index,
            then_branch,
            else_branch,
            continuation,
            ..
        } => {
            *branch_source_index == source_index
                || checked_execution_region_contains_source_at(then_branch, source_index, depth + 1)
                || checked_execution_region_contains_source_at(else_branch, source_index, depth + 1)
                || checked_execution_region_contains_source_at(
                    continuation,
                    source_index,
                    depth + 1,
                )
        }
        InternalProofNode::Open {
            source_index: open_source_index,
            body,
            continuation,
            ..
        } => {
            *open_source_index == source_index
                || checked_execution_region_contains_source_at(body, source_index, depth + 1)
                || checked_execution_region_contains_source_at(
                    continuation,
                    source_index,
                    depth + 1,
                )
        }
        InternalProofNode::If {
            source_index: if_source_index,
            then_branch,
            else_branch,
            continuation,
            ..
        } => {
            *if_source_index == source_index
                || checked_execution_region_contains_source_at(then_branch, source_index, depth + 1)
                || checked_execution_region_contains_source_at(else_branch, source_index, depth + 1)
                || checked_execution_region_contains_source_at(
                    continuation,
                    source_index,
                    depth + 1,
                )
        }
    }
}

fn internal_proof_contains_frame(node: &InternalProofNode) -> bool {
    match node {
        InternalProofNode::Done => false,
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => {
            tactics.iter().any(|indexed| {
                matches!(
                    indexed.tactic,
                    ProofTactic::SmartFrame(_) | ProofTactic::FrameUsing { .. }
                )
            }) || internal_proof_contains_frame(continuation)
        }
        InternalProofNode::Open {
            body, continuation, ..
        } => internal_proof_contains_frame(body) || internal_proof_contains_frame(continuation),
        InternalProofNode::If {
            then_branch,
            else_branch,
            continuation,
            ..
        }
        | InternalProofNode::Branch {
            then_branch,
            else_branch,
            continuation,
            ..
        } => {
            internal_proof_contains_frame(then_branch)
                || internal_proof_contains_frame(else_branch)
                || internal_proof_contains_frame(continuation)
        }
    }
}

fn checked_linear_continuation_tactic(tactic: &ProofTactic) -> bool {
    linear_execution_proof_step(tactic).is_some()
        || matches!(
            tactic,
            ProofTactic::Step
                | ProofTactic::ApplyTheorem(_)
                | ProofTactic::Transport { .. }
                | ProofTactic::Have(_)
                | ProofTactic::ExecuteUntil(_)
                | ProofTactic::SmartExecute
                | ProofTactic::SmartExecuteAllPaths
                | ProofTactic::SmartFrame(_)
                | ProofTactic::Loop(_)
        )
}

fn checked_linear_continuation_reaches_frame(node: &InternalProofNode) -> bool {
    let Some(tactics) = linear_execution_tactics(node) else {
        return false;
    };
    for indexed in tactics {
        if matches!(
            indexed.tactic,
            ProofTactic::SmartFrame(_) | ProofTactic::FrameUsing { .. }
        ) {
            return true;
        }
        if !checked_linear_continuation_tactic(&indexed.tactic) {
            return false;
        }
    }
    false
}

fn flat_post_execution_tactic(tactic: &ProofTactic) -> Option<PostExecutionTactic> {
    match tactic {
        ProofTactic::FoldResource(resource) => Some(PostExecutionTactic::Fold(resource.clone())),
        ProofTactic::UnfoldPredicate(name) => {
            Some(PostExecutionTactic::UnfoldPredicate(name.clone()))
        }
        ProofTactic::ApplyTheorem(application) => {
            Some(PostExecutionTactic::Apply(application.clone()))
        }
        ProofTactic::ApplyTheoremUsing {
            application,
            premises,
        } => Some(PostExecutionTactic::ApplyUsing {
            application: application.clone(),
            premises: premises.clone(),
        }),
        ProofTactic::Have(have) => Some(PostExecutionTactic::Have(have.clone())),
        ProofTactic::Transport { source, target } => Some(PostExecutionTactic::Transport {
            source: source.clone(),
            target: target.clone(),
            premises: None,
        }),
        ProofTactic::TransportUsing {
            source,
            target,
            premises,
        } => Some(PostExecutionTactic::Transport {
            source: source.clone(),
            target: target.clone(),
            premises: Some(premises.clone()),
        }),
        ProofTactic::Choose(choice) => Some(PostExecutionTactic::Choose(choice.clone())),
        ProofTactic::Witness(witness) => Some(PostExecutionTactic::Witness(witness.clone())),
        ProofTactic::Assumption => Some(PostExecutionTactic::Assumption),
        ProofTactic::Normalize => Some(PostExecutionTactic::Normalize),
        ProofTactic::Rewrite(equality) => Some(PostExecutionTactic::Rewrite(equality.clone())),
        ProofTactic::FrameUsing { region, premises } => Some(PostExecutionTactic::FrameUsing {
            region: region.clone(),
            premises: premises.clone(),
        }),
        ProofTactic::Simp => Some(PostExecutionTactic::Simp),
        _ => None,
    }
}

/// Converts a supported post-execution syntax region into cursor metadata.
/// This performs no proof transition and stores no semantic state; each leaf
/// operation is checked later against the focused outcome `Proof`.
fn deferred_post_execution_linear_region(
    tactics: &[IndexedTactic],
    continuation: &InternalProofNode,
) -> Option<Vec<DeferredPostExecutionTactic>> {
    let mut deferred = tactics
        .iter()
        .map(|indexed| {
            // Inside a deferred region (an arm of a post-execution `if`)
            // a bare `frame()` is the ambient function frame checked per
            // outcome path at finalization; the arm applies only on the
            // paths that take it, so there is no Proof to search now.
            let tactic = match &indexed.tactic {
                ProofTactic::SmartFrame(None) => PostExecutionTactic::Frame,
                ProofTactic::SmartFrame(Some(region)) => {
                    PostExecutionTactic::FrameRegion(region.clone())
                }
                tactic => flat_post_execution_tactic(tactic)?,
            };
            Some(DeferredPostExecutionTactic {
                tactic_index: indexed.index,
                source_index: indexed.source_index,
                tactic,
                surface_recorded: false,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    deferred.extend(deferred_post_execution_region(continuation)?);
    Some(deferred)
}

fn deferred_post_execution_region(
    node: &InternalProofNode,
) -> Option<Vec<DeferredPostExecutionTactic>> {
    match node {
        InternalProofNode::Done => Some(Vec::new()),
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => deferred_post_execution_linear_region(tactics, continuation),
        InternalProofNode::If {
            index,
            source_index,
            condition,
            then_branch,
            else_branch,
            continuation,
        } => {
            let mut deferred = vec![DeferredPostExecutionTactic {
                tactic_index: *index,
                source_index: *source_index,
                tactic: PostExecutionTactic::If {
                    condition: condition.clone(),
                    then_tactics: deferred_post_execution_region(then_branch)?,
                    else_tactics: deferred_post_execution_region(else_branch)?,
                },
                surface_recorded: false,
            }];
            deferred.extend(deferred_post_execution_region(continuation)?);
            Some(deferred)
        }
        InternalProofNode::Open { .. } | InternalProofNode::Branch { .. } => None,
    }
}

fn deferred_post_execution_if_is_explicit_path_cursor(
    condition: &ClickProposition,
    then_tactics: &[DeferredPostExecutionTactic],
    else_tactics: &[DeferredPostExecutionTactic],
) -> bool {
    fn explicit_tree(tactics: &[DeferredPostExecutionTactic], depth: usize) -> bool {
        depth < MAX_CHECKED_EXECUTION_REGION_DEPTH
            && tactics.iter().all(|deferred| match &deferred.tactic {
                PostExecutionTactic::Simp => false,
                PostExecutionTactic::If {
                    condition,
                    then_tactics,
                    else_tactics,
                } => {
                    proof_case_is_stable_program_point_condition(condition)
                        && explicit_tree(then_tactics, depth + 1)
                        && explicit_tree(else_tactics, depth + 1)
                }
                _ => true,
            })
    }
    proof_case_is_stable_program_point_condition(condition)
        && explicit_tree(then_tactics, 0)
        && explicit_tree(else_tactics, 0)
}

fn checked_structural_execution_branch_supported(
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
    continuation: &InternalProofNode,
) -> bool {
    (checked_execution_region_pair(then_branch, else_branch).is_some()
        || checked_execution_region_pair_is_mixed(then_branch, else_branch))
        && (!internal_proof_contains_frame(continuation)
            || checked_linear_continuation_reaches_frame(continuation))
}

/// Advances the checked linear prefix following a structural branch. Every
/// accepted explicit or smart operation returns the next Proof directly; the
/// first unsupported tactic and its suffix remain untouched for the
/// compatibility driver. A smart miss rejects the whole candidate path, so
/// the caller can fall back from its unchanged root context.
fn advance_checked_linear_continuation<'a>(
    mut proof: Proof<'a>,
    continuation: &InternalProofNode,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    timing_claim_label: Option<&str>,
) -> Result<Option<(Proof<'a>, Vec<IndexedTactic>)>, ClickError> {
    let Some(tactics) = linear_execution_tactics(continuation) else {
        return decline();
    };
    for (offset, indexed) in tactics.iter().enumerate() {
        if !checked_linear_continuation_tactic(&indexed.tactic) {
            return Ok(Some((proof, tactics[offset..].to_vec())));
        }
        check_verification_deadline()?;
        // Every source driver starts a tactic with an empty step delta.
        proof = proof.start_source_tactic()?;
        let statement_index = proof.execution_frontier_index()?;
        let terminal_frame = matches!(
            indexed.tactic,
            ProofTactic::SmartFrame(_) | ProofTactic::FrameUsing { .. }
        );
        // Once the common execution has returned, proposition and resource
        // operations are interpreted once per concrete outcome. In
        // particular, `result` has no single value on this joined Proof.
        // A function frame is the one audited exception: it checks the typed
        // effect goal across every owned outcome before ordered finalization.
        if proof.is_at_function_exit() && !terminal_frame {
            return Ok(Some((proof, tactics[offset..].to_vec())));
        }
        let _timing = timing_claim_label.and_then(|claim_label| {
            TacticTiming::new(
                claim_label,
                indexed.index,
                indexed.source_index,
                &indexed.tactic,
                statement_index,
            )
        });
        let checkpoint = proof.checkpoint();
        let next = if let Some(step) = linear_execution_proof_step(&indexed.tactic) {
            proof.apply_step_at(step, indexed.index, indexed.source_index)?
        } else if let ProofTactic::ApplyTheorem(application) = &indexed.tactic {
            let Some(applied) = proof.try_theorem_application(application)? else {
                return decline();
            };
            applied
        } else if let ProofTactic::Transport { source, target } = &indexed.tactic {
            let transported = match proof.try_execution_fact_transport(source, target)? {
                Some(transported) => transported,
                None => proof.apply_planned_fact_transport(source, target, indexed.index)?,
            };
            transported
        } else if let ProofTactic::Have(have) = &indexed.tactic {
            let nested = proof.begin_have(have.proposition.clone())?;
            if let Some(selected) = solve_nested_have(nested, have, true)? {
                selected.join()?
            } else {
                // The nested scope declines shapes the shared mid-execution
                // have law still checks; the law is the same one the
                // interpreter used, so there is no second engine behind it.
                proof.apply_mid_execution_have(
                    expansion_capture.as_deref_mut(),
                    have,
                    indexed.index,
                    indexed.source_index,
                )?
            }
        } else if let ProofTactic::ExecuteUntil(region) = &indexed.tactic {
            match proof.try_linear_execute_until(region)? {
                Some(executed) => executed,
                None => proof.apply_planned_execute_until(region, indexed.index)?,
            }
        } else if matches!(
            indexed.tactic,
            ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths
        ) {
            match proof.try_linear_execute()? {
                Some(executed) => executed,
                None => {
                    // The planner fallback constructs the explicit checked
                    // operations through the same law the interpreter used.
                    let force_all_paths =
                        matches!(indexed.tactic, ProofTactic::SmartExecuteAllPaths);
                    // The planner's failure is the answer: it applies the
                    // same statement steps with nothing more to see.
                    proof.apply_planned_smart_execute(force_all_paths, indexed.index)?
                }
            }
        } else if let ProofTactic::Loop(clause) = &indexed.tactic {
            // A frontier-local loop is one checked operation; its expansion
            // capture and surface record are handled inside the operation.
            proof.apply_frontier_local_loop(
                expansion_capture.as_deref_mut(),
                clause,
                indexed.index,
                indexed.source_index,
            )?
        } else if let ProofTactic::SmartFrame(region) = &indexed.tactic {
            let Some(framed) =
                proof.try_smart_frame_at(region.as_ref(), indexed.index, indexed.source_index)?
            else {
                return Err(smart_frame_miss_error(&proof));
            };
            framed
        } else {
            return Ok(Some((proof, tactics[offset..].to_vec())));
        };
        // Observe the source tactic's limit before its timing scope ends, so
        // a completed checked operation cannot hand control to a later tactic
        // after exhausting its own budget.
        check_verification_deadline()?;
        // Generated certificates retain the source index of the smart
        // operation that produced them. Their nested steps are part of that
        // operation's already-recorded branch certificate, not independent
        // expansions of the same source occurrence.
        if indexed.source_index != owning_source_index
            && !matches!(indexed.tactic, ProofTactic::Loop(_))
            && let Some(site) = proof_site
            && selected_tactic_index_for_site(expansion_capture.as_deref(), site)
                == Some(indexed.source_index)
        {
            let certificate = next.certificate_since(&checkpoint)?;
            record_proof_site_tactic_expansion(
                expansion_capture.as_deref_mut(),
                site,
                indexed.source_index,
                &certificate.to_proof_tactics(),
            );
        }
        proof = next;
        // A checked function frame closes the execution-frontier portion of
        // this continuation. Later tactics are ordered outcome operations:
        // in particular, a `have` may name the path-local `result`, which has
        // no single lowering on the joined execution Proof. Return that suffix
        // to the post-execution driver instead of treating it as another
        // execution-frontier transition.
        if terminal_frame {
            return Ok(Some((proof, tactics[offset + 1..].to_vec())));
        }
    }
    Ok(Some((proof, Vec::new())))
}

/// Checks one flat function proof on a single persistent `Proof` lineage.
/// The source shape excludes structural proof branches, resource scopes, and
/// loop regions. Execution operations advance the frontier immediately;
/// result-aware suffix operations are retained only as source-order metadata
/// and are applied to the typed outcome goals during finalization. The exact
/// empty-frame transport segment owns its continuation transactionally, so
/// its smart statement steps may use the indexed selector without exporting a
/// partial descendant; other direct and compatibility callers retain the
/// narrower standalone-step policy.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn try_check_flat_function_proof<'a>(
    execution: &ExecutionProofState,
    pure_facts: &[Proposition],
    constants: &ExecutionProofConstants,
    program: &InternalProofNode,
    generated_by_source_index: Option<usize>,
    expansion_capture: Option<&mut ExpansionCapture>,
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
) -> Result<Option<Proof<'a>>, ClickError> {
    // A retained proof or a terminal error publishes what the driver
    // captured; only a decline (`Ok(None)`) leaves the cursor untouched.
    let mut staged = expansion_capture.as_deref().cloned();
    let result = try_check_flat_function_proof_inner(
        execution,
        pure_facts,
        constants,
        program,
        generated_by_source_index,
        &mut staged,
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
    );
    if !matches!(result, Ok(None))
        && let (Some(expansion_capture), Some(staged)) = (expansion_capture, staged)
    {
        *expansion_capture = staged;
    }
    result
}

#[allow(clippy::too_many_arguments)]
fn try_check_flat_function_proof_inner<'a>(
    execution: &ExecutionProofState,
    pure_facts: &[Proposition],
    constants: &ExecutionProofConstants,
    program: &InternalProofNode,
    generated_by_source_index: Option<usize>,
    staged_expansion_capture: &mut Option<ExpansionCapture>,
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
) -> Result<Option<Proof<'a>>, ClickError> {
    let Some(tactics) = linear_execution_tactics(program) else {
        return decline();
    };
    if tactics.is_empty() {
        return decline();
    }
    let root = Proof::for_execution_frontier(
        claim_label,
        tactics[0].index,
        execution.clone(),
        pure_facts.to_vec(),
        constants.clone(),
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
    let Some((mut proof, remaining)) = advance_checked_linear_continuation(
        root,
        program,
        staged_expansion_capture.as_mut(),
        constants.proof_site.as_ref(),
        generated_by_source_index.unwrap_or(usize::MAX),
        Some(claim_label),
    )?
    else {
        return decline();
    };
    check_verification_deadline()?;
    if !proof.is_at_function_exit() {
        if let Some(error) = remaining
            .first()
            .and_then(|indexed| pre_exit_outcome_tactic_error(&indexed.tactic))
        {
            return Err(error);
        }
        return decline();
    }
    for indexed in remaining {
        check_verification_deadline()?;
        let Some(next) =
            defer_post_exit_outcome_tactic(proof, &indexed, staged_expansion_capture.as_mut())?
        else {
            return decline();
        };
        proof = next;
    }
    Ok(Some(proof))
}

/// Checks one function proof containing supported top-level resource scopes
/// and execution branches without exporting any checked structure back into
/// parallel semantic state. Linear prefixes, structural bodies and joins,
/// intervening continuations, the frame, and the outcome suffix remain one
/// persistent Proof lineage; a miss publishes neither semantic state nor
/// expansion metadata.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn try_check_structural_function_proof<'a>(
    execution: &ExecutionProofState,
    pure_facts: &[Proposition],
    constants: &ExecutionProofConstants,
    program: &InternalProofNode,
    generated_by_source_index: Option<usize>,
    expansion_capture: Option<&mut ExpansionCapture>,
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
) -> Result<Option<Proof<'a>>, ClickError> {
    // A retained proof or a terminal error publishes what the driver
    // captured; only a decline (`Ok(None)`) leaves the cursor untouched.
    let mut staged = expansion_capture.as_deref().cloned();
    let result = try_check_structural_function_proof_inner(
        execution,
        pure_facts,
        constants,
        program,
        generated_by_source_index,
        &mut staged,
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
    );
    if !matches!(result, Ok(None))
        && let (Some(expansion_capture), Some(staged)) = (expansion_capture, staged)
    {
        *expansion_capture = staged;
    }
    result
}

#[allow(clippy::too_many_arguments)]
fn try_check_structural_function_proof_inner<'a>(
    execution: &ExecutionProofState,
    pure_facts: &[Proposition],
    constants: &ExecutionProofConstants,
    program: &InternalProofNode,
    generated_by_source_index: Option<usize>,
    staged_expansion_capture: &mut Option<ExpansionCapture>,
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
) -> Result<Option<Proof<'a>>, ClickError> {
    let proof_site = constants.proof_site.clone();
    let owning_source_index = generated_by_source_index.unwrap_or(usize::MAX);
    let mut proof = Proof::for_execution_frontier(
        claim_label,
        internal_proof_first_index(program).ok_or_else(|| {
            ClickError::new(format!("`{claim_label}` has no structural proof tactics"))
        })?,
        execution.clone(),
        pure_facts.to_vec(),
        constants.clone(),
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
    let mut current = program;
    let mut remaining = Vec::new();
    let mut saw_structure = false;
    loop {
        match current {
            InternalProofNode::Done => break,
            InternalProofNode::Linear {
                tactics,
                continuation,
            } => {
                let linear = InternalProofNode::Linear {
                    tactics: tactics.clone(),
                    continuation: Box::new(InternalProofNode::Done),
                };
                let Some((advanced, unconsumed)) = advance_checked_linear_continuation(
                    proof,
                    &linear,
                    staged_expansion_capture.as_mut(),
                    proof_site.as_ref(),
                    generated_by_source_index.unwrap_or(usize::MAX),
                    Some(claim_label),
                )?
                else {
                    return decline();
                };
                proof = advanced;
                if !unconsumed.is_empty() {
                    if matches!(continuation.as_ref(), InternalProofNode::Done) {
                        remaining = unconsumed;
                        break;
                    }
                    // Post-exit outcome tactics from this linear run precede
                    // more structure (a post-execution `if`). Defer them onto
                    // the exit Proof in order, then process the continuation.
                    for indexed in &unconsumed {
                        let Some(next) = defer_post_exit_outcome_tactic(
                            proof,
                            indexed,
                            staged_expansion_capture.as_mut(),
                        )?
                        else {
                            return decline();
                        };
                        proof = next;
                    }
                    saw_structure = true;
                }
                current = continuation;
            }
            InternalProofNode::Open {
                index,
                source_index,
                resource,
                body,
                continuation,
            } => {
                if proof.is_at_function_exit() {
                    return decline();
                }
                saw_structure = true;
                proof = proof.with_execution_tactic_index(*index)?;
                let scope = proof.begin_open(resource.clone(), *source_index)?;
                let Some(scope) = advance_checked_open_scope(
                    scope,
                    body,
                    staged_expansion_capture.as_mut(),
                    proof_site.as_ref(),
                    owning_source_index,
                )?
                else {
                    return decline();
                };
                proof = scope.join()?;
                current = continuation;
            }
            InternalProofNode::Branch {
                index,
                source_index,
                ensuring,
                then_branch,
                else_branch,
                continuation,
            } => {
                let selected_source_index = proof_site.as_ref().and_then(|site| {
                    selected_tactic_index_for_site(staged_expansion_capture.as_ref(), site)
                });
                let capture_in_continuation = selected_source_index.is_some_and(|wanted| {
                    internal_proof_contains_source_index(continuation, wanted)
                });
                let capture_in_nested_branch = selected_source_index.is_some_and(|wanted| {
                    checked_execution_region_contains_source(then_branch, wanted)
                        || checked_execution_region_contains_source(else_branch, wanted)
                });
                if !selected_source_index.is_none_or(|wanted| {
                    wanted <= *source_index || capture_in_continuation || capture_in_nested_branch
                }) {
                    return decline();
                }
                if !checked_structural_execution_branch_supported(
                    then_branch,
                    else_branch,
                    continuation,
                ) {
                    return decline();
                }
                let Some((advanced, _, certificate, consumed_continuation)) =
                    try_advance_checked_execution_branch(
                        proof,
                        *index,
                        ensuring,
                        then_branch,
                        else_branch,
                        continuation,
                        staged_expansion_capture.as_mut(),
                        proof_site.as_ref(),
                        owning_source_index,
                        0,
                    )?
                else {
                    return decline();
                };
                proof = advanced;
                saw_structure = true;
                if !capture_in_continuation
                    && !capture_in_nested_branch
                    && let Some(site) = proof_site.as_ref()
                {
                    record_proof_site_tactic_expansion(
                        staged_expansion_capture.as_mut(),
                        site,
                        *source_index,
                        &certificate
                            .expect("an expansion request retains the branch certificate")
                            .to_proof_tactics(),
                    );
                }
                current = if consumed_continuation {
                    &InternalProofNode::Done
                } else {
                    continuation
                };
            }
            InternalProofNode::If {
                index,
                source_index,
                condition,
                then_branch,
                else_branch,
                continuation,
                ..
            } => {
                if proof.is_at_function_exit() {
                    let Some(then_tactics) = deferred_post_execution_region(then_branch) else {
                        return decline();
                    };
                    let Some(else_tactics) = deferred_post_execution_region(else_branch) else {
                        return decline();
                    };
                    if !deferred_post_execution_if_is_explicit_path_cursor(
                        condition,
                        &then_tactics,
                        &else_tactics,
                    ) && !proof.post_execution_if_is_path_decided(condition)?
                    {
                        // The condition is a proof-level case split on some
                        // outcome path: fork those paths, one per polarity.
                        match proof.split_outcome_paths_by_case(condition) {
                            Ok(split) => proof = split,
                            Err(_) => {
                                check_verification_deadline()?;
                                return decline();
                            }
                        }
                    }
                    proof = proof.defer_post_execution_source_tactic(
                        *index,
                        *source_index,
                        PostExecutionTactic::If {
                            condition: condition.clone(),
                            then_tactics,
                            else_tactics,
                        },
                        staged_expansion_capture.as_mut(),
                    )?;
                    saw_structure = true;
                    current = continuation;
                    continue;
                }
                proof = proof.with_execution_tactic_index(*index)?;
                if let Some((then_steps, else_steps)) =
                    expanded_execution_if_steps(then_branch, else_branch)
                    && proof.frontier_is_execution_branch(condition)?
                {
                    proof =
                        proof.apply_expanded_execution_if(condition, &then_steps, &else_steps)?;
                    saw_structure = true;
                    current = continuation;
                    continue;
                }
                let arm_steps = match (
                    execution_region_leading_tactic(then_branch),
                    execution_region_leading_tactic(else_branch),
                ) {
                    (Some(then_tactic), Some(else_tactic)) => match (
                        source_successor_if_arm_step(then_tactic),
                        source_successor_if_arm_step(else_tactic),
                    ) {
                        (Some(then_step), Some(else_step)) => Some([then_step, else_step]),
                        _ => None,
                    },
                    _ => None,
                };
                let product = if let Some(arm_steps) = arm_steps.as_ref() {
                    let exact = proof.try_split_source_successor_if(
                        condition,
                        [
                            (arm_steps[0].0, arm_steps[0].1),
                            (arm_steps[1].0, arm_steps[1].1),
                        ],
                    )?;
                    if exact.is_some() {
                        record_source_successor_smart_expansions(
                            arm_steps,
                            staged_expansion_capture.as_mut(),
                            proof_site.as_ref(),
                            owning_source_index,
                        );
                    }
                    exact
                } else {
                    None
                };
                let consumed_leading_steps = product.is_some();
                let (split, record) = if let Some(split) = product {
                    split
                } else {
                    proof.split_focused_execution_if(condition.clone())?
                };
                let mut advanced = split;
                let mut consumed_continuation = false;
                for (take_then, branch) in
                    [(true, then_branch.as_ref()), (false, else_branch.as_ref())]
                {
                    let focused = advanced.focus_execution_if_arm(&record, take_then)?;
                    let next = if consumed_leading_steps {
                        advance_focused_execution_region_after_leading_tactic(
                            focused,
                            None,
                            branch,
                            staged_expansion_capture.as_mut(),
                            proof_site.as_ref(),
                            owning_source_index,
                            1,
                        )?
                    } else {
                        advance_focused_execution_region(
                            focused,
                            None,
                            branch,
                            staged_expansion_capture.as_mut(),
                            proof_site.as_ref(),
                            owning_source_index,
                            1,
                        )?
                    };
                    let Some(mut next) = next else {
                        return decline();
                    };
                    // A proof `if` is a case split: each case is the function
                    // running linearly under one assumed polarity. A case
                    // whose arm ends short of function exit keeps running
                    // through the shared continuation to its own exit; the
                    // cases never rejoin as one state.
                    if !next.is_at_function_exit()
                        && !matches!(continuation.as_ref(), InternalProofNode::Done)
                    {
                        let Some(continued) = advance_focused_execution_region(
                            next,
                            None,
                            continuation,
                            staged_expansion_capture.as_mut(),
                            proof_site.as_ref(),
                            owning_source_index,
                            1,
                        )?
                        else {
                            return decline();
                        };
                        next = continued;
                        consumed_continuation = true;
                    }
                    if !next.is_at_function_exit() {
                        return decline();
                    }
                    advanced = next;
                }
                proof = advanced.join_focused_execution_if_terminal(&record)?;
                saw_structure = true;
                current = if consumed_continuation {
                    &InternalProofNode::Done
                } else {
                    continuation
                };
            }
        }
    }
    check_verification_deadline()?;
    if !proof.is_at_function_exit() {
        if let Some(error) = remaining
            .first()
            .and_then(|indexed| pre_exit_outcome_tactic_error(&indexed.tactic))
        {
            return Err(error);
        }
        return decline();
    }
    if !saw_structure {
        return decline();
    }
    for indexed in remaining {
        check_verification_deadline()?;
        let Some(next) =
            defer_post_exit_outcome_tactic(proof, &indexed, staged_expansion_capture.as_mut())?
        else {
            return decline();
        };
        proof = next;
    }
    Ok(Some(proof))
}

/// The diagnostic for a smart `frame` that found no checked candidate: the
/// frontier must have reached function exit, the claim must own an effect
/// goal, and otherwise the search missed.
fn smart_frame_miss_error(proof: &Proof<'_>) -> ClickError {
    if !proof.is_at_function_exit() {
        return ClickError::new(
            "`frame` requires execution to reach function exit first".to_string(),
        );
    }
    if !proof.frontier_owns_effect_goal() {
        return ClickError::new("`frame` has no effect claim to prove".to_string());
    }
    ClickError::new("`frame` found no checked Proof candidate".to_string())
}

/// Defers one ordered outcome operation, written after the checked
/// execution reached function exit, onto the exit `Proof`. A bare `frame()`
/// is the smart function frame searched here; other outcome tactics are
/// deferred by their post-execution kind. `Ok(None)` declines; `Err` is a
/// terminal diagnostic.
fn defer_post_exit_outcome_tactic<'a>(
    proof: Proof<'a>,
    indexed: &IndexedTactic,
    mut expansion_capture: Option<&mut ExpansionCapture>,
) -> Result<Option<Proof<'a>>, ClickError> {
    if let ProofTactic::SmartFrame(region) = &indexed.tactic {
        let checkpoint = proof.checkpoint();
        let Some(framed) =
            proof.try_smart_frame_at(region.as_ref(), indexed.index, indexed.source_index)?
        else {
            return Err(smart_frame_miss_error(&proof));
        };
        let certificate = framed.certificate_since(&checkpoint)?;
        let (_, deferred) =
            framed.edit_execution(|execution, _| execution.post_execution_tactics.pop())?;
        let Some(mut deferred) = deferred else {
            return decline();
        };
        let PostExecutionTactic::CheckedFrameUsing {
            surface_tactics, ..
        } = &mut deferred.tactic
        else {
            return decline();
        };
        *surface_tactics = Some(certificate.to_proof_tactics());
        deferred.surface_recorded = false;
        let branch_skeleton =
            ProofCertificate::from_steps(surface_branch_skeleton(proof.certificate().steps()))
                .to_proof_tactics();
        let (source_index, tactic_index) = (indexed.source_index, indexed.index);
        let proof_site = proof
            .execution_context()
            .and_then(|context| context.constants.proof_site.clone());
        let mut capture = expansion_capture.as_deref_mut();
        let (framed, _) = proof.edit_execution(|execution, _| {
            if begin_tactic_expansion_capture(
                capture.take(),
                source_index,
                &execution.expansion,
                proof_site.as_ref(),
            ) {
                execution.expansion.deferred_tactic_capture = Some(DeferredTacticCapture {
                    tactic_index,
                    source_index,
                    post_execution_index: execution.post_execution_tactics.len(),
                    branch_skeleton,
                });
            }
            execution.post_execution_tactics.push(deferred);
        })?;
        return Ok(Some(framed));
    }
    if let Some(error) = post_exit_execution_tactic_error(&indexed.tactic) {
        return Err(error);
    }
    let Some(post_tactic) = flat_post_execution_tactic(&indexed.tactic) else {
        return decline();
    };
    Ok(Some(proof.defer_post_execution_source_tactic(
        indexed.index,
        indexed.source_index,
        post_tactic,
        expansion_capture,
    )?))
}

pub(super) fn solve_nested_have<'a>(
    nested: ProofScope<'a>,
    have: &ProofHave,
    authoritative: bool,
) -> Result<Option<ProofScope<'a>>, ClickError> {
    let selected = match &have.proof {
        SourceProof::Default | SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => {
            nested.try_simp_closure()?
        }
        SourceProof::Script(body) => {
            // An explicit script is checked by its proof steps alone: a
            // step that fails is an error, never a miss for search to
            // rescue. A script containing smart tactics may decline to the
            // shared law.
            let nested = nested.with_have_script(body);
            if authoritative && !script_contains_linear_search(body) {
                nested.try_authoritative_linear_script(body)?
            } else {
                nested.try_linear_script(body)?
            }
        }
        SourceProof::Tactic(SmartTactic::Frame) => None,
    };
    // A surface `have` may lower to more than the currently focused
    // proposition goal (for example, a loadability assertion can carry an
    // additional resource obligation). The linear body above advances only
    // its focused goal, while joining requires the entire nested scope to be
    // complete. Treat that unsupported multi-goal shape as a transactional
    // miss so the enclosing checked driver can try another law or report the
    // unsupported shape.
    Ok(selected.filter(ProofScope::is_complete))
}

/// One smart statement step on a preservation-region descendant: the exact
/// Proof selection first, the planner construction second, with the checked
/// certificate delta pushed into the path's surface record. Shared by the
/// preservation driver and the automatic-preservation search.
pub(in crate::lang::click::proof) fn preservation_smart_step<'a>(
    proof: Proof<'a>,
) -> Result<Proof<'a>, ClickError> {
    let advanced = if let Some(stepped) = proof.try_statement_step()? {
        stepped
    } else {
        proof.apply_planned_smart_step(0)?
    };
    Ok(advanced)
}

/// Drives one preservation program region on the typed boundary `Proof`.
/// `pending` is the stack of continuation nodes still owed to the current
/// path, innermost first. Proof-level `if` arms stay separate — a
/// preservation path never rejoins across the back edge — so every leaf
/// reaches the loop's typed boundary and is collected for the caller's
/// per-path bundle, certificate, and effect processing. There is no
/// secondary interpreter: a tactic outside the checked operations is a
/// prompt failure naming the tactic.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn advance_preservation_region<'a>(
    mut proof: Proof<'a>,
    node: &InternalProofNode,
    pending: &[&InternalProofNode],
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    claim_label: &str,
    leaves: &mut Vec<Proof<'a>>,
) -> Result<Proof<'a>, ClickError> {
    check_verification_deadline()?;
    match node {
        InternalProofNode::Done => {
            let Some((next, rest)) = pending.split_first() else {
                if !proof.is_at_region_boundary() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` must execute exactly one complete loop-body iteration"
                    )));
                }
                leaves.push(proof.clone());
                return Ok(proof);
            };
            advance_preservation_region(
                proof,
                next,
                rest,
                expansion_capture,
                proof_site,
                owning_source_index,
                claim_label,
                leaves,
            )
        }
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => {
            for indexed in tactics {
                let handled_by_linear_driver = !matches!(
                    indexed.tactic,
                    ProofTactic::Loop(_) | ProofTactic::Simp | ProofTactic::Step
                );
                if handled_by_linear_driver {
                    let segment = InternalProofNode::Linear {
                        tactics: vec![indexed.clone()],
                        continuation: Box::new(InternalProofNode::Done),
                    };
                    let advanced = advance_checked_linear_continuation(
                        proof.clone(),
                        &segment,
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                        Some(claim_label),
                    )?
                    .filter(|(_, unconsumed)| unconsumed.is_empty());
                    let Some((advanced, _)) = advanced else {
                        // The Proof-native nested scope may decline a `have`
                        // the shared mid-execution law can still check.
                        if let ProofTactic::Have(have) = &indexed.tactic {
                            proof = proof.apply_mid_execution_have(
                                expansion_capture.as_deref_mut(),
                                have,
                                indexed.index,
                                indexed.source_index,
                            )?;
                            continue;
                        }
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {}: `{}` did not verify as a checked preservation operation",
                            indexed.index,
                            tactic_name(&indexed.tactic)
                        )));
                    };
                    proof = advanced;
                    if matches!(indexed.tactic, ProofTactic::CloseInvariants) {
                        proof =
                            proof.record_invariant_closer(indexed.index, indexed.source_index)?;
                    }
                    continue;
                }
                match &indexed.tactic {
                    ProofTactic::Step => {
                        let checkpoint = proof.checkpoint();
                        proof = proof.apply_step(ProofStep::Step)?;
                        if indexed.source_index != owning_source_index
                            && let Some(site) = proof_site
                            && selected_tactic_index_for_site(expansion_capture.as_deref(), site)
                                == Some(indexed.source_index)
                        {
                            let certificate = proof.certificate_since(&checkpoint)?;
                            record_proof_site_tactic_expansion(
                                expansion_capture.as_deref_mut(),
                                site,
                                indexed.source_index,
                                &certificate.to_proof_tactics(),
                            );
                        }
                    }
                    ProofTactic::Loop(clause) => {
                        proof = proof.apply_frontier_local_loop(
                            expansion_capture.as_deref_mut(),
                            clause,
                            indexed.index,
                            indexed.source_index,
                        )?;
                    }
                    ProofTactic::Simp => {
                        // The region simp's semantic content is the bundle
                        // closer certified at the boundary; its capture
                        // completes with that closer.
                        proof = proof.defer_region_simp(indexed.index, indexed.source_index)?;
                    }
                    tactic => {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {}: `{}` is not a checked preservation operation",
                            indexed.index,
                            tactic_name(tactic)
                        )));
                    }
                }
            }
            advance_preservation_region(
                proof,
                continuation,
                pending,
                expansion_capture,
                proof_site,
                owning_source_index,
                claim_label,
                leaves,
            )
        }
        InternalProofNode::If {
            index,
            condition,
            then_branch,
            else_branch,
            continuation,
            ..
        } => {
            let proof = proof.with_execution_tactic_index(*index)?;
            let (split, ids) = proof.split_preservation_case(condition, *index)?;
            let mut arm_pending: Vec<&InternalProofNode> = Vec::with_capacity(pending.len() + 1);
            arm_pending.push(continuation.as_ref());
            arm_pending.extend_from_slice(pending);
            let mut advanced = split;
            for (value, arm) in [(true, then_branch), (false, else_branch)] {
                let Some(id) = ids[usize::from(!value)] else {
                    continue;
                };
                let focused = advanced.focus_branch(id)?;
                advanced = advance_preservation_region(
                    focused,
                    arm,
                    &arm_pending,
                    expansion_capture.as_deref_mut(),
                    proof_site,
                    owning_source_index,
                    claim_label,
                    leaves,
                )?;
            }
            Ok(advanced)
        }
        InternalProofNode::Branch {
            index,
            ensuring,
            then_branch,
            else_branch,
            continuation,
            ..
        } => {
            let proof = proof.with_execution_tactic_index(*index)?;
            let Some((advanced, _, _, consumed_continuation)) =
                try_advance_checked_execution_branch(
                    proof,
                    *index,
                    ensuring,
                    then_branch,
                    else_branch,
                    continuation,
                    expansion_capture.as_deref_mut(),
                    proof_site,
                    owning_source_index,
                    0,
                )?
            else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {index}: `branch` did not verify as a checked preservation operation"
                )));
            };
            advance_preservation_region(
                advanced,
                if consumed_continuation {
                    &InternalProofNode::Done
                } else {
                    continuation
                },
                pending,
                expansion_capture,
                proof_site,
                owning_source_index,
                claim_label,
                leaves,
            )
        }
        InternalProofNode::Open {
            index,
            source_index,
            resource,
            body,
            continuation,
        } => {
            let proof = proof.with_execution_tactic_index(*index)?;
            let scope = proof.begin_open(resource.clone(), *source_index)?;
            let Some(scope) = advance_checked_open_scope(
                scope,
                body,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
            )?
            else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {index}: `open` did not verify as a checked preservation operation"
                )));
            };
            let proof = scope.join()?;
            advance_preservation_region(
                proof,
                continuation,
                pending,
                expansion_capture,
                proof_site,
                owning_source_index,
                claim_label,
                leaves,
            )
        }
    }
}
/// Advances one sibling arm of an in-`Proof` execution split through its
/// linear source tactics, on a proof focused at that arm's recorded goal.
/// Every operation is the ordinary focused `Proof` form; the bounded arm
/// frontier itself refuses source steps past the arm's typed region
/// boundary, so a source `branch` arm must stop at its shared
/// continuation. Only expanded and smart step layers may continue past a
/// boundary, through their own split records.
fn advance_focused_execution_arm<'a>(
    mut proof: Proof<'a>,
    tactics: &[IndexedTactic],
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
) -> Result<Option<Proof<'a>>, ClickError> {
    for indexed in tactics {
        if proof.is_at_function_exit() {
            // A bare `frame()` at an arm's exit is the smart function frame
            // searched on this arm's exit Proof, kept as an ordered deferral
            // like the flat driver's post-exit frame.
            if let ProofTactic::SmartFrame(region) = &indexed.tactic {
                let checkpoint = proof.checkpoint();
                let Some(framed) = proof.try_smart_frame_at(
                    region.as_ref(),
                    indexed.index,
                    indexed.source_index,
                )?
                else {
                    return Err(smart_frame_miss_error(&proof));
                };
                let certificate = framed.certificate_since(&checkpoint)?;
                let (_, deferred) =
                    framed.edit_execution(|execution, _| execution.post_execution_tactics.pop())?;
                let Some(mut deferred) = deferred else {
                    return decline();
                };
                let PostExecutionTactic::CheckedFrameUsing {
                    surface_tactics, ..
                } = &mut deferred.tactic
                else {
                    return decline();
                };
                *surface_tactics = Some(certificate.to_proof_tactics());
                deferred.surface_recorded = false;
                let branch_skeleton = ProofCertificate::from_steps(surface_branch_skeleton(
                    proof.certificate().steps(),
                ))
                .to_proof_tactics();
                let (source_index, tactic_index) = (indexed.source_index, indexed.index);
                let proof_site = proof
                    .execution_context()
                    .and_then(|context| context.constants.proof_site.clone());
                let mut capture = expansion_capture.as_deref_mut();
                let (next, _) = proof.edit_execution(|execution, _| {
                    if begin_tactic_expansion_capture(
                        capture.take(),
                        source_index,
                        &execution.expansion,
                        proof_site.as_ref(),
                    ) {
                        execution.expansion.deferred_tactic_capture = Some(DeferredTacticCapture {
                            tactic_index,
                            source_index,
                            post_execution_index: execution.post_execution_tactics.len(),
                            branch_skeleton,
                        });
                    }
                    execution.post_execution_tactics.push(deferred);
                })?;
                proof = next;
                continue;
            }
            if let Some(error) = post_exit_execution_tactic_error(&indexed.tactic) {
                return Err(error);
            }
            let Some(post_tactic) = flat_post_execution_tactic(&indexed.tactic) else {
                return decline();
            };
            proof = proof.defer_post_execution_source_tactic(
                indexed.index,
                indexed.source_index,
                post_tactic,
                expansion_capture.as_deref_mut(),
            )?;
            continue;
        }
        let checkpoint = proof.checkpoint();
        let next = if let Some(step) = linear_execution_proof_step(&indexed.tactic) {
            proof.apply_step(step)?
        } else if let ProofTactic::ApplyTheorem(application) = &indexed.tactic {
            if proof.is_at_function_exit() {
                // Exit applications need one fixed-state proof per concrete
                // outcome so that `result` lowers correctly; ordered
                // finalization owns that distinct operation.
                return decline();
            }
            let Some(next) = proof.try_theorem_application(application)? else {
                return decline();
            };
            next
        } else if let ProofTactic::Transport { source, target } = &indexed.tactic {
            if proof.is_at_function_exit() {
                return decline();
            }
            let Some(next) = proof.try_execution_fact_transport(source, target)? else {
                return decline();
            };
            next
        } else if let ProofTactic::Have(have) = &indexed.tactic {
            let nested = proof.begin_have(have.proposition.clone())?;
            if let Some(nested) = solve_nested_have(nested, have, true)? {
                nested.join()?
            } else {
                // A structural proof arm has the same mid-execution `have`
                // surface as the flat continuation. The nested Proof scope
                // deliberately handles only its linear subset; route a
                // supported richer script through the shared checked law
                // instead of declining the entire explicit case split.
                proof.apply_mid_execution_have(
                    expansion_capture.as_deref_mut(),
                    have,
                    indexed.index,
                    indexed.source_index,
                )?
            }
        } else if let ProofTactic::Loop(clause) = &indexed.tactic {
            // A frontier-local loop inside a case is one checked operation,
            // exactly as in the linear continuation.
            proof.apply_frontier_local_loop(
                expansion_capture.as_deref_mut(),
                clause,
                indexed.index,
                indexed.source_index,
            )?
        } else if matches!(
            indexed.tactic,
            ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths
        ) {
            let Some(next) = proof.try_focused_execute_to_exit()? else {
                return decline();
            };
            next
        } else {
            return decline();
        };
        check_verification_deadline()?;
        if indexed.source_index != owning_source_index
            && !matches!(indexed.tactic, ProofTactic::Loop(_))
            && let Some(site) = proof_site
            && selected_tactic_index_for_site(expansion_capture.as_deref(), site)
                == Some(indexed.source_index)
        {
            let certificate = next.certificate_since(&checkpoint)?;
            record_proof_site_tactic_expansion(
                expansion_capture.as_deref_mut(),
                site,
                indexed.source_index,
                &certificate.to_proof_tactics(),
            );
        }
        proof = next;
    }
    Ok(Some(proof))
}

fn execution_region_leading_tactic(region: &InternalProofNode) -> Option<&IndexedTactic> {
    let InternalProofNode::Linear { tactics, .. } = region else {
        return None;
    };
    tactics.first()
}

fn source_successor_if_arm_step(indexed: &IndexedTactic) -> Option<(usize, usize, bool)> {
    match &indexed.tactic {
        ProofTactic::Step => Some((indexed.index, indexed.source_index, true)),
        _ => None,
    }
}

fn record_source_successor_smart_expansions(
    arm_steps: &[(usize, usize, bool); 2],
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
) {
    let Some(site) = proof_site else {
        return;
    };
    for (_, source_index, smart) in arm_steps {
        if *smart
            && *source_index != owning_source_index
            && selected_tactic_index_for_site(expansion_capture.as_deref(), site)
                == Some(*source_index)
        {
            let certificate = ProofCertificate::from_steps(vec![ProofStep::Step]);
            record_proof_site_tactic_expansion(
                expansion_capture.as_deref_mut(),
                site,
                *source_index,
                &certificate.to_proof_tactics(),
            );
        }
    }
}

/// Advances a structural source region after its first linear tactic was
/// already consumed by the operation that created the focused Proof arms.
/// The untouched continuation is borrowed directly, so this cursor retains
/// no semantic state and does not clone the proof tree.
#[allow(clippy::too_many_arguments)]
fn advance_focused_execution_region_after_leading_tactic<'a>(
    proof: Proof<'a>,
    enclosing_record: Option<&ExecutionSplit<'a>>,
    region: &InternalProofNode,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    depth: usize,
) -> Result<Option<Proof<'a>>, ClickError> {
    let InternalProofNode::Linear {
        tactics,
        continuation,
    } = region
    else {
        return decline();
    };
    let Some(_) = tactics.first() else {
        return decline();
    };
    let Some(proof) = advance_focused_execution_arm(
        proof,
        &tactics[1..],
        expansion_capture.as_deref_mut(),
        proof_site,
        owning_source_index,
    )?
    else {
        return decline();
    };
    advance_focused_execution_region(
        proof,
        enclosing_record,
        continuation,
        expansion_capture,
        proof_site,
        owning_source_index,
        depth + 1,
    )
}

/// Advances the supported structural grammar of one checked execution arm.
/// Nested branches recurse through the same typed split/arm/join helper; the
/// enclosing split record remains only the checked stop boundary for linear
/// source steps.
fn advance_focused_execution_region<'a>(
    mut proof: Proof<'a>,
    enclosing_record: Option<&ExecutionSplit<'a>>,
    region: &InternalProofNode,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    depth: usize,
) -> Result<Option<Proof<'a>>, ClickError> {
    if depth >= MAX_CHECKED_EXECUTION_REGION_DEPTH {
        return decline();
    }
    match region {
        InternalProofNode::Done => Ok(Some(proof)),
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => {
            let Some(advanced) = advance_focused_execution_arm(
                proof,
                tactics,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
            )?
            else {
                return decline();
            };
            advance_focused_execution_region(
                advanced,
                enclosing_record,
                continuation,
                expansion_capture,
                proof_site,
                owning_source_index,
                depth + 1,
            )
        }
        InternalProofNode::Branch {
            index,
            source_index,
            ensuring,
            then_branch,
            else_branch,
            continuation,
        } => {
            let owner = proof.clone();
            let Some((nested, _, certificate, consumed_continuation)) =
                try_advance_checked_execution_branch(
                    proof,
                    *index,
                    ensuring,
                    then_branch,
                    else_branch,
                    continuation,
                    expansion_capture.as_deref_mut(),
                    proof_site,
                    owning_source_index,
                    depth,
                )?
            else {
                return decline();
            };
            proof = nested.restore_execution_tactic_attribution(&owner)?;
            let selected_source_index = proof_site.as_ref().and_then(|site| {
                selected_tactic_index_for_site(expansion_capture.as_deref(), site)
            });
            if selected_source_index == Some(*source_index)
                && let Some(site) = proof_site
            {
                record_proof_site_tactic_expansion(
                    expansion_capture.as_deref_mut(),
                    site,
                    *source_index,
                    &certificate
                        .expect("an expansion request retains the nested branch certificate")
                        .to_proof_tactics(),
                );
            }
            advance_focused_execution_region(
                proof,
                enclosing_record,
                if consumed_continuation {
                    &InternalProofNode::Done
                } else {
                    continuation
                },
                expansion_capture,
                proof_site,
                owning_source_index,
                depth + 1,
            )
        }
        InternalProofNode::Open {
            index,
            source_index,
            resource,
            body,
            continuation,
        } => {
            let owner = proof.clone();
            let proof = proof.with_execution_tactic_index(*index)?;
            let scope = proof.begin_open(resource.clone(), *source_index)?;
            let Some(scope) = advance_checked_open_scope(
                scope,
                body,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
            )?
            else {
                return decline();
            };
            let proof = scope.join()?.restore_execution_tactic_attribution(&owner)?;
            advance_focused_execution_region(
                proof,
                enclosing_record,
                continuation,
                expansion_capture,
                proof_site,
                owning_source_index,
                depth + 1,
            )
        }
        InternalProofNode::If {
            index,
            source_index,
            condition,
            then_branch,
            else_branch,
            continuation,
            ..
        } => {
            if proof.is_at_function_exit() {
                let Some(then_tactics) = deferred_post_execution_region(then_branch) else {
                    return decline();
                };
                let Some(else_tactics) = deferred_post_execution_region(else_branch) else {
                    return decline();
                };
                if !deferred_post_execution_if_is_explicit_path_cursor(
                    condition,
                    &then_tactics,
                    &else_tactics,
                ) && !proof.post_execution_if_is_path_decided(condition)?
                {
                    // A proof-level case split on some outcome path, as at
                    // the top level: fork those paths, one per polarity.
                    match proof.split_outcome_paths_by_case(condition) {
                        Ok(split) => proof = split,
                        Err(_) => {
                            check_verification_deadline()?;
                            return decline();
                        }
                    }
                }
                let proof = proof.defer_post_execution_source_tactic(
                    *index,
                    *source_index,
                    PostExecutionTactic::If {
                        condition: condition.clone(),
                        then_tactics,
                        else_tactics,
                    },
                    expansion_capture.as_deref_mut(),
                )?;
                return advance_focused_execution_region(
                    proof,
                    enclosing_record,
                    continuation,
                    expansion_capture,
                    proof_site,
                    owning_source_index,
                    depth + 1,
                );
            }
            let owner = proof.clone();
            let proof = proof.with_execution_tactic_index(*index)?;
            let arm_steps = match (
                execution_region_leading_tactic(then_branch),
                execution_region_leading_tactic(else_branch),
            ) {
                (Some(then_tactic), Some(else_tactic)) => match (
                    source_successor_if_arm_step(then_tactic),
                    source_successor_if_arm_step(else_tactic),
                ) {
                    (Some(then_step), Some(else_step)) => Some([then_step, else_step]),
                    _ => None,
                },
                _ => None,
            };
            let product = if let Some(arm_steps) = arm_steps.as_ref() {
                let product = proof.try_split_source_successor_if(
                    condition,
                    [
                        (arm_steps[0].0, arm_steps[0].1),
                        (arm_steps[1].0, arm_steps[1].1),
                    ],
                )?;
                if product.is_some() {
                    record_source_successor_smart_expansions(
                        arm_steps,
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                    );
                }
                product
            } else {
                None
            };
            let consumed_leading_steps = product.is_some();
            let (split, record) = if let Some(split) = product {
                split
            } else {
                proof.split_focused_execution_if(condition.clone())?
            };
            let mut advanced = split;
            let mut consumed_continuation = false;
            for (take_then, branch) in [(true, then_branch.as_ref()), (false, else_branch.as_ref())]
            {
                let focused = advanced.focus_execution_if_arm(&record, take_then)?;
                let next = if consumed_leading_steps {
                    advance_focused_execution_region_after_leading_tactic(
                        focused,
                        enclosing_record,
                        branch,
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                        depth + 1,
                    )?
                } else {
                    advance_focused_execution_region(
                        focused,
                        enclosing_record,
                        branch,
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                        depth + 1,
                    )?
                };
                let Some(mut next) = next else {
                    return decline();
                };
                // Case split, as at the top level: a case whose arm ends
                // short of function exit runs the shared continuation to
                // its own exit.
                if !next.is_at_function_exit()
                    && !matches!(continuation.as_ref(), InternalProofNode::Done)
                {
                    let Some(continued) = advance_focused_execution_region(
                        next,
                        enclosing_record,
                        continuation,
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                        depth + 1,
                    )?
                    else {
                        return decline();
                    };
                    next = continued;
                    consumed_continuation = true;
                }
                if !next.is_at_function_exit() {
                    return decline();
                }
                advanced = next;
            }
            let proof = advanced
                .join_focused_execution_if_terminal(&record)?
                .restore_execution_tactic_attribution(&owner)?;
            advance_focused_execution_region(
                proof,
                enclosing_record,
                if consumed_continuation {
                    &InternalProofNode::Done
                } else {
                    continuation
                },
                expansion_capture,
                proof_site,
                owning_source_index,
                depth + 1,
            )
        }
    }
}

/// Applies one supported two-arm execution branch entirely through the typed
/// Proof split/join API. Callers may choose different source-driving
/// boundaries, but branch entry, arm advancement, interface checking, and the
/// semantic join have one implementation.
/// The fourth result reports that the branch's continuation was consumed:
/// one arm returned and the other ran the continuation to function exit
/// inside the arm, so the caller must not run the continuation again.
fn try_advance_checked_execution_branch<'a>(
    proof: Proof<'a>,
    tactic_index: usize,
    ensuring: &Option<Vec<ProofAssertion>>,
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
    continuation: &InternalProofNode,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    depth: usize,
) -> Result<Option<(Proof<'a>, bool, Option<ProofCertificate>, bool)>, ClickError> {
    if depth >= MAX_CHECKED_EXECUTION_REGION_DEPTH {
        return decline();
    }
    let proof = proof.with_execution_tactic_index(tactic_index)?;
    let checkpoint = proof.checkpoint();
    let (split, record) = proof.split_focused_execution_branch()?;
    let has_sole_feasible_arm = record.sole_feasible_arm().is_some();
    let Some(arms) = advance_checked_branch_arms(
        split,
        &record,
        ensuring,
        then_branch,
        else_branch,
        continuation,
        expansion_capture.as_deref_mut(),
        proof_site,
        owning_source_index,
        depth,
    )?
    else {
        return decline();
    };
    let joined =
        arms.advanced
            .join_focused_execution_split(&record, arms.empty, arms.join_interface)?;
    let certificate = proof_site
        .is_some()
        .then(|| joined.certificate_since(&checkpoint))
        .transpose()?;
    Ok(Some((
        joined,
        has_sole_feasible_arm,
        certificate,
        arms.consumed_continuation,
    )))
}

/// The result of advancing a branch's two arms, ready for the caller to join
/// on its own target (`Proof` or `ProofScope`).
struct AdvancedBranchArms<'a> {
    advanced: Proof<'a>,
    consumed_continuation: bool,
    empty: bool,
    join_interface: Option<Vec<ProofAssertion>>,
}

/// The single branch arm-advancing law, shared by the `Proof` branch driver
/// and the open-scope branch handler: it advances both feasible arms, runs
/// the shared continuation inside a continuing arm when the arms end
/// differently (checking any `ensuring` interface there), and reports whether
/// the continuation was consumed. The caller splits and joins on its own
/// target; only the arm interiors, which are always `Proof`s, live here.
#[allow(clippy::too_many_arguments)]
fn advance_checked_branch_arms<'a>(
    split: Proof<'a>,
    record: &ExecutionSplit<'a>,
    ensuring: &Option<Vec<ProofAssertion>>,
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
    continuation: &InternalProofNode,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    depth: usize,
) -> Result<Option<AdvancedBranchArms<'a>>, ClickError> {
    if ensuring
        .as_ref()
        .is_some_and(|_| !record.supports_interface_branch())
    {
        return decline();
    }
    let has_sole_feasible_arm = record.sole_feasible_arm().is_some();
    let mut advanced = split;
    for (take_then, region) in [(true, then_branch), (false, else_branch)] {
        if record.arm_id(take_then).is_none() {
            continue;
        }
        let Some(next) = advance_focused_execution_region(
            advanced.focus_split_arm(record, take_then)?,
            Some(record),
            region,
            expansion_capture.as_deref_mut(),
            proof_site,
            owning_source_index,
            depth + 1,
        )?
        else {
            return decline();
        };
        advanced = next;
    }
    let mut consumed_continuation = false;
    if !has_sole_feasible_arm {
        let then_exit = advanced.arm_at_function_exit(record, true);
        let else_exit = advanced.arm_at_function_exit(record, false);
        if then_exit != else_exit {
            // One arm returned. The other continues past its boundary into
            // the shared continuation, which it runs to function exit; the
            // two arms then join terminally. An `ensuring` interface is
            // checked on the continuing arm at its boundary; the retained
            // state is the arm's own, which is stronger than the interface.
            let continuing = advanced.focus_split_arm(record, !then_exit)?;
            if let Some(assertions) = ensuring
                && !continuing.interface_facts_established(assertions)?
            {
                return decline();
            }
            let continuing = continuing.continue_arm_into_parent_frontier(record)?;
            let Some(next) = advance_focused_execution_region(
                continuing,
                Some(record),
                continuation,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
                depth + 1,
            )?
            else {
                return decline();
            };
            if !next.is_at_function_exit() {
                return decline();
            }
            advanced = next;
            consumed_continuation = true;
        }
    }
    let empty = checked_execution_region_is_empty(then_branch)
        && checked_execution_region_is_empty(else_branch);
    let join_interface = if consumed_continuation {
        None
    } else {
        ensuring.clone()
    };
    Ok(Some(AdvancedBranchArms {
        advanced,
        consumed_continuation,
        empty,
        join_interface,
    }))
}

fn linear_execution_steps(node: &InternalProofNode) -> Option<Vec<ProofStep>> {
    linear_execution_tactics(node)?
        .iter()
        .map(|indexed| arm_proof_step(&indexed.tactic))
        .collect()
}

fn expanded_execution_if_steps(
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
) -> Option<(Vec<ProofStep>, Vec<ProofStep>)> {
    let then_steps = linear_execution_steps(then_branch)?;
    let else_steps = linear_execution_steps(else_branch)?;
    (expanded_execution_arm_supported(&then_steps)
        && expanded_execution_arm_supported(&else_steps)
        && !(then_steps.is_empty() && else_steps.is_empty()))
    .then_some((then_steps, else_steps))
}
/// Advances a linear resource scope one checked node at a time. A nested
/// `have` is joined back through the scope API, so its selected theorem steps
/// and its published proposition are retained by the same immutable proof.
fn advance_linear_open_scope<'a>(
    mut scope: ProofScope<'a>,
    tactics: &[IndexedTactic],
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
) -> Result<Option<ProofScope<'a>>, ClickError> {
    for indexed in tactics {
        if let Some(step) = linear_execution_proof_step(&indexed.tactic) {
            scope = if let ProofStep::FrameUsing { region, premises } = &step {
                if scope.is_at_function_exit()
                    && !scope.supports_checked_frame_using(region.as_ref(), premises)?
                {
                    // Execution inside the scope reached function exit and
                    // this frame is not checkable here: defer it through the
                    // scope to finalization, as the arm walker defers a
                    // post-exit outcome tactic on a `Proof`.
                    let Some(post_tactic) = flat_post_execution_tactic(&indexed.tactic) else {
                        return decline();
                    };
                    scope = scope.defer_post_execution_source_tactic(
                        indexed.index,
                        indexed.source_index,
                        post_tactic,
                        expansion_capture.as_deref_mut(),
                    )?;
                    continue;
                }
                scope.apply_step_at(step, indexed.index, indexed.source_index)?
            } else {
                scope.apply_step(step)?
            };
            continue;
        }
        if let ProofTactic::ApplyTheorem(application) = &indexed.tactic {
            let checkpoint = scope.checkpoint();
            let Some(applied) = scope.try_theorem_application(application)? else {
                return decline();
            };
            scope = applied;
            if indexed.source_index != owning_source_index
                && let Some(site) = proof_site
            {
                let certificate = scope.certificate_since(&checkpoint)?;
                record_proof_site_tactic_expansion(
                    expansion_capture.as_deref_mut(),
                    site,
                    indexed.source_index,
                    &certificate.to_proof_tactics(),
                );
            }
            continue;
        }
        if let ProofTactic::Transport { source, target } = &indexed.tactic {
            let checkpoint = scope.checkpoint();
            let Some(transported) = scope.try_fact_transport(source, target)? else {
                return decline();
            };
            scope = transported;
            if indexed.source_index != owning_source_index
                && let Some(site) = proof_site
            {
                let certificate = scope.certificate_since(&checkpoint)?;
                record_proof_site_tactic_expansion(
                    expansion_capture.as_deref_mut(),
                    site,
                    indexed.source_index,
                    &certificate.to_proof_tactics(),
                );
            }
            continue;
        }
        if matches!(
            indexed.tactic,
            ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths
        ) {
            let checkpoint = scope.checkpoint();
            let Some(executed) = scope.try_linear_execute()? else {
                return decline();
            };
            scope = executed;
            if indexed.source_index != owning_source_index
                && let Some(site) = proof_site
            {
                let certificate = scope.certificate_since(&checkpoint)?;
                record_proof_site_tactic_expansion(
                    expansion_capture.as_deref_mut(),
                    site,
                    indexed.source_index,
                    &certificate.to_proof_tactics(),
                );
            }
            continue;
        }
        if let ProofTactic::SmartFrame(region) = &indexed.tactic {
            let checkpoint = scope.checkpoint();
            let Some(framed) =
                scope.try_smart_frame_at(region.as_ref(), indexed.index, indexed.source_index)?
            else {
                return Err(if scope.is_at_function_exit() {
                    ClickError::new("`frame` found no checked Proof candidate".to_string())
                } else {
                    ClickError::new(
                        "`frame` requires execution to reach function exit first".to_string(),
                    )
                });
            };
            scope = framed;
            if indexed.source_index != owning_source_index
                && let Some(site) = proof_site
            {
                let certificate = scope.certificate_since(&checkpoint)?;
                record_proof_site_tactic_expansion(
                    expansion_capture.as_deref_mut(),
                    site,
                    indexed.source_index,
                    &certificate.to_proof_tactics(),
                );
            }
            continue;
        }
        if let ProofTactic::ExecuteUntil(region) = &indexed.tactic {
            let checkpoint = scope.checkpoint();
            let Some(executed) = scope.try_linear_execute_until(region)? else {
                return decline();
            };
            scope = executed;
            if indexed.source_index != owning_source_index
                && let Some(site) = proof_site
            {
                let certificate = scope.certificate_since(&checkpoint)?;
                record_proof_site_tactic_expansion(
                    expansion_capture.as_deref_mut(),
                    site,
                    indexed.source_index,
                    &certificate.to_proof_tactics(),
                );
            }
            continue;
        }
        // After execution reached function exit inside the scope, an ordered
        // outcome operation (`simp`, `fold`, a `have` naming `result`, ...)
        // is deferred on the scope body and follows the scope's join.
        if scope.is_at_function_exit()
            && !matches!(indexed.tactic, ProofTactic::Have(_))
            && let Some(post_tactic) = flat_post_execution_tactic(&indexed.tactic)
        {
            scope = scope.defer_post_execution_source_tactic(
                indexed.index,
                indexed.source_index,
                post_tactic,
                expansion_capture.as_deref_mut(),
            )?;
            continue;
        }
        let ProofTactic::Have(have) = &indexed.tactic else {
            return decline();
        };
        let nested = scope.begin_have(have.proposition.clone())?;
        let selected = solve_nested_have(nested, have, false)?;
        let Some(selected) = selected else {
            return decline();
        };
        scope = scope.join_nested(selected)?;
    }
    Ok(Some(scope))
}

fn advance_checked_open_scope<'a>(
    scope: ProofScope<'a>,
    body: &InternalProofNode,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
) -> Result<Option<ProofScope<'a>>, ClickError> {
    if matches!(body, InternalProofNode::Done) {
        return Ok(Some(scope));
    }
    if let Some(tactics) = linear_execution_tactics(body) {
        return advance_linear_open_scope(
            scope,
            tactics,
            expansion_capture,
            proof_site,
            owning_source_index,
        );
    }
    if let InternalProofNode::Linear {
        tactics,
        continuation,
    } = body
    {
        let Some(scope) = advance_linear_open_scope(
            scope,
            tactics,
            expansion_capture.as_deref_mut(),
            proof_site,
            owning_source_index,
        )?
        else {
            return decline();
        };
        return advance_checked_open_scope(
            scope,
            continuation,
            expansion_capture,
            proof_site,
            owning_source_index,
        );
    }
    if let InternalProofNode::Open {
        index,
        source_index,
        resource,
        body: nested_body,
        continuation,
    } = body
    {
        let scope = scope.with_execution_tactic_index(*index)?;
        let nested = scope.begin_open(resource.clone(), *source_index)?;
        let Some(nested) = advance_checked_open_scope(
            nested,
            nested_body,
            expansion_capture.as_deref_mut(),
            proof_site,
            owning_source_index,
        )?
        else {
            return decline();
        };
        let scope = scope.join_nested(nested)?;
        return advance_checked_open_scope(
            scope,
            continuation,
            expansion_capture,
            proof_site,
            owning_source_index,
        );
    }
    if let InternalProofNode::If {
        condition,
        then_branch,
        else_branch,
        continuation,
        ..
    } = body
        && let Some((then_steps, else_steps)) =
            expanded_execution_if_steps(then_branch, else_branch)
        && scope.frontier_is_execution_branch(condition)?
    {
        let scope = scope.apply_expanded_execution_if(condition, &then_steps, &else_steps)?;
        return advance_checked_open_scope(
            scope,
            continuation,
            expansion_capture,
            proof_site,
            owning_source_index,
        );
    }
    if let InternalProofNode::If {
        index,
        source_index,
        condition,
        then_branch,
        else_branch,
        continuation,
    } = body
        && let Some(then_tactics) = linear_execution_tactics(then_branch)
        && let Some(else_tactics) = linear_execution_tactics(else_branch)
        && matches!(
            then_tactics.last().map(|indexed| &indexed.tactic),
            Some(ProofTactic::FrameUsing { region: None, .. })
        )
        && matches!(
            else_tactics.last().map(|indexed| &indexed.tactic),
            Some(ProofTactic::FrameUsing { region: None, .. })
        )
    {
        let Some(scope) = scope.apply_contextual_frame_tactics_at(
            condition.clone(),
            then_tactics
                .iter()
                .map(|indexed| indexed.tactic.clone())
                .collect(),
            else_tactics
                .iter()
                .map(|indexed| indexed.tactic.clone())
                .collect(),
            *index,
            *source_index,
        )?
        else {
            return decline();
        };
        return advance_checked_open_scope(
            scope,
            continuation,
            expansion_capture,
            proof_site,
            owning_source_index,
        );
    }
    if let InternalProofNode::If {
        index,
        condition,
        then_branch,
        else_branch,
        continuation,
        ..
    } = body
    {
        // A proof `if` inside a resource scope is the same case split as
        // outside one: each case runs its arm and then the shared
        // continuation to its own function exit, and the cases join
        // terminally as the scope's next node.
        let scope = scope.with_execution_tactic_index(*index)?;
        let (split, record) = scope.split_execution_if(condition.clone())?;
        let mut advanced = split;
        let mut consumed_continuation = false;
        for (take_then, branch) in [(true, then_branch.as_ref()), (false, else_branch.as_ref())] {
            let focused = advanced.focus_execution_if_arm(&record, take_then)?;
            let Some(mut next) = advance_focused_execution_region(
                focused,
                None,
                branch,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
                1,
            )?
            else {
                return decline();
            };
            if !next.is_at_function_exit()
                && !matches!(continuation.as_ref(), InternalProofNode::Done)
            {
                let Some(continued) = advance_focused_execution_region(
                    next,
                    None,
                    continuation,
                    expansion_capture.as_deref_mut(),
                    proof_site,
                    owning_source_index,
                    1,
                )?
                else {
                    return decline();
                };
                next = continued;
                consumed_continuation = true;
            }
            if !next.is_at_function_exit() {
                return decline();
            }
            advanced = next;
        }
        let scope = scope.join_execution_if_terminal(&advanced, &record)?;
        return advance_checked_open_scope(
            scope,
            if consumed_continuation {
                &InternalProofNode::Done
            } else {
                continuation
            },
            expansion_capture,
            proof_site,
            owning_source_index,
        );
    }
    let InternalProofNode::Branch {
        ensuring,
        then_branch,
        else_branch,
        continuation,
        ..
    } = body
    else {
        return decline();
    };
    let (split, record) = scope.split_execution_branch()?;
    let Some(arms) = advance_checked_branch_arms(
        split,
        &record,
        ensuring,
        then_branch,
        else_branch,
        continuation,
        expansion_capture.as_deref_mut(),
        proof_site,
        owning_source_index,
        0,
    )?
    else {
        return decline();
    };
    let scope =
        scope.join_execution_split(&arms.advanced, &record, arms.empty, arms.join_interface)?;
    advance_checked_open_scope(
        scope,
        if arms.consumed_continuation {
            &InternalProofNode::Done
        } else {
            continuation
        },
        expansion_capture,
        proof_site,
        owning_source_index,
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn introduce_proof_case_assumption(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    pure_facts: &mut Vec<Proposition>,
    structured_branch_history: bool,
    condition: &ClickProposition,
    value: bool,
) -> Result<bool, ClickError> {
    let tactic_index = proof_context.tactic_index;
    let parameters = proof_context.parsed_function.parameters();
    let arguments = proof_context.arguments;
    let predicate_environment = proof_context.predicate_environment;
    let click_function_environment = proof_context.click_function_environment;
    let claim_label = proof_context.claim_label;

    if execution.loop_effect_goal.is_some() {
        // A structural-effect validation path may already own the exact C-branch
        // fact under this Surface spelling. Prefer that unambiguous indexed
        // identity to rereading the condition from the heap. Ordinary loop
        // preservation must lower afresh because the same spelling can name
        // the next iteration's new condition variables.
        let positive_surface = condition.clone();
        let negative_surface = negate_click_proposition(condition);
        let positive = execution
            .surface_propositions
            .available_kernel_matching(&positive_surface, |kernel| pure_facts.contains(kernel))
            .cloned();
        let negative = execution
            .surface_propositions
            .available_kernel_matching(&negative_surface, |kernel| pure_facts.contains(kernel))
            .cloned();
        if positive.is_some() != negative.is_some() {
            let recorded_value = positive.is_some();
            if value != recorded_value {
                return Ok(false);
            }
            let kernel_fact = positive.or(negative).expect("one recorded polarity exists");
            let surface_fact = if value {
                positive_surface
            } else {
                negative_surface
            };
            execution
                .surface_propositions
                .record_lowering(&surface_fact, &kernel_fact)?;
            execution.case_assumptions.push(CaseAssumption {
                tactic_index,
                condition: condition.clone(),
                value,
                fact: Some(kernel_fact),
                at_function_entry: execution.frontier.is_at_function_entry(),
            });
            return Ok(true);
        }
    }
    if execution.frontier.is_at_function_exit()
        && structured_branch_history
        && proof_case_is_stable_program_point_condition(condition)
    {
        // A source-qualified condition can still be lowered without choosing
        // one return outcome. Use it immediately when possible so a logical
        // certificate nested under an already selected C path does not
        // manufacture its contradictory sibling at function exit. Conditions
        // involving `result` or the post-state retain the deferred per-outcome
        // handling below.
        if let Ok(proposition) = lower_fixed_state_proposition(
            condition,
            pure_facts,
            parameters,
            arguments,
            proof_context.old_reference_state(&execution.frontier, &execution.state),
            &execution.state,
            None,
            &execution.recorded_snapshots,
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
            if pure_facts
                .iter()
                .any(|available| propositions_are_exact_negations(available, &kernel_fact))
            {
                return Ok(false);
            }
            execution
                .surface_propositions
                .record_lowering(&surface_fact, &kernel_fact)?;
            pure_facts.push(kernel_fact.clone());
            execution.case_assumptions.push(CaseAssumption {
                tactic_index,
                condition: condition.clone(),
                value,
                fact: Some(kernel_fact),
                at_function_entry: false,
            });
            return Ok(true);
        }
    }
    if execution.frontier.is_at_function_exit() {
        execution.case_assumptions.push(CaseAssumption {
            tactic_index,
            condition: condition.clone(),
            value,
            fact: None,
            at_function_entry: false,
        });
        return Ok(true);
    }
    let at_function_entry = execution.frontier.is_at_function_entry();
    let proposition = lower_fixed_state_proposition(
        condition,
        pure_facts,
        parameters,
        arguments,
        proof_context.old_reference_state(&execution.frontier, &execution.state),
        &execution.state,
        None,
        &execution.recorded_snapshots,
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
    if pure_facts
        .iter()
        .any(|available| propositions_are_exact_negations(available, &kernel_fact))
    {
        return Ok(false);
    }
    execution
        .surface_propositions
        .record_lowering(&surface_fact, &kernel_fact)?;
    pure_facts.push(kernel_fact.clone());
    execution.case_assumptions.push(CaseAssumption {
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
            ContractExpression::At { .. } | ContractExpression::Old(_)
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
            ClickProposition::At { .. } => true,
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

/// The diagnostic for an execution tactic written after execution already
/// reached function exit: the tactic has no statement to run.
fn post_exit_execution_tactic_error(tactic: &ProofTactic) -> Option<ClickError> {
    let name = match tactic {
        ProofTactic::Step => "step()".to_string(),
        ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths => "execute()".to_string(),
        ProofTactic::ExecuteUntil(region) => format!(
            "execute_until({})",
            crate::lang::click::diagnostics::describe_code_region_ref(region)
        ),
        _ => return None,
    };
    Some(ClickError::new(format!(
        "`{name}` cannot run after execution already reached function exit"
    )))
}

/// The diagnostic for a function-exit tactic written before execution
/// reached function exit.
fn pre_exit_outcome_tactic_error(tactic: &ProofTactic) -> Option<ClickError> {
    let name = match tactic {
        ProofTactic::Witness(_) => "witness",
        ProofTactic::Choose(_) => "choose",
        ProofTactic::Simp => "simp",
        ProofTactic::SmartFrame(_) | ProofTactic::FrameUsing { .. } => "frame",
        _ => return None,
    };
    Some(ClickError::new(format!(
        "`{name}` requires execution to reach function exit first"
    )))
}
