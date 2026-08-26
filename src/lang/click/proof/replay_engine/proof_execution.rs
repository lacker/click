use super::*;

#[cfg(test)]
thread_local! {
    static INTERNAL_PROOF_EXECUTIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static ROOT_INTERNAL_PROOF_EXECUTIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static COLLECTED_INTERNAL_PROOF_LABELS: std::cell::RefCell<Option<Vec<String>>> = const {
        std::cell::RefCell::new(None)
    };
}

#[cfg(test)]
pub(in crate::lang::click) fn count_root_internal_proof_executions<R>(
    operation: impl FnOnce() -> R,
) -> (R, usize) {
    let before = ROOT_INTERNAL_PROOF_EXECUTIONS.with(std::cell::Cell::get);
    let result = operation();
    let after = ROOT_INTERNAL_PROOF_EXECUTIONS.with(std::cell::Cell::get);
    (result, after - before)
}

#[cfg(test)]
pub(in crate::lang::click) fn count_internal_proof_executions<R>(
    operation: impl FnOnce() -> R,
) -> (R, usize) {
    let before = INTERNAL_PROOF_EXECUTIONS.with(std::cell::Cell::get);
    let result = operation();
    let after = INTERNAL_PROOF_EXECUTIONS.with(std::cell::Cell::get);
    (result, after - before)
}

#[cfg(test)]
pub(in crate::lang::click) fn collect_internal_proof_execution_labels<R>(
    operation: impl FnOnce() -> R,
) -> (R, Vec<String>) {
    COLLECTED_INTERNAL_PROOF_LABELS.with(|labels| {
        assert!(
            labels.borrow().is_none(),
            "internal-proof label collectors cannot nest"
        );
        *labels.borrow_mut() = Some(Vec::new());
    });
    let result = operation();
    let labels = COLLECTED_INTERNAL_PROOF_LABELS.with(|labels| {
        labels
            .borrow_mut()
            .take()
            .expect("the active internal-proof label collector was retained")
    });
    (result, labels)
}

/// A simple step written in an execution arm. A source `step()` is the bare
/// statement step; the other simple statement forms map as themselves.
fn arm_simple_step(tactic: &ProofTactic) -> Option<SimpleProofStep> {
    match tactic {
        ProofTactic::SmartStep => Some(SimpleProofStep::Step),
        tactic => linear_execution_simple_step(tactic),
    }
}

fn linear_execution_simple_step(tactic: &ProofTactic) -> Option<SimpleProofStep> {
    match tactic {
        ProofTactic::Mark(name) => Some(SimpleProofStep::Mark(name.clone())),
        ProofTactic::Step => Some(SimpleProofStep::Step),
        ProofTactic::StepUsing(premises) => Some(SimpleProofStep::StepUsing(premises.clone())),
        ProofTactic::TransportUsing {
            source,
            target,
            premises,
        } => Some(SimpleProofStep::TransportUsing {
            source: source.clone(),
            target: target.clone(),
            premises: premises.clone(),
        }),
        ProofTactic::UnfoldPredicate(name) => Some(SimpleProofStep::UnfoldPredicate(name.clone())),
        ProofTactic::UnfoldResource(resource) => {
            Some(SimpleProofStep::UnfoldResource(resource.clone()))
        }
        ProofTactic::FoldResource(resource) => {
            Some(SimpleProofStep::FoldResource(resource.clone()))
        }
        ProofTactic::ObserveResource(resource) => {
            Some(SimpleProofStep::ObserveResource(resource.clone()))
        }
        ProofTactic::ApplyTheoremUsing {
            application,
            premises,
        } => Some(SimpleProofStep::ApplyTheoremUsing {
            application: application.clone(),
            premises: premises.clone(),
        }),
        ProofTactic::FrameUsing { region, premises } => Some(SimpleProofStep::FrameUsing {
            region: region.clone(),
            premises: premises.clone(),
        }),
        ProofTactic::CloseInvariants => Some(SimpleProofStep::CloseInvariants),
        _ => None,
    }
}

fn expanded_execution_arm_supported(
    condition: &ClickProposition,
    take_then: bool,
    steps: &[SimpleProofStep],
) -> bool {
    if steps.is_empty() {
        return true;
    }
    let expected = if take_then {
        condition.clone()
    } else {
        negate_click_proposition(condition)
    };
    // An empty entry-premise list is still the surface shape of this checked
    // operation: admit it so `Proof` reports the missing branch anchor instead
    // of silently dropping to compatibility replay. A nonempty, different
    // premise belongs to an older certificate shape and remains unsupported.
    let entry_supported = match steps.first() {
        Some(SimpleProofStep::Step) => true,
        Some(SimpleProofStep::StepUsing(premises)) => {
            premises.is_empty() || premises.as_slice() == std::slice::from_ref(&expected)
        }
        _ => false,
    };
    entry_supported
        && matches!(
            steps.last(),
            Some(SimpleProofStep::StepUsing(_) | SimpleProofStep::Step)
        )
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
        if matches!(indexed.tactic, ProofTactic::SmartStep) {
            may_exit = true;
            continue;
        }
        if linear_execution_simple_step(&indexed.tactic).is_none()
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
    linear_execution_simple_step(tactic).is_some()
        || matches!(
            tactic,
            ProofTactic::SmartStep
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
    allow_unrelated_statement_context: bool,
    allow_contextual_frame: bool,
    authoritative_nested_haves: bool,
    timing_claim_label: Option<&str>,
) -> Result<Option<(Proof<'a>, Vec<IndexedTactic>)>, ClickError> {
    let Some(tactics) = linear_execution_tactics(continuation) else {
        return Ok(None);
    };
    for (offset, indexed) in tactics.iter().enumerate() {
        if !checked_linear_continuation_tactic(&indexed.tactic) {
            return Ok(Some((proof, tactics[offset..].to_vec())));
        }
        check_verification_deadline()?;
        // Every source driver starts a tactic with an empty step delta.
        proof = proof.start_source_tactic()?;
        let statement_index = proof
            .finalization_view()?
            .replay
            .frontier
            .next_statement_index;
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
        let next = if let Some(step) = linear_execution_simple_step(&indexed.tactic) {
            if let SimpleProofStep::FrameUsing { region, premises } = &step
                && !authoritative_nested_haves
                && !proof.supports_checked_frame_using(region.as_ref(), premises)?
            {
                return Ok(None);
            }
            proof.apply_step_at(step, indexed.index, indexed.source_index)?
        } else if matches!(indexed.tactic, ProofTactic::SmartStep) {
            // A complete top-level resource scope owns its linear suffix, so
            // statement selection may retain unrelated resources and facts
            // just as it does inside the scope. Flat partial migration keeps
            // the narrower standalone-step policy until its continuation is
            // owned transactionally too.
            let stepped = if allow_unrelated_statement_context {
                proof.try_indexed_execute_step()?
            } else {
                proof.try_smart_step()?
            };
            match stepped {
                Some(stepped) => stepped,
                // The planner fallback constructs the explicit checked
                // operations through the same law the interpreter used.
                // While the compatibility interpreter still exists, its
                // failures stay a decline so routing does not change; the
                // fallback deletion makes them terminal, as they were in
                // the interpreter itself.
                None => match proof.apply_planned_smart_step(indexed.index) {
                    Ok(stepped) => stepped,
                    Err(_) => return Ok(None),
                },
            }
        } else if let ProofTactic::ApplyTheorem(application) = &indexed.tactic {
            let Some(applied) = proof.try_theorem_application(application)? else {
                return Ok(None);
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
            // Partial continuation migration keeps the audited exact-frame
            // subset. A complete transactional effect script may also search
            // for contextual premises because a miss discards the whole
            // Proof lineage instead of publishing its execution prefix.
            if !allow_contextual_frame
                && !proof.supports_checked_frame_using(region.as_ref(), &[])?
            {
                return Ok(None);
            }
            let Some(framed) =
                proof.try_smart_frame_at(region.as_ref(), indexed.index, indexed.source_index)?
            else {
                return Ok(None);
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
    context: &ProofReplayContext,
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
    complete_grouped_authority: bool,
    allow_indexed_smart_step: bool,
) -> Result<Option<Proof<'a>>, ClickError> {
    // A compatibility miss must leave the expansion cursor untouched just as
    // it leaves the semantic root untouched. Only publish cursor metadata
    // after the complete flat proof has been retained successfully.
    let mut staged_expansion_capture = expansion_capture.as_deref().cloned();
    let Some(tactics) = linear_execution_tactics(program) else {
        return Ok(None);
    };
    if tactics.is_empty() {
        return Ok(None);
    }
    let root = Proof::for_execution_frontier(
        claim_label,
        tactics[0].index,
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
    let Some((mut proof, remaining)) = advance_checked_linear_continuation(
        root,
        program,
        staged_expansion_capture.as_mut(),
        context.replay.proof_site.as_ref(),
        generated_by_source_index.unwrap_or(usize::MAX),
        allow_indexed_smart_step,
        true,
        complete_grouped_authority,
        Some(claim_label),
    )?
    else {
        return Ok(None);
    };
    check_verification_deadline()?;
    if !proof.is_at_function_exit() {
        if let Some(error) = remaining
            .first()
            .and_then(|indexed| pre_exit_outcome_tactic_error(&indexed.tactic))
        {
            return Err(error);
        }
        return Ok(None);
    }
    for indexed in remaining {
        check_verification_deadline()?;
        // A bare `frame()` among the ordered outcome operations is the
        // smart function frame searched on the exit Proof now, as the
        // linear continuation does for a frame that arrives first.
        if let ProofTactic::SmartFrame(region) = &indexed.tactic {
            let checkpoint = proof.checkpoint();
            let Some(framed) =
                proof.try_smart_frame_at(region.as_ref(), indexed.index, indexed.source_index)?
            else {
                return Ok(None);
            };
            // The function frame at exit retains an ordered deferral whose
            // authority finalization applies. Keep that deferral, printing
            // the checked contribution at its source position after the
            // outcome operations deferred before it, on the unframed Proof:
            // the frame step itself would otherwise precede them in the
            // retained certificate.
            let certificate = framed.certificate_since(&checkpoint)?;
            let (_, deferred) =
                framed.edit_replay_cursor(|replay, _, _| replay.post_execution_tactics.pop())?;
            let Some(mut deferred) = deferred else {
                return Ok(None);
            };
            let PostExecutionTactic::CheckedFrameUsing {
                surface_tactics, ..
            } = &mut deferred.tactic
            else {
                return Ok(None);
            };
            *surface_tactics = Some(certificate.to_proof_tactics());
            deferred.surface_recorded = false;
            let branch_skeleton =
                ProofCertificate::from_steps(surface_branch_skeleton(proof.certificate().steps()))
                    .to_proof_tactics();
            let (source_index, tactic_index) = (indexed.source_index, indexed.index);
            let mut capture = staged_expansion_capture.as_mut();
            let (framed, _) = proof.edit_replay_cursor(|replay, _, _| {
                if begin_tactic_expansion_capture(capture.take(), source_index, replay) {
                    replay.deferred_tactic_capture = Some(DeferredTacticCapture {
                        tactic_index,
                        source_index,
                        post_execution_index: replay.post_execution_tactics.len(),
                        branch_skeleton,
                    });
                }
                replay.post_execution_tactics.push(deferred);
            })?;
            proof = framed;
            continue;
        }
        if let Some(error) = post_exit_execution_tactic_error(&indexed.tactic) {
            return Err(error);
        }
        let Some(post_tactic) = flat_post_execution_tactic(&indexed.tactic) else {
            return Ok(None);
        };
        proof = proof.defer_post_execution_source_tactic(
            indexed.index,
            indexed.source_index,
            post_tactic,
            staged_expansion_capture.as_mut(),
        )?;
    }
    if let (Some(expansion_capture), Some(staged)) = (expansion_capture, staged_expansion_capture) {
        *expansion_capture = staged;
    }
    Ok(Some(proof))
}

/// Checks one function proof containing supported top-level resource scopes
/// and execution branches without exporting any checked structure back into
/// replay-owned semantic state. Linear prefixes, structural bodies and joins,
/// intervening continuations, the frame, and the outcome suffix remain one
/// persistent Proof lineage; a miss publishes neither semantic state nor
/// expansion metadata.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn try_check_structural_function_proof<'a>(
    context: &ProofReplayContext,
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
    let mut staged_expansion_capture = expansion_capture.as_deref().cloned();
    let proof_site = context.replay.proof_site.clone();
    let owning_source_index = generated_by_source_index.unwrap_or(usize::MAX);
    let mut proof = Proof::for_execution_frontier(
        claim_label,
        internal_proof_first_index(program).ok_or_else(|| {
            ClickError::new(format!("`{claim_label}` has no structural proof tactics"))
        })?,
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
                    true,
                    true,
                    false,
                    Some(claim_label),
                )?
                else {
                    return Ok(None);
                };
                proof = advanced;
                if !unconsumed.is_empty() {
                    if !matches!(continuation.as_ref(), InternalProofNode::Done) {
                        return Ok(None);
                    }
                    remaining = unconsumed;
                    break;
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
                    return Ok(None);
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
                    return Ok(None);
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
                    wanted == *source_index || capture_in_continuation || capture_in_nested_branch
                }) {
                    return Ok(None);
                }
                if !checked_structural_execution_branch_supported(
                    then_branch,
                    else_branch,
                    continuation,
                ) {
                    return Ok(None);
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
                    return Ok(None);
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
                        return Ok(None);
                    };
                    let Some(else_tactics) = deferred_post_execution_region(else_branch) else {
                        return Ok(None);
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
                                return Ok(None);
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
                if expanded_execution_internal_if_supported(current, 0) {
                    let Some(result) =
                        advance_expanded_execution_region(proof, current, 0, &mut None)?
                    else {
                        return Ok(None);
                    };
                    proof = result.proof;
                    for deferred in result.post_execution {
                        proof = proof.defer_post_execution_source_tactic(
                            deferred.tactic_index,
                            deferred.source_index,
                            deferred.tactic,
                            staged_expansion_capture.as_mut(),
                        )?;
                    }
                    saw_structure = true;
                    break;
                }
                proof = proof.with_execution_tactic_index(*index)?;
                if let Some((then_steps, else_steps)) =
                    expanded_execution_if_steps(condition, then_branch, else_branch)
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
                        source_successor_if_arm_step(then_tactic, condition, true),
                        source_successor_if_arm_step(else_tactic, condition, false),
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
                            (arm_steps[0].0, arm_steps[0].1, arm_steps[0].2.clone()),
                            (arm_steps[1].0, arm_steps[1].1, arm_steps[1].2.clone()),
                        ],
                    )?;
                    if exact.is_some() {
                        record_source_successor_smart_expansions(
                            arm_steps,
                            staged_expansion_capture.as_mut(),
                            proof_site.as_ref(),
                            owning_source_index,
                        );
                        exact
                    } else if !arm_steps[0].3 && !arm_steps[1].3 {
                        proof.try_collapse_statement_successor_if(
                            condition,
                            [
                                (arm_steps[0].0, arm_steps[0].2.clone()),
                                (arm_steps[1].0, arm_steps[1].2.clone()),
                            ],
                        )?
                    } else {
                        None
                    }
                } else {
                    None
                };
                let consumed_leading_steps = product.is_some();
                let (split, record) = if let Some(collapsed) = product {
                    collapsed
                } else if let Some(existing) = proof.enter_statement_successor_if(condition)? {
                    existing
                } else {
                    proof.split_focused_execution_if(condition.clone())?
                };
                let mut advanced = split;
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
                    let Some(next) = next else {
                        return Ok(None);
                    };
                    if !next.is_at_function_exit() {
                        return Ok(None);
                    }
                    advanced = next;
                }
                proof = advanced.join_focused_execution_if_terminal(&record)?;
                saw_structure = true;
                current = continuation;
            }
        }
    }
    if !saw_structure {
        return Ok(None);
    }
    check_verification_deadline()?;
    if !proof.is_at_function_exit() {
        if let Some(error) = remaining
            .first()
            .and_then(|indexed| pre_exit_outcome_tactic_error(&indexed.tactic))
        {
            return Err(error);
        }
        return Ok(None);
    }
    for indexed in remaining {
        check_verification_deadline()?;
        // A bare `frame()` among the ordered outcome operations is the
        // smart function frame searched on the exit Proof now, as the
        // linear continuation does for a frame that arrives first.
        if let ProofTactic::SmartFrame(region) = &indexed.tactic {
            let checkpoint = proof.checkpoint();
            let Some(framed) =
                proof.try_smart_frame_at(region.as_ref(), indexed.index, indexed.source_index)?
            else {
                return Ok(None);
            };
            // The function frame at exit retains an ordered deferral whose
            // authority finalization applies. Keep that deferral, printing
            // the checked contribution at its source position after the
            // outcome operations deferred before it, on the unframed Proof:
            // the frame step itself would otherwise precede them in the
            // retained certificate.
            let certificate = framed.certificate_since(&checkpoint)?;
            let (_, deferred) =
                framed.edit_replay_cursor(|replay, _, _| replay.post_execution_tactics.pop())?;
            let Some(mut deferred) = deferred else {
                return Ok(None);
            };
            let PostExecutionTactic::CheckedFrameUsing {
                surface_tactics, ..
            } = &mut deferred.tactic
            else {
                return Ok(None);
            };
            *surface_tactics = Some(certificate.to_proof_tactics());
            deferred.surface_recorded = false;
            let branch_skeleton =
                ProofCertificate::from_steps(surface_branch_skeleton(proof.certificate().steps()))
                    .to_proof_tactics();
            let (source_index, tactic_index) = (indexed.source_index, indexed.index);
            let mut capture = staged_expansion_capture.as_mut();
            let (framed, _) = proof.edit_replay_cursor(|replay, _, _| {
                if begin_tactic_expansion_capture(capture.take(), source_index, replay) {
                    replay.deferred_tactic_capture = Some(DeferredTacticCapture {
                        tactic_index,
                        source_index,
                        post_execution_index: replay.post_execution_tactics.len(),
                        branch_skeleton,
                    });
                }
                replay.post_execution_tactics.push(deferred);
            })?;
            proof = framed;
            continue;
        }
        if let Some(error) = post_exit_execution_tactic_error(&indexed.tactic) {
            return Err(error);
        }
        let Some(post_tactic) = flat_post_execution_tactic(&indexed.tactic) else {
            return Ok(None);
        };
        proof = proof.defer_post_execution_source_tactic(
            indexed.index,
            indexed.source_index,
            post_tactic,
            staged_expansion_capture.as_mut(),
        )?;
    }
    if let (Some(expansion_capture), Some(staged)) = (expansion_capture, staged_expansion_capture) {
        *expansion_capture = staged;
    }
    Ok(Some(proof))
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
            // An explicit script is checked by its simple steps alone: a
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
    // miss so the unchanged compatibility interpreter can own it.
    Ok(selected.filter(ProofScope::is_complete))
}

/// One smart statement step on a preservation-region descendant: the exact
/// Proof selection first, the planner construction second, with the checked
/// certificate delta pushed into the path's surface record. Shared by the
/// preservation driver and the automatic-preservation search.
pub(in crate::lang::click::proof) fn preservation_smart_step<'a>(
    proof: Proof<'a>,
) -> Result<Proof<'a>, ClickError> {
    let advanced = if let Some(stepped) = proof.try_smart_step()? {
        stepped
    } else {
        proof.apply_planned_smart_step(0)?
    };
    let checkpoint = proof.checkpoint();
    let steps = advanced.certificate_since(&checkpoint)?.steps().to_vec();
    advanced.record_surface_steps(&steps)
}

/// Drives one preservation program region on the typed boundary `Proof`.
/// `pending` is the stack of continuation nodes still owed to the current
/// path, innermost first. Proof-level `if` arms stay separate — a
/// preservation path never rejoins across the back edge — so every leaf
/// reaches the loop's typed boundary and is collected for the caller's
/// per-path bundle, certificate, and effect processing. There is no
/// compatibility fallback: a tactic outside the checked operations is a
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
                    ProofTactic::Loop(_) | ProofTactic::Simp | ProofTactic::SmartStep
                );
                if handled_by_linear_driver {
                    let segment = InternalProofNode::Linear {
                        tactics: vec![indexed.clone()],
                        continuation: Box::new(InternalProofNode::Done),
                    };
                    let checkpoint = proof.checkpoint();
                    let advanced = advance_checked_linear_continuation(
                        proof.clone(),
                        &segment,
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                        false,
                        true,
                        false,
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
                    let steps = advanced.certificate_since(&checkpoint)?.steps().to_vec();
                    proof = advanced.record_surface_steps(&steps)?;
                    if matches!(indexed.tactic, ProofTactic::CloseInvariants) {
                        proof =
                            proof.record_invariant_closer(indexed.index, indexed.source_index)?;
                    }
                    continue;
                }
                match &indexed.tactic {
                    ProofTactic::SmartStep => {
                        let checkpoint = proof.checkpoint();
                        proof = if let Some(stepped) = proof.try_smart_step()? {
                            stepped
                        } else {
                            proof.apply_planned_smart_step(indexed.index)?
                        };
                        let steps = proof.certificate_since(&checkpoint)?.steps().to_vec();
                        proof = proof.record_surface_steps(&steps)?;
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
                let focused = advanced.focus(id)?;
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
            let checkpoint = proof.checkpoint();
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
            let steps = advanced.certificate_since(&checkpoint)?.steps().to_vec();
            let advanced = advanced.record_surface_steps(&steps)?;
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
            let checkpoint = proof.checkpoint();
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
            let steps = proof.certificate_since(&checkpoint)?.steps().to_vec();
            let proof = proof.record_surface_steps(&steps)?;
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
                    return Ok(None);
                };
                let certificate = framed.certificate_since(&checkpoint)?;
                let (_, deferred) = framed
                    .edit_replay_cursor(|replay, _, _| replay.post_execution_tactics.pop())?;
                let Some(mut deferred) = deferred else {
                    return Ok(None);
                };
                let PostExecutionTactic::CheckedFrameUsing {
                    surface_tactics, ..
                } = &mut deferred.tactic
                else {
                    return Ok(None);
                };
                *surface_tactics = Some(certificate.to_proof_tactics());
                deferred.surface_recorded = false;
                let branch_skeleton = ProofCertificate::from_steps(surface_branch_skeleton(
                    proof.certificate().steps(),
                ))
                .to_proof_tactics();
                let (source_index, tactic_index) = (indexed.source_index, indexed.index);
                let mut capture = expansion_capture.as_deref_mut();
                let (next, _) = proof.edit_replay_cursor(|replay, _, _| {
                    if begin_tactic_expansion_capture(capture.take(), source_index, replay) {
                        replay.deferred_tactic_capture = Some(DeferredTacticCapture {
                            tactic_index,
                            source_index,
                            post_execution_index: replay.post_execution_tactics.len(),
                            branch_skeleton,
                        });
                    }
                    replay.post_execution_tactics.push(deferred);
                })?;
                proof = next;
                continue;
            }
            if let Some(error) = post_exit_execution_tactic_error(&indexed.tactic) {
                return Err(error);
            }
            let Some(post_tactic) = flat_post_execution_tactic(&indexed.tactic) else {
                return Ok(None);
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
        let next = if let Some(step) = linear_execution_simple_step(&indexed.tactic) {
            proof.apply_step(step)?
        } else if matches!(indexed.tactic, ProofTactic::SmartStep) {
            let Some(next) = proof.try_indexed_execute_step()? else {
                return Ok(None);
            };
            next
        } else if let ProofTactic::ApplyTheorem(application) = &indexed.tactic {
            if proof.is_at_function_exit() {
                // Exit applications need one point proof per concrete
                // outcome so that `result` lowers correctly; ordered
                // finalization owns that distinct operation.
                return Ok(None);
            }
            let Some(next) = proof.try_theorem_application(application)? else {
                return Ok(None);
            };
            next
        } else if let ProofTactic::Transport { source, target } = &indexed.tactic {
            if proof.is_at_function_exit() {
                return Ok(None);
            }
            let Some(next) = proof.try_execution_fact_transport(source, target)? else {
                return Ok(None);
            };
            next
        } else if let ProofTactic::Have(have) = &indexed.tactic {
            let nested = proof.begin_have(have.proposition.clone())?;
            let Some(nested) = solve_nested_have(nested, have, false)? else {
                return Ok(None);
            };
            nested.join()?
        } else if matches!(
            indexed.tactic,
            ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths
        ) {
            let Some(next) = proof.try_focused_execute_to_exit()? else {
                return Ok(None);
            };
            next
        } else {
            return Ok(None);
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

fn source_successor_if_arm_step(
    indexed: &IndexedTactic,
    condition: &ClickProposition,
    take_then: bool,
) -> Option<(usize, usize, Vec<ClickProposition>, bool)> {
    match &indexed.tactic {
        ProofTactic::StepUsing(premises) => {
            Some((indexed.index, indexed.source_index, premises.clone(), false))
        }
        ProofTactic::SmartStep => Some((
            indexed.index,
            indexed.source_index,
            vec![if take_then {
                condition.clone()
            } else {
                negate_click_proposition(condition)
            }],
            true,
        )),
        _ => None,
    }
}

fn record_source_successor_smart_expansions(
    arm_steps: &[(usize, usize, Vec<ClickProposition>, bool); 2],
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
) {
    let Some(site) = proof_site else {
        return;
    };
    for (_, source_index, premises, smart) in arm_steps {
        if *smart
            && *source_index != owning_source_index
            && selected_tactic_index_for_site(expansion_capture.as_deref(), site)
                == Some(*source_index)
        {
            let certificate =
                ProofCertificate::from_steps(vec![SimpleProofStep::StepUsing(premises.clone())]);
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
        return Ok(None);
    };
    let Some(_) = tactics.first() else {
        return Ok(None);
    };
    let Some(proof) = advance_focused_execution_arm(
        proof,
        &tactics[1..],
        expansion_capture.as_deref_mut(),
        proof_site,
        owning_source_index,
    )?
    else {
        return Ok(None);
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
        return Ok(None);
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
                return Ok(None);
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
                return Ok(None);
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
                return Ok(None);
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
            if !matches!(continuation.as_ref(), InternalProofNode::Done) {
                return Ok(None);
            }
            if proof.is_at_function_exit() {
                let Some(then_tactics) = deferred_post_execution_region(then_branch) else {
                    return Ok(None);
                };
                let Some(else_tactics) = deferred_post_execution_region(else_branch) else {
                    return Ok(None);
                };
                if !deferred_post_execution_if_is_explicit_path_cursor(
                    condition,
                    &then_tactics,
                    &else_tactics,
                ) && !proof.post_execution_if_is_path_decided(condition)?
                {
                    return Ok(None);
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
                    source_successor_if_arm_step(then_tactic, condition, true),
                    source_successor_if_arm_step(else_tactic, condition, false),
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
                        (arm_steps[0].0, arm_steps[0].1, arm_steps[0].2.clone()),
                        (arm_steps[1].0, arm_steps[1].1, arm_steps[1].2.clone()),
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
            let (split, record) = if let Some(collapsed) = product {
                collapsed
            } else if let Some(existing) = proof.enter_statement_successor_if(condition)? {
                existing
            } else {
                proof.split_focused_execution_if(condition.clone())?
            };
            let mut advanced = split;
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
                let Some(next) = next else {
                    return Ok(None);
                };
                if !next.is_at_function_exit() {
                    return Ok(None);
                }
                advanced = next;
            }
            let proof = advanced
                .join_focused_execution_if_terminal(&record)?
                .restore_execution_tactic_attribution(&owner)?;
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
        return Ok(None);
    }
    let proof = proof.with_execution_tactic_index(tactic_index)?;
    let checkpoint = proof.checkpoint();
    let (split, record) = proof.split_focused_execution_branch()?;
    if ensuring
        .as_ref()
        .is_some_and(|_| !record.supports_interface_branch())
    {
        return Ok(None);
    }
    let has_sole_feasible_arm = record.sole_feasible_arm().is_some();
    let mut advanced = split;
    for (take_then, region) in [(true, then_branch), (false, else_branch)] {
        if record.arm_id(take_then).is_none() {
            continue;
        }
        let Some(next) = advance_focused_execution_region(
            advanced.focus_split_arm(&record, take_then)?,
            Some(&record),
            region,
            expansion_capture.as_deref_mut(),
            proof_site,
            owning_source_index,
            depth + 1,
        )?
        else {
            return Ok(None);
        };
        advanced = next;
    }
    let mut consumed_continuation = false;
    if !has_sole_feasible_arm {
        let then_exit = advanced.arm_at_function_exit(&record, true);
        let else_exit = advanced.arm_at_function_exit(&record, false);
        if then_exit != else_exit {
            // One arm returned. The other continues past its boundary into
            // the shared continuation, which it runs to function exit; the
            // two arms then join terminally. An `ensuring` interface is
            // checked on the continuing arm at its boundary; the retained
            // state is the arm's own, which is stronger than the interface.
            let continuing = advanced.focus_split_arm(&record, !then_exit)?;
            if let Some(assertions) = ensuring
                && !continuing.interface_facts_established(assertions)?
            {
                return Ok(None);
            }
            let continuing = continuing.continue_arm_into_parent_frontier(&record)?;
            let Some(next) = advance_focused_execution_region(
                continuing,
                Some(&record),
                continuation,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
                depth + 1,
            )?
            else {
                return Ok(None);
            };
            if !next.is_at_function_exit() {
                return Ok(None);
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
    let joined = advanced.join_focused_execution_split(&record, empty, join_interface)?;
    let certificate = proof_site
        .is_some()
        .then(|| joined.certificate_since(&checkpoint))
        .transpose()?;
    Ok(Some((
        joined,
        has_sole_feasible_arm,
        certificate,
        consumed_continuation,
    )))
}

fn linear_execution_steps(node: &InternalProofNode) -> Option<Vec<SimpleProofStep>> {
    linear_execution_tactics(node)?
        .iter()
        .map(|indexed| arm_simple_step(&indexed.tactic))
        .collect()
}

fn expanded_execution_if_steps(
    condition: &ClickProposition,
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
) -> Option<(Vec<SimpleProofStep>, Vec<SimpleProofStep>)> {
    let then_steps = linear_execution_steps(then_branch)?;
    let else_steps = linear_execution_steps(else_branch)?;
    (expanded_execution_arm_supported(condition, true, &then_steps)
        && expanded_execution_arm_supported(condition, false, &else_steps)
        && !(then_steps.is_empty() && else_steps.is_empty()))
    .then_some((then_steps, else_steps))
}

struct ExpandedExecutionRegionAdvance<'a> {
    proof: Proof<'a>,
    post_execution: Vec<DeferredPostExecutionTactic>,
}

fn expanded_execution_internal_arm_supported(
    condition: &ClickProposition,
    take_then: bool,
    region: &InternalProofNode,
    depth: usize,
) -> bool {
    if depth >= MAX_CHECKED_EXECUTION_REGION_DEPTH {
        return false;
    }
    if matches!(region, InternalProofNode::Done) {
        return true;
    }
    let InternalProofNode::Linear {
        tactics,
        continuation,
    } = region
    else {
        return false;
    };
    let post_only = matches!(continuation.as_ref(), InternalProofNode::Done)
        && tactics
            .iter()
            .all(|indexed| flat_post_execution_tactic(&indexed.tactic).is_some())
        && tactics
            .iter()
            .any(|indexed| !matches!(indexed.tactic, ProofTactic::Simp));
    if post_only {
        return true;
    }
    let expected = if take_then {
        condition.clone()
    } else {
        negate_click_proposition(condition)
    };
    let entry_supported = match tactics.first().map(|indexed| &indexed.tactic) {
        Some(ProofTactic::Step) => true,
        Some(ProofTactic::StepUsing(premises)) => {
            premises.as_slice() == std::slice::from_ref(&expected)
        }
        _ => false,
    };
    if !entry_supported {
        return false;
    }
    match continuation.as_ref() {
        InternalProofNode::Done => {
            tactics.iter().all(|indexed| {
                arm_simple_step(&indexed.tactic).is_some()
                    || (!matches!(indexed.tactic, ProofTactic::Simp)
                        && flat_post_execution_tactic(&indexed.tactic).is_some())
            }) && tactics.iter().any(|indexed| {
                !matches!(indexed.tactic, ProofTactic::Simp)
                    && flat_post_execution_tactic(&indexed.tactic).is_some()
            })
        }
        nested @ InternalProofNode::If { .. } => {
            tactics
                .iter()
                .all(|indexed| arm_simple_step(&indexed.tactic).is_some())
                && expanded_execution_internal_if_supported(nested, depth + 1)
        }
        InternalProofNode::Linear { .. }
        | InternalProofNode::Open { .. }
        | InternalProofNode::Branch { .. } => false,
    }
}

fn expanded_execution_internal_if_supported(node: &InternalProofNode, depth: usize) -> bool {
    let InternalProofNode::If {
        condition,
        then_branch,
        else_branch,
        continuation,
        ..
    } = node
    else {
        return false;
    };
    proof_case_is_stable_program_point_condition(condition)
        && expanded_execution_internal_arm_supported(condition, true, then_branch, depth)
        && expanded_execution_internal_arm_supported(condition, false, else_branch, depth)
        && matches!(continuation.as_ref(), InternalProofNode::Done)
}

fn advance_expanded_execution_linear_region<'a>(
    mut proof: Proof<'a>,
    tactics: &[IndexedTactic],
    continuation: &InternalProofNode,
    depth: usize,
    enclosing: &mut Option<&ExecutionSplit<'a>>,
) -> Result<Option<ExpandedExecutionRegionAdvance<'a>>, ClickError> {
    if depth >= MAX_CHECKED_EXECUTION_REGION_DEPTH {
        return Ok(None);
    }
    for (offset, indexed) in tactics.iter().enumerate() {
        if proof.is_at_function_exit() {
            let Some(post_execution) =
                deferred_post_execution_linear_region(&tactics[offset..], continuation)
            else {
                return Ok(None);
            };
            return Ok(Some(ExpandedExecutionRegionAdvance {
                proof,
                post_execution,
            }));
        }
        let Some(step) = arm_simple_step(&indexed.tactic) else {
            return Ok(None);
        };
        // A terminal arm's source steps may continue past its typed
        // boundary into the parent continuation, consuming the one escape
        // the enclosing split record supplies.
        if matches!(step, SimpleProofStep::StepUsing(_) | SimpleProofStep::Step)
            && proof.is_at_region_boundary()
            && let Some(record) = enclosing.take()
        {
            proof = proof.continue_arm_into_parent_frontier(record)?;
        }
        proof = proof.with_execution_tactic_index(indexed.index)?;
        proof = proof.apply_step(step)?;
    }
    advance_expanded_execution_region(proof, continuation, depth + 1, enclosing)
}

fn expanded_execution_region_leading_steps(
    region: &InternalProofNode,
) -> Option<(&[IndexedTactic], &InternalProofNode, Vec<SimpleProofStep>)> {
    let InternalProofNode::Linear {
        tactics,
        continuation,
    } = region
    else {
        return None;
    };
    let steps = tactics
        .iter()
        .map_while(|indexed| {
            flat_post_execution_tactic(&indexed.tactic)
                .is_none()
                .then(|| arm_simple_step(&indexed.tactic))
                .flatten()
        })
        .collect();
    Some((tactics, continuation, steps))
}

fn advance_expanded_execution_if_region<'a>(
    proof: Proof<'a>,
    index: usize,
    source_index: usize,
    condition: &ClickProposition,
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
    continuation: &InternalProofNode,
    depth: usize,
    enclosing: &mut Option<&ExecutionSplit<'a>>,
) -> Result<Option<ExpandedExecutionRegionAdvance<'a>>, ClickError> {
    if depth >= MAX_CHECKED_EXECUTION_REGION_DEPTH {
        return Ok(None);
    }
    let mut proof = proof.with_execution_tactic_index(index)?;
    if proof.is_at_region_boundary()
        && let Some(record) = enclosing.take()
    {
        proof = proof.continue_arm_into_parent_frontier(record)?;
    }
    if !proof.frontier_is_execution_branch(condition)? {
        return Ok(None);
    }
    let (split, record) = proof.split_focused_execution_branch()?;
    let mut advanced = split;
    let mut post_arms = [Vec::new(), Vec::new()];
    for (arm_index, take_then, region) in
        [(0usize, true, then_branch), (1usize, false, else_branch)]
    {
        let leading = expanded_execution_region_leading_steps(region);
        let leading_steps = leading
            .as_ref()
            .map(|(_, _, steps)| steps.as_slice())
            .unwrap_or(&[]);
        let focused = advanced.focus_expanded_execution_arm_entry(
            &record,
            take_then,
            condition,
            leading_steps,
        )?;
        let Some((focused, consumed)) = focused else {
            if !checked_execution_region_is_empty(region)
                && deferred_post_execution_region(region).is_none()
            {
                return Ok(None);
            }
            continue;
        };
        let Some((tactics, arm_continuation, _)) = leading else {
            return Ok(None);
        };
        let mut arm_enclosing = Some(&record);
        let Some(result) = advance_expanded_execution_linear_region(
            focused,
            &tactics[consumed..],
            arm_continuation,
            depth + 1,
            &mut arm_enclosing,
        )?
        else {
            return Ok(None);
        };
        advanced = result.proof;
        post_arms[arm_index] = result.post_execution;
    }
    let joined = advanced.join_focused_execution_split(&record, false, None)?;
    let Some(mut continued) =
        advance_expanded_execution_region(joined, continuation, depth + 1, enclosing)?
    else {
        return Ok(None);
    };
    let branch = DeferredPostExecutionTactic {
        tactic_index: index,
        source_index,
        tactic: PostExecutionTactic::If {
            condition: condition.clone(),
            then_tactics: std::mem::take(&mut post_arms[0]),
            else_tactics: std::mem::take(&mut post_arms[1]),
        },
        surface_recorded: false,
    };
    continued.post_execution.insert(0, branch);
    Ok(Some(continued))
}

fn advance_expanded_execution_region<'a>(
    proof: Proof<'a>,
    region: &InternalProofNode,
    depth: usize,
    enclosing: &mut Option<&ExecutionSplit<'a>>,
) -> Result<Option<ExpandedExecutionRegionAdvance<'a>>, ClickError> {
    if depth >= MAX_CHECKED_EXECUTION_REGION_DEPTH {
        return Ok(None);
    }
    match region {
        InternalProofNode::Done => {
            if proof.is_at_function_exit() {
                Ok(Some(ExpandedExecutionRegionAdvance {
                    proof,
                    post_execution: Vec::new(),
                }))
            } else {
                Ok(None)
            }
        }
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => advance_expanded_execution_linear_region(
            proof,
            tactics,
            continuation,
            depth + 1,
            enclosing,
        ),
        InternalProofNode::If {
            index,
            source_index,
            condition,
            then_branch,
            else_branch,
            continuation,
        } => advance_expanded_execution_if_region(
            proof,
            *index,
            *source_index,
            condition,
            then_branch,
            else_branch,
            continuation,
            depth + 1,
            enclosing,
        ),
        InternalProofNode::Open { .. } | InternalProofNode::Branch { .. } => Ok(None),
    }
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
        if let Some(step) = linear_execution_simple_step(&indexed.tactic) {
            scope = if let SimpleProofStep::FrameUsing { region, premises } = &step {
                if !scope.supports_checked_frame_using(region.as_ref(), premises)? {
                    return Ok(None);
                }
                scope.apply_step_at(step, indexed.index, indexed.source_index)?
            } else {
                scope.apply_step(step)?
            };
            continue;
        }
        if matches!(indexed.tactic, ProofTactic::SmartStep) {
            let checkpoint = scope.checkpoint();
            let Some(stepped) = scope.try_smart_step()? else {
                return Ok(None);
            };
            scope = stepped;
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
        if let ProofTactic::ApplyTheorem(application) = &indexed.tactic {
            let checkpoint = scope.checkpoint();
            let Some(applied) = scope.try_theorem_application(application)? else {
                return Ok(None);
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
                return Ok(None);
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
                return Ok(None);
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
                return Ok(None);
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
                return Ok(None);
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
            return Ok(None);
        };
        let nested = scope.begin_have(have.proposition.clone())?;
        let selected = solve_nested_have(nested, have, false)?;
        let Some(selected) = selected else {
            return Ok(None);
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
            return Ok(None);
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
            return Ok(None);
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
            expanded_execution_if_steps(condition, then_branch, else_branch)
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
            return Ok(None);
        };
        return advance_checked_open_scope(
            scope,
            continuation,
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
        return Ok(None);
    };
    if checked_execution_region_pair(then_branch, else_branch).is_none() {
        return Ok(None);
    }
    let (split, record) = scope.split_execution_branch()?;
    if ensuring
        .as_ref()
        .is_some_and(|_| !record.supports_interface_branch())
    {
        return Ok(None);
    }
    let empty = checked_execution_region_is_empty(then_branch)
        && checked_execution_region_is_empty(else_branch);
    let mut advanced = split;
    for (take_then, region) in [(true, then_branch), (false, else_branch)] {
        if record.arm_id(take_then).is_none() {
            continue;
        }
        let Some(next) = advance_focused_execution_region(
            advanced.focus_split_arm(&record, take_then)?,
            Some(&record),
            region,
            expansion_capture.as_deref_mut(),
            proof_site,
            owning_source_index,
            0,
        )?
        else {
            return Ok(None);
        };
        advanced = next;
    }
    let scope = scope.join_execution_split(&advanced, &record, empty, ensuring.clone())?;
    advance_checked_open_scope(
        scope,
        continuation,
        expansion_capture,
        proof_site,
        owning_source_index,
    )
}

// The complete mdtest and example gates both reach depth 9. Keep a modest
// amount of room for ordinary proof nesting while rejecting hostile or
// accidentally recursive certificates before the large interpreter frame is
// entered. The wrapper must stay separate from `execute_internal_proof_inner`:
// checking inside the inner function would reserve its frame before observing
// the bound and could still abort on stack overflow.
const MAX_INTERNAL_PROOF_REPLAY_DEPTH: usize = 12;

thread_local! {
    static INTERNAL_PROOF_REPLAY_DEPTH: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
}

struct InternalProofReplayDepthGuard;

impl InternalProofReplayDepthGuard {
    fn enter(claim_label: &str) -> Result<Self, ClickError> {
        INTERNAL_PROOF_REPLAY_DEPTH.with(|depth| {
            let current = depth.get();
            if current >= MAX_INTERNAL_PROOF_REPLAY_DEPTH {
                return Err(ClickError::new(format!(
                    "`{claim_label}` proof replay nesting exceeds the supported maximum of \
                     {MAX_INTERNAL_PROOF_REPLAY_DEPTH}; simplify nested proof blocks"
                )));
            }
            depth.set(current + 1);
            Ok(Self)
        })
    }
}

impl Drop for InternalProofReplayDepthGuard {
    fn drop(&mut self) {
        INTERNAL_PROOF_REPLAY_DEPTH.with(|depth| {
            let current = depth.get();
            debug_assert!(current > 0, "proof replay depth guard underflow");
            depth.set(current.saturating_sub(1));
        });
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
    #[cfg(test)]
    INTERNAL_PROOF_EXECUTIONS.with(|executions| executions.set(executions.get() + 1));
    #[cfg(test)]
    if INTERNAL_PROOF_REPLAY_DEPTH.with(|depth| depth.get() == 0) {
        ROOT_INTERNAL_PROOF_EXECUTIONS.with(|executions| executions.set(executions.get() + 1));
    }
    #[cfg(test)]
    COLLECTED_INTERNAL_PROOF_LABELS.with(|labels| {
        if let Some(labels) = labels.borrow_mut().as_mut() {
            labels.push(claim_label.to_string());
        }
    });
    let _depth_guard = InternalProofReplayDepthGuard::enter(claim_label)?;
    execute_internal_proof_inner(
        node,
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

#[allow(clippy::too_many_arguments)]
fn execute_internal_proof_inner(
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
            ..
        } => {
            let mut context = context;
            // A mid-execution case condition may name the current statement's
            // entry snapshot (`at(statement(N).entry, ...)`) before any step
            // has crossed that statement; record it so the form lowers.
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
                // surface record. Cross-context extraction reassembles the
                // claim's provenance at exactly these recorded choices, so
                // the tactics a case runs are written inside its surface
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
            source_index: _,
            ensuring,
            then_branch,
            else_branch,
            continuation,
        } => {
            let mut context = context;
            let statement_index = context.replay.frontier.next_statement_index;
            // The branch condition is written against the branch statement's
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
            let selected_source_index = context.replay.proof_site.as_ref().and_then(|site| {
                selected_tactic_index_for_site(expansion_capture.as_deref(), site)
            });
            let capture_in_continuation = selected_source_index
                .is_some_and(|wanted| internal_proof_contains_source_index(continuation, wanted));
            let (_, _, branch_statement, _) = next_top_level_statement_from_execution_point(
                &context.replay,
                &context.state,
                function,
                arguments,
                claim_label,
                *index,
                "branch",
            )?;
            let CStatement::If {
                then_branch: branch_statement_then,
                else_branch: branch_statement_else,
                ..
            } = branch_statement.clone()
            else {
                unreachable!("source branch was checked as an if above")
            };
            let branch_surface_condition = {
                let CStatement::If { condition, .. } = &branch_statement else {
                    unreachable!("source branch was checked as an if above")
                };
                surface_with_source_site(
                    &surface_c_condition(condition),
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
            // Writes a proof-`if` case around a context's arm record: the
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
                    let entry_step = SimpleProofStep::Step;
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
                    BranchArmMode::Inline,
                    None,
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
                let empty_arm = matches!(
                    if take_then {
                        branch_statement_then.as_ref()
                    } else {
                        branch_statement_else.as_ref()
                    },
                    CStatement::Skip
                );
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
                    let reached_continuation = returned
                        || branch_context.replay.is_at_region_boundary()
                        || branch_context.replay.frontier.next_statement_index
                            == continuation_index;
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
                // Every continuing arm rests at its typed region boundary,
                // so the arms share the parent's continuation by
                // construction; the interface anchors there.
                let target = ProgramPointRef {
                    region: CodeRegionRef::Statement(continuation_index),
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
            // recorded surface branch choice is written against the branch
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
            // Inline arms carry the post-join frontier themselves; the join
            // records the branch region's canonical exit state.
            record_statement_program_point_state(
                &mut joined_context.replay,
                function_block,
                statement_index,
                ProgramPointKind::Exit,
                joined_context.state.clone(),
            );
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
pub(in crate::lang::click::proof) fn introduce_proof_case_assumption(
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
    if proof_case_is_statement_identity_condition(condition) {
        // An opaque call's allocation-identity split owns several certified
        // statement successors. Lowering this snapshot-qualified condition
        // against one representative successor would bake that successor's
        // fresh kernel variables into both proof arms. Retain the surface
        // condition so final path routing lowers it independently for each
        // concrete outcome.
        context.replay.case_assumptions.push(ReplayCaseAssumption {
            tactic_index,
            condition: condition.clone(),
            value,
            fact: None,
            at_function_entry: false,
        });
        return Ok(true);
    }
    if context.replay.loop_effect_goal.is_some() {
        // A structural-effect replay path may already own the exact C-branch
        // fact under this Surface spelling. Prefer that unambiguous indexed
        // identity to rereading the condition from the heap. Ordinary loop
        // preservation must lower afresh because the same spelling can name
        // the next iteration's new condition variables.
        let positive_surface = condition.clone();
        let negative_surface = negate_click_proposition(condition);
        let positive = context
            .replay
            .surface_propositions
            .available_kernel_matching(&positive_surface, |kernel| {
                context.pure_facts.contains(kernel)
            })
            .cloned();
        let negative = context
            .replay
            .surface_propositions
            .available_kernel_matching(&negative_surface, |kernel| {
                context.pure_facts.contains(kernel)
            })
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
            context
                .replay
                .surface_propositions
                .record_lowering(&surface_fact, &kernel_fact)?;
            context.replay.case_assumptions.push(ReplayCaseAssumption {
                tactic_index,
                condition: condition.clone(),
                value,
                fact: Some(kernel_fact),
                at_function_entry: context.replay.is_at_function_entry(),
            });
            return Ok(true);
        }
    }
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

fn proof_case_is_statement_identity_condition(condition: &ClickProposition) -> bool {
    let ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::Equal,
        right,
    } = condition
    else {
        return false;
    };
    let is_statement_exit = |expression: &ContractExpression| {
        matches!(
            expression,
            ContractExpression::At {
                selector: VisitSelector::ProgramPoint(ProgramPointRef {
                    region: CodeRegionRef::Statement(_),
                    kind: ProgramPointKind::Exit,
                }),
                ..
            }
        )
    };
    let is_old = |expression: &ContractExpression| matches!(expression, ContractExpression::Old(_));
    (is_statement_exit(left) && is_old(right)) || (is_old(left) && is_statement_exit(right))
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

#[cfg(test)]
mod depth_guard_tests {
    use super::*;

    #[test]
    fn internal_proof_replay_depth_is_bounded_before_entering_the_large_frame() {
        let mut guards = Vec::new();
        for _ in 0..MAX_INTERNAL_PROOF_REPLAY_DEPTH {
            guards.push(
                InternalProofReplayDepthGuard::enter("deep_claim")
                    .expect("depths through the documented maximum should be accepted"),
            );
        }
        let error = match InternalProofReplayDepthGuard::enter("deep_claim") {
            Ok(_) => panic!("depth beyond the documented maximum should be rejected"),
            Err(error) => error,
        };
        assert!(
            error
                .message()
                .contains("proof replay nesting exceeds the supported maximum of 12"),
            "{error:?}"
        );
        drop(guards);
        InternalProofReplayDepthGuard::enter("next_claim")
            .expect("dropping a replay must restore the thread-local depth");
    }
}

/// The diagnostic for an execution tactic written after execution already
/// reached function exit: the tactic has no statement to run.
fn post_exit_execution_tactic_error(tactic: &ProofTactic) -> Option<ClickError> {
    let name = match tactic {
        ProofTactic::Step | ProofTactic::StepUsing(_) | ProofTactic::SmartStep => {
            "step()".to_string()
        }
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
        _ => return None,
    };
    Some(ClickError::new(format!(
        "`{name}` requires execution to reach function exit first"
    )))
}
