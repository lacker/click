use super::*;

#[cfg(test)]
thread_local! {
    static INTERNAL_PROOF_EXECUTIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
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
    matches!(
        steps.first(),
        Some(SimpleProofStep::StepUsing(premises))
            if premises.is_empty()
                || premises.as_slice() == std::slice::from_ref(&expected)
    ) && matches!(steps.last(), Some(SimpleProofStep::StepUsing(_)))
}

pub(in crate::lang::click::proof) fn expanded_execution_if_tactic_supported(
    tactic: &ProofTactic,
) -> bool {
    let ProofTactic::If(proof_if) = tactic else {
        return false;
    };
    let arm_steps = |tactics: &[ProofTactic]| {
        tactics
            .iter()
            .map(linear_execution_simple_step)
            .collect::<Option<Vec<_>>>()
    };
    let Some(then_steps) = arm_steps(&proof_if.then_tactics) else {
        return false;
    };
    let Some(else_steps) = arm_steps(&proof_if.else_tactics) else {
        return false;
    };
    expanded_execution_arm_supported(&proof_if.condition, true, &then_steps)
        && expanded_execution_arm_supported(&proof_if.condition, false, &else_steps)
        && !(then_steps.is_empty() && else_steps.is_empty())
}

pub(in crate::lang::click::proof) fn post_execution_if_tactic_supported(
    tactic: &ProofTactic,
) -> bool {
    let ProofTactic::If(proof_if) = tactic else {
        return false;
    };
    // A handwritten `if { simp() } else { simp() }` is an undecided logical
    // split, not an expansion cursor selecting a checked execution outcome.
    // Execution expansion leaves a stable program-point condition and
    // explicit checked operations in both arms.
    proof_case_is_stable_program_point_condition(&proof_if.condition)
        && proof_if
            .then_tactics
            .iter()
            .chain(&proof_if.else_tactics)
            .all(|tactic| {
                !matches!(tactic, ProofTactic::Simp) && flat_post_execution_tactic(tactic).is_some()
            })
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

fn internal_proof_first_index(node: &InternalProofNode) -> Option<usize> {
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

fn linear_execution_branch_tactics(node: &InternalProofNode) -> Option<&[IndexedTactic]> {
    let tactics = linear_execution_tactics(node)?;
    checked_execution_arm_tactics_end(tactics).map(|_| tactics)
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
) -> Option<CheckedExecutionRegionEnd> {
    tactics
        .iter()
        .enumerate()
        .all(|(index, indexed)| {
            let is_execute = matches!(
                indexed.tactic,
                ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths
            );
            (!is_execute || index + 1 == tactics.len())
                && (linear_execution_simple_step(&indexed.tactic).is_some()
                    || matches!(
                        indexed.tactic,
                        ProofTactic::SmartStep
                            | ProofTactic::ApplyTheorem(_)
                            | ProofTactic::Transport { .. }
                            | ProofTactic::Have(_)
                            | ProofTactic::SmartExecute
                            | ProofTactic::SmartExecuteAllPaths
                    ))
        })
        .then(|| {
            if execution_branch_tactics_end_at_exit(tactics) {
                CheckedExecutionRegionEnd::FunctionExit
            } else {
                CheckedExecutionRegionEnd::SharedContinuation
            }
        })
}

/// Classifies the supported execution-region grammar used inside a checked
/// branch arm. Linear prefixes and nested execution branches are accepted;
/// every sibling pair must agree on whether it returns to a shared frontier
/// or completes at function exit.
fn checked_execution_region_end(node: &InternalProofNode) -> Option<CheckedExecutionRegionEnd> {
    checked_execution_region_end_at(node, 0)
}

fn checked_execution_region_end_at(
    node: &InternalProofNode,
    depth: usize,
) -> Option<CheckedExecutionRegionEnd> {
    if depth >= MAX_CHECKED_EXECUTION_REGION_DEPTH {
        return None;
    }
    match node {
        InternalProofNode::Done => Some(CheckedExecutionRegionEnd::SharedContinuation),
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => match checked_execution_arm_tactics_end(tactics)? {
            CheckedExecutionRegionEnd::FunctionExit => {
                matches!(continuation.as_ref(), InternalProofNode::Done)
                    .then_some(CheckedExecutionRegionEnd::FunctionExit)
            }
            CheckedExecutionRegionEnd::SharedContinuation => {
                checked_execution_region_end_at(continuation, depth + 1)
            }
        },
        InternalProofNode::Branch {
            then_branch,
            else_branch,
            continuation,
            ..
        } => {
            let then_end = checked_execution_region_end_at(then_branch, depth + 1)?;
            let else_end = checked_execution_region_end_at(else_branch, depth + 1)?;
            if then_end != else_end {
                return None;
            }
            match then_end {
                CheckedExecutionRegionEnd::FunctionExit => {
                    matches!(continuation.as_ref(), InternalProofNode::Done)
                        .then_some(CheckedExecutionRegionEnd::FunctionExit)
                }
                CheckedExecutionRegionEnd::SharedContinuation => {
                    checked_execution_region_end_at(continuation, depth + 1)
                }
            }
        }
        InternalProofNode::Open { .. } | InternalProofNode::If { .. } => None,
    }
}

fn checked_execution_region_pair(
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
) -> Option<CheckedExecutionRegionEnd> {
    let then_end = checked_execution_region_end(then_branch)?;
    (checked_execution_region_end(else_branch)? == then_end).then_some(then_end)
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

fn checked_execution_region_contains_branch_source(
    node: &InternalProofNode,
    source_index: usize,
) -> bool {
    checked_execution_region_contains_branch_source_at(node, source_index, 0)
}

fn checked_execution_region_contains_branch_source_at(
    node: &InternalProofNode,
    source_index: usize,
    depth: usize,
) -> bool {
    if depth >= MAX_CHECKED_EXECUTION_REGION_DEPTH {
        return false;
    }
    match node {
        InternalProofNode::Done => false,
        InternalProofNode::Linear { continuation, .. } => {
            checked_execution_region_contains_branch_source_at(
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
                || checked_execution_region_contains_branch_source_at(
                    then_branch,
                    source_index,
                    depth + 1,
                )
                || checked_execution_region_contains_branch_source_at(
                    else_branch,
                    source_index,
                    depth + 1,
                )
                || checked_execution_region_contains_branch_source_at(
                    continuation,
                    source_index,
                    depth + 1,
                )
        }
        InternalProofNode::Open { .. } | InternalProofNode::If { .. } => false,
    }
}

/// Selects only arm pairs whose terminal shape has an audited Proof join.
/// Two arms that both end in `execute()` join as terminal outcomes; arms that
/// both stop at the shared continuation use the ordinary branch join. A mixed
/// pair still needs the legacy multi-context representation.
fn linear_execution_branch_pair<'a>(
    then_branch: &'a InternalProofNode,
    else_branch: &'a InternalProofNode,
) -> Option<(&'a [IndexedTactic], &'a [IndexedTactic])> {
    let then_tactics = linear_execution_branch_tactics(then_branch)?;
    let else_tactics = linear_execution_branch_tactics(else_branch)?;
    (execution_branch_tactics_end_at_exit(then_tactics)
        == execution_branch_tactics_end_at_exit(else_tactics))
    .then_some((then_tactics, else_tactics))
}

fn execution_branch_tactics_end_at_exit(tactics: &[IndexedTactic]) -> bool {
    tactics.last().is_some_and(|indexed| {
        matches!(
            indexed.tactic,
            ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths
        )
    })
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
fn deferred_post_execution_region(
    node: &InternalProofNode,
) -> Option<Vec<DeferredPostExecutionTactic>> {
    match node {
        InternalProofNode::Done => Some(Vec::new()),
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => {
            let mut deferred = tactics
                .iter()
                .map(|indexed| {
                    Some(DeferredPostExecutionTactic {
                        tactic_index: indexed.index,
                        source_index: indexed.source_index,
                        tactic: flat_post_execution_tactic(&indexed.tactic)?,
                        surface_recorded: false,
                    })
                })
                .collect::<Option<Vec<_>>>()?;
            deferred.extend(deferred_post_execution_region(continuation)?);
            Some(deferred)
        }
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

fn checked_structural_execution_branch_supported(
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
    continuation: &InternalProofNode,
) -> bool {
    checked_execution_region_pair(then_branch, else_branch).is_some()
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
            let Some(stepped) = stepped else {
                return Ok(None);
            };
            stepped
        } else if let ProofTactic::ApplyTheorem(application) = &indexed.tactic {
            let Some(applied) = proof.try_theorem_application(application)? else {
                return Ok(None);
            };
            applied
        } else if let ProofTactic::Transport { source, target } = &indexed.tactic {
            let Some(transported) = proof.try_execution_fact_transport(source, target)? else {
                return Ok(None);
            };
            transported
        } else if let ProofTactic::Have(have) = &indexed.tactic {
            let nested = proof.begin_have(have.proposition.clone())?;
            let Some(selected) = solve_nested_have(nested, have, authoritative_nested_haves)?
            else {
                return Ok(None);
            };
            selected.join()?
        } else if let ProofTactic::ExecuteUntil(region) = &indexed.tactic {
            let Some(executed) = proof.try_linear_execute_until(region)? else {
                return Ok(None);
            };
            executed
        } else if matches!(
            indexed.tactic,
            ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths
        ) {
            let Some(executed) = proof.try_linear_execute()? else {
                return Ok(None);
            };
            executed
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
        return Ok(None);
    }
    // An infeasible sibling has no surface operations to reapply yet. Keep
    // that exact shape on compatibility replay, using Proof-owned structural
    // metadata rather than extracting and inspecting a certificate here.
    if proof.has_empty_execution_branch_leaf() {
        return Ok(None);
    }
    for indexed in remaining {
        check_verification_deadline()?;
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
                    checked_execution_region_contains_branch_source(then_branch, wanted)
                        || checked_execution_region_contains_branch_source(else_branch, wanted)
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
                let Some((advanced, _, certificate)) = try_advance_checked_execution_branch(
                    proof,
                    *index,
                    ensuring,
                    then_branch,
                    else_branch,
                    staged_expansion_capture.as_mut(),
                    proof_site.as_ref(),
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
                current = continuation;
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
                let Some((then_steps, else_steps)) =
                    expanded_execution_if_steps(condition, then_branch, else_branch)
                else {
                    return Ok(None);
                };
                proof = proof.with_execution_tactic_index(*index)?;
                proof = proof.apply_expanded_execution_if(condition, &then_steps, &else_steps)?;
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
        return Ok(None);
    }
    for indexed in remaining {
        check_verification_deadline()?;
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

fn solve_nested_have<'a>(
    nested: ProofScope<'a>,
    have: &ProofHave,
    authoritative: bool,
) -> Result<Option<ProofScope<'a>>, ClickError> {
    let selected = match &have.proof {
        SourceProof::Default | SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => {
            nested.try_simp_closure()?
        }
        SourceProof::Script(body) => {
            if authoritative {
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

/// Advances one sibling arm of an in-`Proof` execution split through its
/// linear source tactics, on a proof focused at that arm's recorded goal.
/// Every operation is the ordinary focused `Proof` form; the split record
/// supplies only the stop-at-continuation boundary for source steps.
fn advance_focused_execution_arm<'a>(
    mut proof: Proof<'a>,
    record: &ExecutionSplit<'a>,
    tactics: &[IndexedTactic],
) -> Result<Option<Proof<'a>>, ClickError> {
    for indexed in tactics {
        if let Some(step) = linear_execution_simple_step(&indexed.tactic) {
            proof.ensure_focused_arm_step(record, &step)?;
            proof = proof.apply_step(step)?;
        } else if matches!(indexed.tactic, ProofTactic::SmartStep) {
            proof.ensure_focused_arm_can_advance(record)?;
            let Some(next) = proof.try_indexed_execute_step()? else {
                return Ok(None);
            };
            proof = next;
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
            proof = next;
        } else if let ProofTactic::Transport { source, target } = &indexed.tactic {
            if proof.is_at_function_exit() {
                return Ok(None);
            }
            let Some(next) = proof.try_execution_fact_transport(source, target)? else {
                return Ok(None);
            };
            proof = next;
        } else if let ProofTactic::Have(have) = &indexed.tactic {
            let nested = proof.begin_have(have.proposition.clone())?;
            let Some(nested) = solve_nested_have(nested, have, false)? else {
                return Ok(None);
            };
            proof = nested.join()?;
        } else if matches!(
            indexed.tactic,
            ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths
        ) {
            let Some(next) = proof.try_focused_execute_to_exit()? else {
                return Ok(None);
            };
            proof = next;
        } else {
            return Ok(None);
        }
    }
    Ok(Some(proof))
}

/// Advances the supported structural grammar of one checked execution arm.
/// Nested branches recurse through the same typed split/arm/join helper; the
/// enclosing split record remains only the checked stop boundary for linear
/// source steps.
fn advance_focused_execution_region<'a>(
    mut proof: Proof<'a>,
    enclosing_record: &ExecutionSplit<'a>,
    region: &InternalProofNode,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
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
            let Some(advanced) = advance_focused_execution_arm(proof, enclosing_record, tactics)?
            else {
                return Ok(None);
            };
            advance_focused_execution_region(
                advanced,
                enclosing_record,
                continuation,
                expansion_capture,
                proof_site,
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
            proof.ensure_focused_arm_can_advance(enclosing_record)?;
            let owner = proof.clone();
            let Some((nested, _, certificate)) = try_advance_checked_execution_branch(
                proof,
                *index,
                ensuring,
                then_branch,
                else_branch,
                expansion_capture.as_deref_mut(),
                proof_site,
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
                continuation,
                expansion_capture,
                proof_site,
                depth + 1,
            )
        }
        InternalProofNode::Open { .. } | InternalProofNode::If { .. } => Ok(None),
    }
}

/// Applies one supported two-arm execution branch entirely through the typed
/// Proof split/join API. Callers may choose different source-driving
/// boundaries, but branch entry, arm advancement, interface checking, and the
/// semantic join have one implementation.
fn try_advance_checked_execution_branch<'a>(
    proof: Proof<'a>,
    tactic_index: usize,
    ensuring: &Option<Vec<ProofAssertion>>,
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    depth: usize,
) -> Result<Option<(Proof<'a>, bool, Option<ProofCertificate>)>, ClickError> {
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
            &record,
            region,
            expansion_capture.as_deref_mut(),
            proof_site,
            depth + 1,
        )?
        else {
            return Ok(None);
        };
        advanced = next;
    }
    let empty = checked_execution_region_is_empty(then_branch)
        && checked_execution_region_is_empty(else_branch);
    let joined = advanced.join_focused_execution_split(&record, empty, ensuring.clone())?;
    let certificate = proof_site
        .is_some()
        .then(|| joined.certificate_since(&checkpoint))
        .transpose()?;
    Ok(Some((joined, has_sole_feasible_arm, certificate)))
}

fn linear_execution_steps(node: &InternalProofNode) -> Option<Vec<SimpleProofStep>> {
    linear_execution_tactics(node)?
        .iter()
        .map(|indexed| linear_execution_simple_step(&indexed.tactic))
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

/// Advances a linear resource scope one checked node at a time. A nested
/// `have` is joined back through the scope API, so its selected theorem steps
/// and its published proposition are retained by the same immutable proof.
fn advance_linear_open_scope<'a>(
    mut scope: ProofScope<'a>,
    tactics: &[IndexedTactic],
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
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
            if let Some(site) = proof_site {
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
            if let Some(site) = proof_site {
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
            if let Some(site) = proof_site {
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
            if let Some(site) = proof_site {
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
            if let Some(site) = proof_site {
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
            if let Some(site) = proof_site {
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
) -> Result<Option<ProofScope<'a>>, ClickError> {
    if matches!(body, InternalProofNode::Done) {
        return Ok(Some(scope));
    }
    if let Some(tactics) = linear_execution_tactics(body) {
        return advance_linear_open_scope(scope, tactics, expansion_capture, proof_site);
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
        )?
        else {
            return Ok(None);
        };
        return advance_checked_open_scope(scope, continuation, expansion_capture, proof_site);
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
    {
        let scope = scope.apply_expanded_execution_if(condition, &then_steps, &else_steps)?;
        return advance_checked_open_scope(scope, continuation, expansion_capture, proof_site);
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
        return advance_checked_open_scope(scope, continuation, expansion_capture, proof_site);
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
    let Some((then_tactics, else_tactics)) = linear_execution_branch_pair(then_branch, else_branch)
    else {
        return Ok(None);
    };
    let (split, record) = scope.split_execution_branch()?;
    if ensuring
        .as_ref()
        .is_some_and(|_| !record.supports_interface_branch())
    {
        return Ok(None);
    }
    let empty = then_tactics.is_empty() && else_tactics.is_empty();
    let mut advanced = split;
    for (take_then, tactics) in [(true, then_tactics), (false, else_tactics)] {
        if record.arm_id(take_then).is_none() {
            continue;
        }
        let Some(next) = advance_focused_execution_arm(
            advanced.focus_split_arm(&record, take_then)?,
            &record,
            tactics,
        )?
        else {
            return Ok(None);
        };
        advanced = next;
    }
    let scope = scope.join_execution_split(&advanced, &record, empty, ensuring.clone())?;
    advance_checked_open_scope(scope, continuation, expansion_capture, proof_site)
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
                // surface record. Cross-context synthesis reassembles the
                // whole-claim certificate at exactly these recorded choices,
                // so the tactics a case runs are written inside its surface
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
