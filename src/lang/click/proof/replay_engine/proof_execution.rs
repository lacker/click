use super::*;

fn linear_execution_simple_step(tactic: &ProofTactic) -> Option<SimpleProofStep> {
    // `frame()` is source sugar for the smart frame search even though the
    // surface certificate parser can represent its empty form as a
    // `FrameUsing`. Keep the source operation on the smart branch so mutable
    // effects can select and retain their contextual premises.
    if matches!(tactic, ProofTactic::SmartFrame(_)) {
        return None;
    }
    let certificate = ProofCertificate::from_proof_tactics(std::slice::from_ref(tactic)).ok()?;
    let [step] = certificate.steps() else {
        return None;
    };
    matches!(
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
            | SimpleProofStep::FrameUsing { .. }
            | SimpleProofStep::CloseInvariants
    )
    .then(|| step.clone())
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

fn linear_execution_branch_tactics(node: &InternalProofNode) -> Option<&[IndexedTactic]> {
    let tactics = linear_execution_tactics(node)?;
    (tactics.iter().enumerate().all(|(index, indexed)| {
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
    }))
    .then_some(tactics)
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
    let ends_at_exit = |tactics: &[IndexedTactic]| {
        tactics.last().is_some_and(|indexed| {
            matches!(
                indexed.tactic,
                ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths
            )
        })
    };
    (ends_at_exit(then_tactics) == ends_at_exit(else_tactics))
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

/// Whether one flat source script can be checked as a complete execution
/// effect proof before any descendant is published. The terminal frame is
/// load-bearing: it validates the facts retained by the preceding execution
/// search, so a miss can discard the whole candidate and leave the legacy
/// context untouched.
fn checked_terminal_effect_script(tactics: &[IndexedTactic]) -> bool {
    let Some((last, prefix)) = tactics.split_last() else {
        return false;
    };
    matches!(
        last.tactic,
        ProofTactic::SmartFrame(_) | ProofTactic::FrameUsing { .. }
    ) && prefix.iter().any(|indexed| {
        matches!(
            indexed.tactic,
            ProofTactic::SmartExecute
                | ProofTactic::SmartExecuteAllPaths
                | ProofTactic::ExecuteUntil(_)
        )
    }) && tactics
        .iter()
        .all(|indexed| checked_linear_continuation_tactic(&indexed.tactic))
}

fn linear_terminal_frame_prefix(node: &InternalProofNode) -> Option<&IndexedTactic> {
    linear_execution_tactics(node)?.first().filter(|indexed| {
        matches!(
            indexed.tactic,
            ProofTactic::SmartFrame(_) | ProofTactic::FrameUsing { .. }
        )
    })
}

/// Selects a branch only when any later frame is reachable through operations
/// already represented by the checked linear continuation driver. Otherwise
/// exporting a partially migrated terminal outcome would hand its ownership
/// back to the legacy frame path.
fn exportable_linear_execution_branch_pair<'a>(
    then_branch: &'a InternalProofNode,
    else_branch: &'a InternalProofNode,
    continuation: &InternalProofNode,
) -> Option<(&'a [IndexedTactic], &'a [IndexedTactic])> {
    let pair = linear_execution_branch_pair(then_branch, else_branch)?;
    if internal_proof_contains_frame(continuation)
        && !checked_linear_continuation_reaches_frame(continuation)
    {
        return None;
    }
    Some(pair)
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
    allow_contextual_frame: bool,
) -> Result<Option<(Proof<'a>, Vec<IndexedTactic>)>, ClickError> {
    let Some(tactics) = linear_execution_tactics(continuation) else {
        return Ok(None);
    };
    for (offset, indexed) in tactics.iter().enumerate() {
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
        let checkpoint = proof.checkpoint();
        let next = if let Some(step) = linear_execution_simple_step(&indexed.tactic) {
            if let SimpleProofStep::FrameUsing { region, premises } = &step
                && !proof.supports_checked_frame_using(region.as_ref(), premises)?
            {
                return Ok(None);
            }
            proof.apply_step_at(step, indexed.index, indexed.source_index)?
        } else if matches!(indexed.tactic, ProofTactic::SmartStep) {
            let Some(stepped) = proof.try_smart_step()? else {
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
            let Some(selected) = solve_nested_have(nested, have)? else {
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
        // Generated certificates retain the source index of the smart
        // operation that produced them. Their nested steps are part of that
        // operation's already-recorded branch certificate, not independent
        // expansions of the same source occurrence.
        if indexed.source_index != owning_source_index
            && let Some(site) = proof_site
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

/// Tries a complete flat execution/effect script on one immutable Proof.
///
/// Search may inspect and fork the Proof, but every accepted statement and
/// frame advances through its ordinary checked operation. Nothing is exported
/// unless the terminal frame closes the selected effect goal; a miss therefore
/// preserves the original replay context for compatibility diagnostics.
#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn try_execute_checked_terminal_effect_script<'a>(
    context: &ProofReplayContext,
    tactics: &[IndexedTactic],
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
) -> Result<Option<ProofReplayContext>, ClickError> {
    if !checked_terminal_effect_script(tactics) {
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
    let checkpoint = root.checkpoint();
    let linear = InternalProofNode::Linear {
        tactics: tactics.to_vec(),
        continuation: Box::new(InternalProofNode::Done),
    };
    let Some((proof, remaining)) = advance_checked_linear_continuation(
        root,
        &linear,
        expansion_capture,
        context.replay.proof_site.as_ref(),
        usize::MAX,
        true,
    )?
    else {
        return Ok(None);
    };
    if !remaining.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` checked terminal effect script left an unexpected source suffix"
        )));
    }
    let certificate = proof.certificate_since(&checkpoint)?;
    let mut checked = proof.into_execution_context()?;
    for step in certificate.steps() {
        checked
            .replay
            .proof_certificate_builder
            .push_step(step.clone());
    }
    Ok(Some(checked))
}

fn solve_nested_have<'a>(
    nested: ProofScope<'a>,
    have: &ProofHave,
) -> Result<Option<ProofScope<'a>>, ClickError> {
    let selected = match &have.proof {
        SourceProof::Default | SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => {
            nested.try_simp_closure()?
        }
        SourceProof::Script(body) => {
            if let Some(selected) = nested.try_linear_smart_script(body)? {
                Some(selected)
            } else if let Ok(certificate) = ProofCertificate::from_proof_tactics(body) {
                nested.apply_candidate_certificate(&certificate).ok()
            } else {
                None
            }
        }
        SourceProof::Tactic(SmartTactic::Frame) => None,
    };
    Ok(selected)
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
            let Some(nested) = solve_nested_have(nested, have)? else {
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

fn linear_execution_certificate(node: &InternalProofNode) -> Option<ProofCertificate> {
    let tactics = linear_execution_tactics(node)?
        .iter()
        .map(|indexed| indexed.tactic.clone())
        .collect::<Vec<_>>();
    ProofCertificate::from_proof_tactics(&tactics).ok()
}

/// The checked open driver can participate in expansion capture when the
/// selected source tactic is one of the smart operations for which it can
/// return the exact retained Proof delta. Captures outside this open are
/// unaffected; unsupported captures inside it keep using the legacy driver.
fn checked_open_scope_can_service_capture(
    body: &InternalProofNode,
    capture: Option<&ExpansionCapture>,
    proof_site: Option<&ProofSite>,
) -> bool {
    let Some(site) = proof_site else {
        return capture.is_none();
    };
    let Some(wanted) = selected_tactic_index_for_site(capture, site) else {
        return true;
    };
    if !internal_proof_contains_source_index(body, wanted) {
        return true;
    }
    linear_execution_tactics(body).is_some_and(|tactics| {
        tactics.iter().any(|indexed| {
            indexed.source_index == wanted
                && matches!(
                    indexed.tactic,
                    ProofTactic::SmartStep
                        | ProofTactic::ApplyTheorem(_)
                        | ProofTactic::Transport { .. }
                        | ProofTactic::SmartExecute
                        | ProofTactic::SmartExecuteAllPaths
                        | ProofTactic::SmartFrame(_)
                        | ProofTactic::ExecuteUntil(_)
                )
        })
    })
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
        let selected = solve_nested_have(nested, have)?;
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
        && let Some(then_proof) = linear_execution_certificate(then_branch)
        && let Some(else_proof) = linear_execution_certificate(else_branch)
        && ((matches!(
            then_proof.steps().last(),
            Some(SimpleProofStep::StepUsing(_))
        ) && matches!(
            else_proof.steps().last(),
            Some(SimpleProofStep::StepUsing(_))
        )) || (then_proof.steps().is_empty()
            && matches!(
                else_proof.steps().last(),
                Some(SimpleProofStep::StepUsing(_))
            ))
            || (else_proof.steps().is_empty()
                && matches!(
                    then_proof.steps().last(),
                    Some(SimpleProofStep::StepUsing(_))
                )))
    {
        let checkpoint = scope.checkpoint();
        let (split, record) = scope.split_execution_branch()?;
        let mut advanced = split;
        if let Some(take_then) = record.sole_feasible_arm() {
            let (selected, impossible) = if take_then {
                (&then_proof, &else_proof)
            } else {
                (&else_proof, &then_proof)
            };
            if !impossible.steps().is_empty()
                || !matches!(selected.steps().last(), Some(SimpleProofStep::StepUsing(_)))
            {
                return Ok(None);
            }
            advanced =
                advanced.check_focused_logical_arm_certificate(&record, take_then, selected)?;
        } else {
            if !matches!(
                then_proof.steps().last(),
                Some(SimpleProofStep::StepUsing(_))
            ) || !matches!(
                else_proof.steps().last(),
                Some(SimpleProofStep::StepUsing(_))
            ) {
                return Ok(None);
            }
            advanced =
                advanced.check_focused_logical_arm_certificate(&record, true, &then_proof)?;
            advanced =
                advanced.check_focused_logical_arm_certificate(&record, false, &else_proof)?;
        }
        let scope = scope.join_execution_split(&advanced, &record, false, None)?;
        let actual = scope.certificate_since(&checkpoint)?;
        let expected = ProofCertificate::from_steps(vec![SimpleProofStep::If {
            condition: condition.clone(),
            then_proof: Box::new(then_proof),
            else_proof: Box::new(else_proof),
        }]);
        if actual.steps() != expected.steps() {
            return Err(ClickError::new(
                "expanded execution branch does not match the checked C branch certificate",
            ));
        }
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
        && let Some(then_proof) = linear_execution_certificate(then_branch)
        && let Some(else_proof) = linear_execution_certificate(else_branch)
        && matches!(
            then_proof.steps().last(),
            Some(SimpleProofStep::FrameUsing { region: None, .. })
        )
        && matches!(
            else_proof.steps().last(),
            Some(SimpleProofStep::FrameUsing { region: None, .. })
        )
    {
        let certificate = ProofCertificate::from_steps(vec![SimpleProofStep::If {
            condition: condition.clone(),
            then_proof: Box::new(then_proof),
            else_proof: Box::new(else_proof),
        }]);
        let scope =
            scope.apply_contextual_frame_certificate_at(&certificate, *index, *source_index)?;
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

/// Checks one supported `open` body on the same Proof that owns its entry and
/// close transitions. Kept out of the recursive structural driver frame for
/// the same stack-bound reason as the resource-step adapter.
#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn execute_checked_open_scope<'a>(
    context: ProofReplayContext,
    expansion_capture: Option<&mut ExpansionCapture>,
    resource: ResourceClause,
    source_index: usize,
    body: &InternalProofNode,
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
    let proof_site = context.replay.proof_site.clone();
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
    let scope = root.begin_open(resource, source_index)?;
    let Some(scope) =
        advance_checked_open_scope(scope, body, expansion_capture, proof_site.as_ref())?
    else {
        return Ok(None);
    };
    let proof = scope.join()?;
    let certificate = proof.certificate();
    let mut context = proof.into_execution_context()?;
    for step in certificate.steps() {
        context
            .replay
            .proof_certificate_builder
            .push_step(step.clone());
    }
    Ok(Some(context))
}

#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn try_execute_checked_open_scope<'a>(
    context: &ProofReplayContext,
    expansion_capture: Option<&mut ExpansionCapture>,
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
    execute_checked_open_scope(
        context.clone(),
        expansion_capture,
        resource,
        source_index,
        body,
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
}

#[inline(never)]
#[allow(clippy::too_many_arguments)]
fn try_execute_checked_open_scope_and_continue<'a>(
    context: &ProofReplayContext,
    expansion_capture: Option<&mut ExpansionCapture>,
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
    let Some(context) = try_execute_checked_open_scope(
        context,
        expansion_capture,
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
            if matches!(continuation.as_ref(), InternalProofNode::Done)
                && let Some(checked) = try_execute_checked_terminal_effect_script(
                    &context,
                    tactics,
                    expansion_capture.as_deref_mut(),
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
                )
                .map_err(|error| add_proof_branch_path(error, &branch_path))?
            {
                return Ok(vec![checked]);
            }
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
            let checked_supported = checked_open_scope_can_service_capture(
                body,
                expansion_capture.as_deref(),
                context.replay.proof_site.as_ref(),
            );
            if checked_supported {
                let checked = try_execute_checked_open_scope_and_continue(
                    &context,
                    expansion_capture.as_deref_mut(),
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
                if let Some(contexts) = checked {
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
            source_index,
            ensuring,
            then_branch,
            else_branch,
            continuation,
        } => {
            let selected_source_index = context.replay.proof_site.as_ref().and_then(|site| {
                selected_tactic_index_for_site(expansion_capture.as_deref(), site)
            });
            let capture_in_continuation = selected_source_index
                .is_some_and(|wanted| internal_proof_contains_source_index(continuation, wanted));
            let checked_capture_supported = selected_source_index
                .is_none_or(|wanted| wanted == *source_index || capture_in_continuation);
            if checked_capture_supported
                && let Some((then_tactics, else_tactics)) =
                    exportable_linear_execution_branch_pair(then_branch, else_branch, continuation)
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
                let (split, record) = proof.split_focused_execution_branch()?;
                let feasible_arm = record.sole_feasible_arm();
                let checked_interface_preflight = ensuring
                    .as_ref()
                    .is_none_or(|_| record.supports_interface_branch());
                let empty = then_tactics.is_empty() && else_tactics.is_empty();
                let checked = if checked_interface_preflight {
                    (|| {
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
                        Ok::<_, ClickError>(Some(advanced))
                    })()?
                } else {
                    None
                };
                if let Some(advanced) = checked {
                    let branch_proof =
                        advanced.join_focused_execution_split(&record, empty, ensuring.clone())?;
                    let branch_certificate = branch_proof.certificate_since(&checkpoint)?;
                    let can_advance_continuation = feasible_arm.is_none()
                        || (execution_branch_tactics_end_at_exit(then_tactics)
                            && linear_terminal_frame_prefix(continuation).is_some());
                    let advanced = if can_advance_continuation
                        && linear_execution_tactics(continuation).is_some()
                    {
                        advance_checked_linear_continuation(
                            branch_proof,
                            continuation,
                            expansion_capture.as_deref_mut(),
                            context.replay.proof_site.as_ref(),
                            *source_index,
                            false,
                        )?
                        .map(|(proof, remaining)| {
                            let continuation = if remaining.is_empty() {
                                InternalProofNode::Done
                            } else {
                                InternalProofNode::Linear {
                                    tactics: remaining,
                                    continuation: Box::new(InternalProofNode::Done),
                                }
                            };
                            (proof, Some(continuation))
                        })
                    } else {
                        Some((branch_proof, None))
                    };
                    if let Some((proof, checked_continuation)) = advanced {
                        if !capture_in_continuation
                            && let Some(site) = context.replay.proof_site.as_ref()
                        {
                            record_proof_site_tactic_expansion(
                                expansion_capture.as_deref_mut(),
                                site,
                                *source_index,
                                &branch_certificate.to_proof_tactics(),
                            );
                        }
                        let certificate = proof.certificate_since(&checkpoint)?;
                        let mut joined_context = proof.into_execution_context()?;
                        for (step_index, step) in certificate.steps().iter().enumerate() {
                            if feasible_arm.is_some() && ensuring.is_none() && step_index == 0 {
                                joined_context
                                    .replay
                                    .proof_certificate_builder
                                    .push_decided_step(step.clone());
                            } else {
                                joined_context
                                    .replay
                                    .proof_certificate_builder
                                    .push_step(step.clone());
                            }
                        }
                        return execute_internal_proof(
                            checked_continuation.as_ref().unwrap_or(continuation),
                            joined_context,
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
                        );
                    }
                }
            }
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
