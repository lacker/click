use super::*;
use std::sync::Arc;

/// The goal one loop-entry invariant certificate must discharge.
///
/// The entry obligation lowering hands back may be wrapped in leading
/// implications: path guards and lowering-inserted loadability or definedness
/// guards. An antecedent that is exactly one of the available facts is already
/// discharged, so it is stripped. Every other antecedent stays in the goal and
/// the certificate must introduce it explicitly.
///
/// Planning and independent validation both derive their goal here, so a
/// retained certificate is always checked against the goal it was built for.
/// Deciding "already known" with a prover on one side and exact containment on
/// the other is what this function replaces.
pub(in crate::surface::proof) fn loop_entry_checked_goal(
    obligation: &Proposition,
    available: &[Proposition],
) -> Proposition {
    let facts = crate::kernel::proof::ProofFacts::from_ordered(available);
    let mut goal = obligation.clone();
    while let Proposition::Implies(antecedent, body) = &goal {
        if !facts.contains(antecedent) {
            break;
        }
        let stripped = body.as_ref().clone();
        goal = stripped;
    }
    goal
}

/// The kernel form the surface invariant itself denotes inside a checked goal
/// that still carries leading guards.
///
/// Lowering wraps an entry obligation in implications that have no Surface
/// connective: path guards and loadability or definedness premises. The
/// certificate introduces those with `intro`, which keeps the written Surface
/// goal focused, and the surface proposition map records the same pairing. A
/// Surface goal that does write an implication keeps its antecedent, so a
/// written antecedent is never paired away.
fn invariant_lowering_under_guards<'a>(
    surface: &ClickProposition,
    goal: &'a Proposition,
) -> &'a Proposition {
    if matches!(surface, ClickProposition::Implies(_, _)) {
        return goal;
    }
    let mut goal = goal;
    while let Proposition::Implies(_, body) = goal {
        goal = body;
    }
    goal
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn verify_loop_initialization_pure_proof(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    loop_index: usize,
    proof: &SourceProof,
    clause: &StructuralClause,
    context: &PlanningExecutionContext,
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
    let mut recorded_snapshots = context.recorded_snapshots.clone();
    recorded_snapshots.insert(
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
        recorded_snapshots.insert(
            ProgramPointRef {
                region: CodeRegionRef::Label(label.to_string()),
                kind: ProgramPointKind::Entry,
            },
            context.state.clone(),
        );
    }
    let invariant_items = clause.items().iter().collect::<Vec<_>>();
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
    // surface-certificate shape on the next verification pass and check it
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
                            if item.proposition() == &have.proposition
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
                let proposition = item.proposition();
                let invariant_claim_label =
                    format!("{claim_label} (loop {loop_index} invariant {invariant_index} entry)");
                let obligation_context =
                    format!("loop {loop_index} invariant {invariant_index} entry");
                let exact_expected_goal = entry_obligations
                    .iter()
                    .find(|obligation| obligation.context() == Some(&obligation_context))
                    .map(|obligation| obligation.proposition().clone());
                let checked_goal = exact_expected_goal
                    .as_ref()
                    .map(|obligation| loop_entry_checked_goal(obligation, &planning_available));
                // Planning an invariant's entry proof is proof search, not
                // check. Classify it by the `by` clause the search is
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
                    plan_fixed_state_pure_goal_certificate(
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
                        &recorded_snapshots,
                        environment.predicate_environment,
                        environment.click_function_environment,
                        &context.surface_propositions,
                        checked_goal.as_ref(),
                        checked_goal.as_ref(),
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
                    .record_lowering(
                        proposition,
                        invariant_lowering_under_guards(proposition, &planned_fact),
                    )?;
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
            let mut certificate_available = context.pure_facts.clone();
            let invariant_start = certificate.to_proof_tactics().len() - invariant_items.len();
            for (certificate_index, tactic) in certificate.to_proof_tactics().iter().enumerate() {
                // Certificate validation for the initialize phase never reaches
                // the checked drivers' tactic loop, so time each step here in
                // the same format and let `source_site_kind` classify it.
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
                    certificate_available = unfold_available_predicate_facts(
                        environment.predicate_environment,
                        environment.click_function_environment,
                        std::slice::from_ref(name),
                        &certificate_available,
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
                    let proposition = invariant_items[invariant_index].proposition();
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
                // Check structured initialization through the same checked
                // proof object that emitted it, including both/and children.
                let exact_entry_goal = invariant_index
                    .and_then(|index| {
                        let obligation_context =
                            format!("loop {loop_index} invariant {index} entry");
                        entry_obligations
                            .iter()
                            .find(|obligation| obligation.context() == Some(&obligation_context))
                            .map(|obligation| obligation.proposition().clone())
                    })
                    .map(|obligation| loop_entry_checked_goal(&obligation, &certificate_available));
                let fact = exact_entry_goal
                    .or_else(|| {
                        surface_propositions
                            .unique_kernel(&have.proposition)
                            .cloned()
                    })
                    .map(Ok)
                    .unwrap_or_else(|| {
                        lower_fixed_state_proposition(
                            &have.proposition,
                            &certificate_available,
                            environment.parsed_function.parameters(),
                            environment.arguments,
                            environment.initial_state,
                            &context.state,
                            None,
                            &recorded_snapshots,
                            environment.predicate_environment,
                            environment.click_function_environment,
                        )
                    })
                    .map_err(ClickError::new)?;
                let root = Proof::for_fixed_state_surface_goal(
                    &step_claim_label,
                    certificate_index,
                    &certificate_available,
                    fact.clone(),
                    have.proposition.clone(),
                    environment.parsed_function.parameters(),
                    environment.arguments,
                    environment.initial_state,
                    &context.state,
                    &recorded_snapshots,
                    &surface_propositions,
                    environment.predicate_environment,
                    environment.click_function_environment,
                    environment.theorem_environment,
                    &[],
                    &[],
                );
                let SourceProof::Script(tactics) = &have.proof else {
                    return Err(ClickError::new(
                        "invariant initialization requires an explicit proof body",
                    ));
                };
                let checked = root.try_authoritative_linear_script(tactics)?;
                if !checked.is_some_and(|proof| proof.is_complete()) {
                    return Err(ClickError::new(
                        "invariant initialization proof body did not close its goal",
                    ));
                }
                if !certificate_available.contains(&fact) {
                    certificate_available.push(fact);
                }
            }
            Ok(certificate_available)
        },
    )?;
    let assumptions = assumptions_from_propositions(&available);
    c_loop_invariants_hold_at_entry(&context.state, invariant_checks, &assumptions)
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
    Ok(certificate)
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn plan_automatic_loop_preservation_body(
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
    let frontier = ExecutionFrontier {
        position: FrontierPosition::StatementEntry {
            remaining: body.clone().into(),
        },
        region: ExecutionRegionKind::LoopBody,
        execution_start_state: Some(preservation.state().clone()),
        next_statement_index: loop_body_statement_index,
        ..ExecutionFrontier::default()
    };
    let mut recorded_snapshots = RecordedSnapshots::new();
    let constants = ExecutionProofConstants {
        proof_site: environment
            .frontier_loop_source
            .and_then(|source| source.proof_site.clone()),
        source_layout,
        function_entry_state: Some(environment.initial_state.clone()),
        ..ExecutionProofConstants::default()
    };
    record_statement_program_snapshot_state(
        &mut recorded_snapshots,
        environment.function_block,
        loop_body_statement_index,
        ProgramPointKind::Entry,
        preservation.state().clone(),
    );
    record_loop_program_snapshot_state(
        &mut recorded_snapshots,
        environment.function_block,
        loop_index,
        ProgramPointKind::Entry,
        preservation.loop_entry_state().clone(),
    );
    let root = Proof::for_execution_frontier(
        &claim_label,
        0,
        ExecutionProofState::at_entry(
            preservation.state().clone(),
            frontier,
            recorded_snapshots,
            environment.surface_propositions.clone(),
            PersistentSequence::default(),
        ),
        pure_facts.to_vec(),
        constants.clone(),
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
    let mut pending = vec![root];
    let mut completed = Vec::new();
    let mut steps = 0;
    while let Some(proof) = pending.pop() {
        if proof.is_at_region_boundary() {
            completed.push(proof);
            continue;
        }
        if steps == BOUNDED_EXECUTE_STEP_LIMIT {
            return Err(ClickError::new(format!(
                "`{claim_label}` automatic preservation exhausted its {BOUNDED_EXECUTE_STEP_LIMIT}-step budget"
            )));
        }
        steps += 1;
        let view = proof.execution_view()?;
        let is_branch = view
            .context
            .constants
            .source_layout
            .statement(view.frontier.next_statement_index)
            .is_some_and(|region| matches!(region.kind, SourceStatementKind::If { .. }));
        if is_branch {
            let FrontierPosition::StatementEntry { remaining } = &view.frontier.position else {
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
            let condition = surface_c_condition(&condition);
            let (split, ids) = proof.split_preservation_case(&condition, 0)?;
            for id in ids.into_iter().flatten() {
                pending.push(preservation_smart_step(split.focus_branch(id)?)?);
            }
        } else {
            pending.push(preservation_smart_step(proof)?);
        }
    }
    let mut paths = Vec::new();
    for leaf in completed {
        let context_execution = leaf.execution_view()?.execution.clone();
        if let Some(blocker) = &context_execution.presentation.surface_record.blocker {
            return Err(ClickError::new(format!(
                "`{claim_label}` automatic preservation could not lower a body step: {blocker}"
            )));
        }
        let case_path = context_execution
            .presentation
            .case_assumptions
            .iter()
            .map(|choice| ProofCaseChoice {
                condition: choice.condition.clone(),
                value: choice.value,
            })
            .collect::<Vec<_>>();
        let surface_tactics = leaf.path_certificate()?.to_proof_tactics();
        let (certificate, selected_offsets) =
            certificate_leaf_for_case_path(&claim_label, &surface_tactics, &case_path)?;
        let case_offsets = selected_offsets
            .or_else(|| recorded_case_offsets(&context_execution.presentation, case_path.len()));
        paths.push(PathCertificate {
            case_path,
            case_offsets,
            certificate,
        });
    }
    merge_path_aligned_certificates(&claim_label, paths)
}

pub(in crate::surface::proof) struct LoopPreservationProofResult {
    pub(in crate::surface::proof) certificate: ProofCertificate,
    pub(in crate::surface::proof) final_exit_candidates: Vec<CLoopFinalExitCandidate>,
    /// Loop rules checked by frontier-local tactics inside this loop's
    /// preservation proof. They are evidence for termination only; the
    /// enclosing contract still uses the outer loop's checked artifact.
    pub(in crate::surface::proof) nested_loop_rules: Vec<CVerifiedLoopRule>,
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn verify_one_loop_preservation_proof(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    loop_index: usize,
    tactics: &[ProofTactic],
    first_generated_tactic_index: usize,
    preservation: &crate::kernel::CLoopPreservationContext,
    pure_facts: &[Proposition],
    invariant_checks: &[CLoopInvariantCheck],
    ranking_measures: &[CExpression],
    condition: &CExpression,
    body: &CStatement,
    do_while: bool,
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
        // Detach them so a later nested clause cannot be mistaken for one of
        // these generated tactics by expand.
        detach_generated_suffix_from_source_indices(&mut program, first_generated_tactic_index);
    }
    let source_layout = SourceExecutionLayout::new(environment.parsed_function.body());
    let loop_body_statement_index = source_layout.loop_body_entry(loop_index).ok_or_else(|| {
        ClickError::new(format!("`{claim_label}` has no source loop({loop_index})"))
    })?;
    let frontier = ExecutionFrontier {
        position: FrontierPosition::StatementEntry {
            remaining: body.clone().into(),
        },
        region: ExecutionRegionKind::LoopBody,
        execution_start_state: Some(preservation.state().clone()),
        next_statement_index: loop_body_statement_index,
        ..ExecutionFrontier::default()
    };
    let mut recorded_snapshots = RecordedSnapshots::new();
    let constants = ExecutionProofConstants {
        proof_site: Some(preserve_site),
        invariant_body_context: Some(Arc::new(InvariantBodyContext {
            loop_entry_state: preservation.loop_entry_state().clone(),
            iteration_entry_state: preservation.state().clone(),
            iteration_entry_selector: Some(SnapshotSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Statement(loop_body_statement_index),
                kind: ProgramPointKind::Entry,
            })),
            checks: invariant_checks.to_vec(),
            ranking_measures: ranking_measures.to_vec(),
        })),
        source_layout,
        function_entry_state: Some(environment.initial_state.clone()),
        ..ExecutionProofConstants::default()
    };
    let mut surface_propositions = environment.surface_propositions.clone();
    record_statement_program_snapshot_state(
        &mut recorded_snapshots,
        environment.function_block,
        loop_body_statement_index,
        ProgramPointKind::Entry,
        preservation.state().clone(),
    );
    record_code_region_program_snapshot_state(
        &mut recorded_snapshots,
        environment.function_block,
        CodeRegion::Loop(loop_index),
        ProgramPointKind::Entry,
        preservation.loop_entry_state().clone(),
    );
    // The invariants are available at the body entry as kernel facts. A
    // pre-tested loop also has its condition there; a do-while does not, so
    // it must not be recorded as an available premise for the first body.
    let loop_condition = surface_c_condition(condition);
    let invariant_surfaces = environment
        .function_block
        .structural_clauses()
        .iter()
        .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
        .flat_map(StructuralClause::items)
        .map(StructuralItem::proposition);
    {
        let surfaces = if do_while {
            invariant_surfaces
                .chain(std::iter::empty())
                .collect::<Vec<_>>()
        } else {
            invariant_surfaces
                .chain(std::iter::once(&loop_condition))
                .collect::<Vec<_>>()
        };
        for surface in surfaces {
            if let Ok(lowered) = lower_fixed_state_proposition(
                surface,
                pure_facts,
                environment.parsed_function.parameters(),
                environment.arguments,
                environment.initial_state,
                preservation.state(),
                None,
                &recorded_snapshots,
                environment.predicate_environment,
                environment.click_function_environment,
            ) {
                let surface = surface_at_snapshot(
                    surface,
                    &ProgramPointRef {
                        region: CodeRegionRef::Statement(loop_body_statement_index),
                        kind: ProgramPointKind::Entry,
                    },
                )?;
                surface_propositions.record_lowering(&surface, &lowered)?;
            }
        }
    }
    let proof_site_for_driver = constants.proof_site.clone();
    let owning_source_index = if environment
        .frontier_loop_source
        .is_some_and(|source| source.preserve_source_index.is_none())
    {
        preserve_source_index
    } else {
        usize::MAX
    };
    let root = Proof::for_execution_frontier(
        &claim_label,
        internal_proof_first_index(&program).unwrap_or(0),
        ExecutionProofState::at_entry(
            preservation.state().clone(),
            frontier,
            recorded_snapshots,
            surface_propositions,
            PersistentSequence::default(),
        ),
        pure_facts.to_vec(),
        constants.clone(),
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
    let mut leaves = Vec::new();
    advance_preservation_region(
        root,
        &program,
        &[],
        expansion_capture.as_deref_mut(),
        proof_site_for_driver.as_ref(),
        owning_source_index,
        &claim_label,
        &mut leaves,
    )?;
    let invariant_surfaces = environment
        .function_block
        .structural_clauses()
        .iter()
        .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
        .flat_map(StructuralClause::items)
        .map(|item| item.proposition().clone())
        .collect::<Vec<_>>();
    let invariant_premise_surfaces = invariant_surfaces
        .iter()
        .map(|surface| {
            surface_at_snapshot(
                surface,
                &ProgramPointRef {
                    region: CodeRegionRef::Statement(loop_body_statement_index),
                    kind: ProgramPointKind::Entry,
                },
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut certificate_paths = Vec::new();
    let mut final_exit_candidates = Vec::new();
    let mut nested_loop_rules = Vec::new();
    for leaf in leaves {
        let context_execution = leaf.execution_view()?.execution.clone();
        for rule in context_execution.core.frontier_loop_rules.iter() {
            if !nested_loop_rules
                .iter()
                .any(|existing: &CVerifiedLoopRule| existing == rule)
            {
                nested_loop_rules.push(rule.clone());
            }
        }
        let context_frontier = leaf.execution_view()?.frontier.clone();
        let case_path = context_execution
            .presentation
            .case_assumptions
            .iter()
            .map(|choice| ProofCaseChoice {
                condition: choice.condition.clone(),
                value: choice.value,
            })
            .collect::<Vec<_>>();
        let source_tactics = leaf.path_certificate()?.to_proof_tactics();
        let region_simp = context_execution.presentation.region_simp;
        let proof_site = leaf.execution_view()?.context.constants.proof_site.clone();
        let invariants_close_requested = context_execution.core.region_invariants_close_requested;
        let has_retained_invariant_body =
            context_execution.core.checked_invariant_lowerings.is_some();
        let statement_index = context_frontier.next_statement_index;
        let (closer_index, closer_source, closer_name, closer_class) =
            if let Some(step) = context_execution.presentation.invariant_closer_step {
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
        let bundle_checkpoint = leaf.checkpoint();
        // A region-level `simp` is a Surface planner. Establish each named
        // invariant through the checked proposition Proof before asking the
        // kernel to close the bundle. In particular, upper-bound extension
        // now becomes a nested proof `if` here instead of recursive search in
        // proposition reasoning.
        let mut leaf = leaf;
        if has_retained_invariant_body {
            // A completed body is bound to this exact premise store. Validate
            // it before skipping preplanning; a source close request alone
            // is not evidence. Adding further `have`s would stale the body.
            leaf.validate_loop_invariant_bundle(invariant_checks, ranking_measures)?;
        } else if region_simp.is_some() {
            if invariant_surfaces.len() != invariant_checks.len() {
                return Err(leaf.step_error(
                    "surface invariants do not align with the lowered invariant bundle",
                ));
            }
            for (index, invariant) in invariant_surfaces.iter().enumerate() {
                let scope = leaf.begin_have(invariant.clone())?;
                let Some(proved) =
                    scope.try_simp_closure_with_surfaces(&invariant_premise_surfaces[..=index])?
                else {
                    continue;
                };
                leaf = proved.join()?;
            }
        }
        let checked = if invariant_checks.is_empty() && ranking_measures.is_empty() {
            leaf.check_loop_state_join(
                preservation.loop_entry_state(),
                preservation.state(),
                condition,
                &[],
                environment.function.composite_resource_definitions(),
            )
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` (loop {loop_index} state join): {}",
                    error.message()
                ))
            })?;
            leaf.clone()
        } else {
            leaf.prepare_loop_invariant_bundle(
                preservation.loop_entry_state(),
                preservation.state(),
                condition,
                invariant_checks,
                ranking_measures,
                &invariant_surfaces,
                environment.function.composite_resource_definitions(),
                do_while,
            )
            .and_then(|prepared| match prepared {
                Some(proof) => {
                    proof.certify_loop_invariant_bundle(invariant_checks, ranking_measures)
                }
                // A do-while exit has no continuing back edge to certify.
                None => Ok(leaf.clone()),
            })
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` (loop {loop_index} invariant bundle preservation): {}",
                    error.message()
                ))
            })?
        };
        let mut join_facts = checked.facts().to_vec();
        let checked_execution = checked.execution_view()?.execution.clone();
        join_facts.extend(
            checked_execution
                .core
                .effect_facts
                .iter()
                .map(|fact| fact.proposition().clone()),
        );
        join_facts.extend(crate::kernel::certified_store_equations(
            &checked_execution.core.effect_facts,
        ));
        // The body must return to the head it started from, which carries the
        // loop's own resource context when the loop declares one.
        if crate::kernel::c_loop_state_components_match_at_back_edge(
            preservation.state(),
            &checked_execution.core.state,
            &assumptions_from_propositions(&join_facts),
            environment.function.composite_resource_definitions(),
        )
        .is_err()
        {
            let candidate = CLoopFinalExitCandidate::new(
                (*checked_execution.core.state).clone(),
                checked.facts().to_vec(),
            );
            if !final_exit_candidates.contains(&candidate) {
                final_exit_candidates.push(candidate);
            }
        }
        let closer_tactics = if (invariant_checks.is_empty() && ranking_measures.is_empty())
            || invariants_close_requested
        {
            Vec::new()
        } else {
            checked
                .certificate_since(&bundle_checkpoint)?
                .to_proof_tactics()
                .to_vec()
        };
        let omitted_frontier_preservation = environment
            .frontier_loop_source
            .is_some_and(|source| source.preserve_source_index.is_none());
        if !omitted_frontier_preservation
            && region_simp.is_some_and(|(_, source_index)| {
                // Region simp is deferred by the preservation driver, so it
                // never opens an active tactic capture. Match its selected
                // source occurrence just as the driver's explicit steps do.
                proof_site.as_ref().is_some_and(|site| {
                    selected_tactic_index_for_site(expansion_capture.as_deref(), site)
                        == Some(source_index)
                })
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
        let (prefix, selected_offsets) =
            certificate_leaf_for_case_path(&claim_label, &source_tactics, &case_path)?;
        let case_offsets = selected_offsets
            .or_else(|| recorded_case_offsets(&context_execution.presentation, case_path.len()));
        let mut leaf_tactics = prefix.to_proof_tactics().to_vec();
        leaf_tactics.extend(closer_tactics);
        let certificate = ProofCertificate::from_proof_tactics(&leaf_tactics).map_err(|error| {
            ClickError::new(format!(
                "`{claim_label}` produced an invalid preservation leaf certificate: {error:?}"
            ))
        })?;
        certificate_paths.push(PathCertificate {
            case_path: case_path.clone(),
            case_offsets,
            certificate,
        });
    }
    let certificate = merge_path_aligned_certificates(&claim_label, certificate_paths)?;
    Ok(LoopPreservationProofResult {
        certificate,
        final_exit_candidates,
        nested_loop_rules,
    })
}

#[cfg(test)]
mod loop_entry_goal_tests {
    use super::*;

    fn variable_is_zero(variable: u64) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(Variable(variable))),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        )
    }

    #[test]
    fn only_exactly_available_leading_antecedents_are_stripped() {
        let first = variable_is_zero(1);
        let second = variable_is_zero(2);
        let conclusion = variable_is_zero(3);
        let obligation = Proposition::Implies(
            Box::new(first.clone()),
            Box::new(Proposition::Implies(
                Box::new(second.clone()),
                Box::new(conclusion.clone()),
            )),
        );

        assert_eq!(loop_entry_checked_goal(&obligation, &[]), obligation);
        // A second antecedent is only reachable once the first one is gone:
        // stripping stops at the first antecedent that is not exactly available.
        assert_eq!(
            loop_entry_checked_goal(&obligation, std::slice::from_ref(&second)),
            obligation
        );
        assert_eq!(
            loop_entry_checked_goal(&obligation, std::slice::from_ref(&first)),
            Proposition::Implies(Box::new(second.clone()), Box::new(conclusion.clone()))
        );
        assert_eq!(
            loop_entry_checked_goal(&obligation, &[first, second]),
            conclusion
        );
    }
}
