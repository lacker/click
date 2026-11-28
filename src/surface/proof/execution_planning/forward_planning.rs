use super::*;
use crate::surface::expansion::LoopEntryBranches;

pub(in crate::surface::proof) fn verify_execution_proofs_forward(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    statement: &ProgramStatement,
    contexts: Vec<PlanningExecutionContext>,
    next_statement_index: &mut usize,
    next_loop_index: &mut usize,
    environment: &ExecutionProofEnvironment<'_>,
    verified_loop_rules: &mut Vec<VerifiedLoopRule>,
) -> Result<Vec<PlanningExecutionContext>, ClickError> {
    match statement {
        ProgramStatement::Seq(statements) => {
            let mut contexts = contexts;
            for statement in statements.iter() {
                contexts = verify_execution_proofs_forward(
                    expansion_capture.as_deref_mut(),
                    statement,
                    contexts,
                    next_statement_index,
                    next_loop_index,
                    environment,
                    verified_loop_rules,
                )?;
            }
            Ok(contexts)
        }
        ProgramStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let statement_index = *next_statement_index;
            let _site_scope = crate::surface::diagnostics::StatementSiteScope::enter(
                environment.source_layout,
                statement_index,
                environment.parsed_function,
            );
            let source_region = environment
                .source_layout
                .statement(statement_index)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "execution proof traversal could not resolve region({statement_index})"
                    ))
                })?;
            let SourceStatementKind::If {
                then_statement_index,
                else_statement_index,
            } = source_region.kind
            else {
                return Err(ClickError::new(format!(
                    "execution proof traversal expected region({statement_index}) to be an `if`"
                )));
            };
            let mut active = Vec::new();
            let mut bypassed = Vec::new();
            for context in contexts {
                match context.resume_at_statement {
                    Some(target) if target >= source_region.continuation_node => {
                        bypassed.push(context);
                    }
                    Some(target) if target > statement_index => {
                        return Err(ClickError::new(
                            "execution proof traversal found a goto target inside an `if`",
                        ));
                    }
                    Some(_) => {
                        return Err(ClickError::new(
                            "execution proof traversal passed a goto target",
                        ));
                    }
                    None => active.push(context),
                }
            }
            let (then_contexts, else_contexts) =
                split_execution_proof_branch_contexts(condition, active)?;
            *next_statement_index = then_statement_index;
            let mut joined = verify_execution_proofs_forward(
                expansion_capture.as_deref_mut(),
                then_branch,
                then_contexts,
                next_statement_index,
                next_loop_index,
                environment,
                verified_loop_rules,
            )?;
            *next_statement_index = else_statement_index;
            joined.extend(verify_execution_proofs_forward(
                expansion_capture.as_deref_mut(),
                else_branch,
                else_contexts,
                next_statement_index,
                next_loop_index,
                environment,
                verified_loop_rules,
            )?);
            joined.extend(bypassed);
            *next_statement_index = source_region.continuation_node;
            Ok(joined)
        }
        ProgramStatement::Loop {
            test: loop_test,
            update,
            invariant_checks,
            effect_checks,
            resource_specs,
            ranking_measures,
            structural_measure,
            body,
            ..
        } => {
            let condition = loop_test.entry_condition();
            let test = Some(loop_test);
            let statement_index = *next_statement_index;
            let _site_scope = crate::surface::diagnostics::StatementSiteScope::enter(
                environment.source_layout,
                statement_index,
                environment.parsed_function,
            );
            let loop_index = *next_loop_index;
            *next_loop_index += 1;
            let source_region = environment
                .source_layout
                .statement(statement_index)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "execution proof traversal could not resolve region({statement_index})"
                    ))
                })?;
            if !matches!(source_region.kind, SourceStatementKind::Loop { loop_index: found } if found == loop_index)
            {
                return Err(ClickError::new(format!(
                    "execution proof traversal region({statement_index}) does not match loop({loop_index})"
                )));
            }
            let opening = match environment.loop_owner {
                Some(owner) => owner.open_loop_proof(loop_index, statement.clone()),
                None => environment
                    .loop_source
                    .open_loop_proof(loop_index, statement.clone()),
            }
            .map_err(|error| {
                crate::surface::verification::termination_analysis_error(
                    &error,
                    error.message().to_owned(),
                )
            })?;
            let loop_clause = environment
                .function_block
                .structural_clauses()
                .for_loop(loop_index);
            let explicit_tactics = loop_clause.and_then(explicit_loop_preservation_tactics);
            let default_initialization = SourceProof::Default;
            let initialization_proof = loop_clause.map(|clause| {
                (
                    clause,
                    clause.initialize_proof().unwrap_or(&default_initialization),
                )
            });
            let mut iteration_contexts = Vec::new();
            let mut initialization_path_certificates = Vec::new();
            let mut checked_initializations = Vec::new();
            let mut preservation_path_certificates = Vec::new();
            let mut final_exit_candidates_by_context = Vec::with_capacity(contexts.len());
            let mut early_exits_by_context = Vec::with_capacity(contexts.len());
            let mut back_edges_by_context = Vec::with_capacity(contexts.len());
            let mut return_exits_by_context = Vec::with_capacity(contexts.len());
            let mut exit_points_by_context = Vec::with_capacity(contexts.len());
            let mut guard_points_by_context = Vec::with_capacity(contexts.len());
            let has_otherwise = loop_clause
                .and_then(StructuralClause::otherwise_proof)
                .and_then(SourceProof::tactics)
                .is_some_and(|tactics| !tactics.is_empty());
            for context in &contexts {
                let mut final_exit_candidates = Vec::new();
                let mut early_exits = Vec::new();
                let mut back_edges = Vec::new();
                let mut return_exits = Vec::new();
                let mut exit_points = Vec::new();
                let mut guard_points = Vec::new();
                let assumptions = assumptions_from_propositions(&context.pure_facts);
                if let Some((clause, proof)) = initialization_proof {
                    let initialization = verify_loop_initialization_pure_proof(
                        expansion_capture.as_deref_mut(),
                        loop_index,
                        proof,
                        clause,
                        context,
                        invariant_checks,
                        environment,
                    )
                    .map_err(|error| {
                        locate_loop_phase_error(
                            environment,
                            error,
                            LoopPhasePlace::Script("initialize"),
                        )
                    })?;
                    initialization_path_certificates.push(PathCertificate {
                        case_path: context.case_path.clone(),
                        case_offsets: None,
                        certificate: initialization.certificate.clone(),
                    });
                    checked_initializations.push(initialization);
                } else {
                    loop_invariants_hold_at_entry(&context.state, invariant_checks, &assumptions)
                        .map_err(|message| {
                        ClickError::new(format!(
                            "`{}`: {message}",
                            crate::surface::claim_labels::loop_phase_claim_label(
                                environment.function_block.signature().name(),
                                loop_index,
                                "initialize",
                            )
                        ))
                    })?;
                }
                // The loop head invents identities for everything the body can
                // change, from this execution's counter rather than from the
                // base of the identity range.
                let pass_body = crate::kernel::program_loop_pass(body, update.as_deref(), test);
                let preservation_contexts = crate::kernel::loop_phase_preservation_contexts(
                    &context.state,
                    condition,
                    invariant_checks,
                    effect_checks,
                    resource_specs,
                    environment.function.composite_resource_definitions(),
                    &pass_body,
                    &assumptions,
                    context.next_kernel_variable,
                )
                .map_err(|refusal| {
                    let diagnostic = ClickError::new(format!(
                        "`{}`: {}{}",
                        crate::surface::claim_labels::loop_phase_claim_label(
                            environment.function_block.signature().name(),
                            loop_index,
                            "maintain",
                        ),
                        crate::surface::diagnostics::describe_loop_head_refusal(&refusal),
                        crate::surface::diagnostics::describe_execution_statement_site()
                    ));
                    match refusal {
                        crate::kernel::LoopHeadRefusal::UnheldResource { .. }
                        | crate::kernel::LoopHeadRefusal::MissingPrerequisite { .. }
                        | crate::kernel::LoopHeadRefusal::ResourceEvaluation(_) => {
                            diagnostic.with_proof_refusal(ProofRefusal::IncompleteProof)
                        }
                        crate::kernel::LoopHeadRefusal::Contract(_) => {
                            diagnostic.with_proof_refusal(ProofRefusal::Contract)
                        }
                        crate::kernel::LoopHeadRefusal::Tactic(_)
                        | crate::kernel::LoopHeadRefusal::GuardEvaluation(_) => {
                            diagnostic.with_proof_refusal(ProofRefusal::Tactic)
                        }
                        crate::kernel::LoopHeadRefusal::Message(_) => diagnostic,
                    }
                })?;
                let multiple_entries = preservation_contexts.len() > 1;
                let mut entry_certificates = Vec::new();
                let mut entry_captures = Vec::new();
                for preservation in &preservation_contexts {
                    // Retain the checked graph prefix paired with the head's
                    // resources. The preservation assumptions are its explicit
                    // delta, not a newly rebuilt equality namespace.
                    let mut pure_facts = context.pure_facts.clone();
                    pure_facts.extend(preservation.pure_facts().iter().cloned());
                    if let Some(clause) = loop_clause {
                        let (preservation_tactics, first_generated_tactic_index) =
                            if let Some(tactics) = explicit_tactics {
                                (tactics.to_vec(), tactics.len())
                            } else {
                                let planned = plan_automatic_loop_preservation_body(
                                    loop_index,
                                    preservation,
                                    &pure_facts,
                                    &context.recorded_states,
                                    body,
                                    update.as_ref(),
                                    test,
                                    environment,
                                )
                                .map_err(|error| {
                                    locate_loop_phase_error(
                                        environment,
                                        error,
                                        LoopPhasePlace::PlannedPreservation,
                                    )
                                })?;
                                let body_certificate = planned.certificate;
                                let mut tactics = clause
                                    .preserve_proof()
                                    .and_then(SourceProof::tactics)
                                    .unwrap_or_default()
                                    .iter()
                                    .filter(|tactic| {
                                        matches!(tactic, ProofTactic::UnfoldProposition(_))
                                    })
                                    .cloned()
                                    .collect::<Vec<_>>();
                                let first_generated_tactic_index = tactics.len();
                                tactics.extend(body_certificate.to_proof_tactics().iter().cloned());
                                tactics.push(ProofTactic::Solve);
                                (tactics, first_generated_tactic_index)
                            };
                        let mut path_capture = multiple_entries
                            .then(|| {
                                expansion_capture
                                    .as_deref()
                                    .map(ExpansionCapture::fork_loop_entry)
                            })
                            .flatten();
                        let result = verify_one_loop_preservation_proof(
                            if multiple_entries {
                                path_capture.as_mut()
                            } else {
                                expansion_capture.as_deref_mut()
                            },
                            loop_index,
                            &preservation_tactics,
                            first_generated_tactic_index,
                            preservation,
                            &pure_facts,
                            &context.recorded_states,
                            invariant_checks,
                            ranking_measures,
                            structural_measure.as_deref(),
                            condition,
                            body,
                            update.as_ref(),
                            test,
                            has_otherwise.then_some(&mut guard_points),
                            environment,
                        )
                        .map_err(|error| {
                            locate_loop_phase_error(
                                environment,
                                error,
                                if explicit_tactics.is_some() {
                                    LoopPhasePlace::Script("maintain")
                                } else {
                                    LoopPhasePlace::PlannedPreservation
                                },
                            )
                        })?;
                        verified_loop_rules.extend(result.nested_loop_rules);
                        final_exit_candidates.extend(result.final_exit_candidates);
                        early_exits.extend(result.early_exits);
                        back_edges.push(result.back_edges);
                        return_exits.extend(result.return_exits);
                        exit_points.extend(result.exit_points);
                        environment
                            .frontier_loop_certificates
                            .borrow_mut()
                            .returns
                            .extend(result.return_proofs);
                        if let Some(capture) = path_capture {
                            entry_captures.push(capture);
                        }
                        entry_certificates.push(result.certificate);
                    }
                    iteration_contexts.push(PlanningExecutionContext {
                        state: preservation.state().clone(),
                        pure_facts,
                        surface_propositions: context.surface_propositions.clone(),
                        recorded_states: context.recorded_states.clone(),
                        case_path: context.case_path.clone(),
                        next_opaque_call: context.next_opaque_call,
                        // The head state this context carries holds the
                        // identities the head invented; continue from where
                        // that left the counter, not from where it started.
                        next_kernel_variable: preservation.next_kernel_variable(),
                        resume_at_statement: context.resume_at_statement,
                    });
                }
                // Keep the existing identical-certificate path. Only differing
                // proofs need a tree of the guard decisions that distinguish them.
                let identical = entry_certificates.first().is_none_or(|first| {
                    entry_certificates.iter().skip(1).all(|certificate| {
                        crate::instrumentation::record_deterministic_work(
                            certificate.steps().len(),
                        );
                        certificate == first
                    })
                });
                let entry_branches = if identical {
                    LoopEntryBranches::Leaf((0..entry_certificates.len()).collect())
                } else {
                    loop_entry_branches(&preservation_contexts, environment, loop_index)?
                };
                if let Some(capture) = expansion_capture.as_deref_mut()
                    && !entry_captures.is_empty()
                {
                    capture.merge_loop_entries(
                        &entry_captures.iter().collect::<Vec<_>>(),
                        &entry_branches,
                    );
                }
                if !entry_certificates.is_empty() {
                    preservation_path_certificates.push(PathCertificate {
                        case_path: context.case_path.clone(),
                        case_offsets: None,
                        certificate: entry_branches.certificate(
                            &entry_certificates,
                            &environment.frontier_loop_source.claim_label,
                        )?,
                    });
                }
                final_exit_candidates_by_context.push(final_exit_candidates);
                early_exits_by_context.push(early_exits);
                back_edges_by_context.push(back_edges);
                return_exits_by_context.push(return_exits);
                environment
                    .frontier_loop_certificates
                    .borrow_mut()
                    .exit_points
                    .entry(loop_index)
                    .or_default()
                    .extend(exit_points.iter().cloned());
                exit_points_by_context.push(exit_points);
                guard_points_by_context.push(guard_points);
            }
            let source = environment.frontier_loop_source;
            if initialization_proof.is_some() {
                let initialization_certificate = merge_path_aligned_certificates(
                    &source.claim_label,
                    initialization_path_certificates,
                )?;
                environment
                    .frontier_loop_certificates
                    .borrow_mut()
                    .initialize = Some(initialization_certificate.clone());
                let selected = match (&source.proof_site, source.initialize_source_index) {
                    (Some(site), Some(_)) => {
                        selected_tactic_indices_for_site(expansion_capture.as_deref(), site)
                    }
                    _ => Vec::new(),
                };
                if let Some(initialization) = checked_initializations.first()
                    && let Some(site) = source.proof_site.as_ref()
                {
                    for index in selected {
                        if let Some(expansion) = initialization
                            .phase_closer_expansion(index, &initialization_certificate)
                        {
                            record_proof_site_tactic_expansion(
                                expansion_capture.as_deref_mut(),
                                site,
                                index,
                                &expansion,
                            );
                        }
                    }
                }
            }
            if !preservation_path_certificates.is_empty() {
                let preservation_certificate = merge_path_aligned_certificates(
                    &source.claim_label,
                    preservation_path_certificates,
                )?;
                environment.frontier_loop_certificates.borrow_mut().preserve =
                    Some(preservation_certificate.clone());
                // `maintain by close();` is one smart tactic standing for the
                // whole phase, exactly as `initialize by close();` is: the
                // planned preservation certificate is its expansion. The
                // driver's own tactics are all generated here, so no
                // source-indexed step claims the occurrence.
                if let Some(preserve_source_index) = source.preserve_source_index
                    && matches!(
                        loop_clause.and_then(StructuralClause::preserve_proof),
                        Some(SourceProof::Tactic(SmartTactic::Solve))
                    )
                    && let Some(site) = source.proof_site.as_ref()
                    && capture_selects_source(
                        expansion_capture.as_deref(),
                        site,
                        preserve_source_index,
                    )
                {
                    record_proof_site_tactic_expansion(
                        expansion_capture.as_deref_mut(),
                        site,
                        preserve_source_index,
                        &preservation_certificate.to_proof_tactics(),
                    );
                }
            }
            *next_statement_index = source_region.continuation_node;

            advance_execution_proof_statement(
                expansion_capture,
                statement,
                contexts,
                statement_index,
                Some(loop_index),
                Some(&opening),
                environment,
                verified_loop_rules,
                if loop_clause.is_some() {
                    LoopPreservationSource::ExecutionProof
                } else {
                    LoopPreservationSource::Automatic
                },
                initialization_proof.map(|_| checked_initializations.as_slice()),
                Some(&final_exit_candidates_by_context),
                Some(&early_exits_by_context),
                Some(&return_exits_by_context),
                Some(&back_edges_by_context),
                Some(&exit_points_by_context),
                Some(&guard_points_by_context),
            )
        }
        ProgramStatement::Return(_) => {
            let statement_index = *next_statement_index;
            *next_statement_index = environment
                .source_layout
                .statement(statement_index)
                .map(|region| region.continuation_node)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "execution proof traversal could not resolve region({statement_index})"
                    ))
                })?;
            let mut bypassed = Vec::new();
            for context in contexts {
                match context.resume_at_statement {
                    Some(target) if target > statement_index => bypassed.push(context),
                    Some(target) if target == statement_index => {}
                    Some(_) => {
                        return Err(ClickError::new(
                            "execution proof traversal passed a goto target",
                        ));
                    }
                    None => {}
                }
            }
            Ok(bypassed)
        }
        _ => {
            let statement_index = *next_statement_index;
            let _site_scope = crate::surface::diagnostics::StatementSiteScope::enter(
                environment.source_layout,
                statement_index,
                environment.parsed_function,
            );
            *next_statement_index = environment
                .source_layout
                .statement(statement_index)
                .map(|region| region.continuation_node)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "execution proof traversal could not resolve region({statement_index})"
                    ))
                })?;
            let mut active = Vec::new();
            let mut bypassed = Vec::new();
            for mut context in contexts {
                match context.resume_at_statement {
                    Some(target) if target > statement_index => bypassed.push(context),
                    Some(target) if target == statement_index => {
                        context.resume_at_statement = None;
                        active.push(context);
                    }
                    Some(_) => {
                        return Err(ClickError::new(
                            "execution proof traversal passed a goto target",
                        ));
                    }
                    None => active.push(context),
                }
            }
            let advanced = advance_execution_proof_statement(
                None,
                statement,
                active,
                statement_index,
                None,
                None,
                environment,
                verified_loop_rules,
                LoopPreservationSource::Automatic,
                None,
                None,
                None,
                None,
                None,
                None,
                None,
            )?;
            bypassed.extend(advanced);
            Ok(bypassed)
        }
    }
}

fn split_execution_proof_branch_contexts(
    condition: &ProgramExpression,
    contexts: Vec<PlanningExecutionContext>,
) -> Result<(Vec<PlanningExecutionContext>, Vec<PlanningExecutionContext>), ClickError> {
    let mut then_contexts = Vec::new();
    let mut else_contexts = Vec::new();
    for context in contexts {
        for transition in certified_condition_transitions(
            &context.state,
            &context.pure_facts,
            condition,
            "execution proof traversal",
            StatementPrerequisitePolicy::Fast,
            None,
        )? {
            let next = PlanningExecutionContext {
                state: context.state.clone(),
                pure_facts: transition.pure_facts,
                surface_propositions: context.surface_propositions.clone(),
                recorded_states: context.recorded_states.clone(),
                case_path: {
                    let mut case_path = context.case_path.clone();
                    case_path.push(ProofCaseChoice {
                        condition: surface_program_condition(
                            condition,
                            &context.state,
                            Some(&context.recorded_states),
                        )?,
                        value: transition.is_true,
                        match_arm: None,
                    });
                    case_path
                },
                next_opaque_call: context.next_opaque_call,
                next_kernel_variable: context.next_kernel_variable,
                resume_at_statement: context.resume_at_statement,
            };
            if transition.is_true {
                then_contexts.push(next);
            } else {
                else_contexts.push(next);
            }
        }
    }
    Ok((then_contexts, else_contexts))
}

fn advance_execution_proof_statement(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    statement: &ProgramStatement,
    contexts: Vec<PlanningExecutionContext>,
    statement_index: usize,
    loop_index: Option<usize>,
    opening: Option<&crate::kernel::StatementProofInput>,
    environment: &ExecutionProofEnvironment<'_>,
    verified_loop_rules: &mut Vec<VerifiedLoopRule>,
    loop_preservation_source: LoopPreservationSource,
    initializations: Option<&[CheckedLoopInitialization]>,
    loop_final_exit_candidates: Option<&[Vec<LoopFinalExitCandidate>]>,
    loop_early_exits: Option<&[Vec<LoopEarlyExit>]>,
    loop_return_exits: Option<&[Vec<LoopReturnExit>]>,
    loop_back_edges: Option<&[Vec<crate::kernel::LoopBackEdges>]>,
    loop_exit_points: Option<&[Vec<RecordedRegionPoints>]>,
    guard_points_by_context: Option<&[Vec<RecordedRegionPoints>]>,
) -> Result<Vec<PlanningExecutionContext>, ClickError> {
    let input = opening.cloned().unwrap_or_else(|| statement.into());
    let mut advanced = Vec::new();
    let mut otherwise_certificates = Vec::new();
    for (context_index, mut context) in contexts.into_iter().enumerate() {
        record_code_region_program_state(
            &mut context.recorded_states,
            environment.function_block,
            CodeRegion::Statement(statement_index),
            ProgramPointKind::Entry,
            context.state.clone(),
        );
        let label = format!("execution proof traversal at region({statement_index})");
        let preservation_proven = matches!(
            loop_preservation_source,
            LoopPreservationSource::ExecutionProof
        );
        let final_exit_candidates = loop_final_exit_candidates
            .and_then(|candidates| candidates.get(context_index))
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let early_exits = loop_early_exits
            .and_then(|exits| exits.get(context_index))
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let return_exits = loop_return_exits
            .and_then(|exits| exits.get(context_index))
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let back_edges = loop_back_edges
            .and_then(|edges| edges.get(context_index))
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let initialization_proven = match initializations {
            Some(initializations) => {
                if !initializations
                    .get(context_index)
                    .is_some_and(CheckedLoopInitialization::is_complete)
                {
                    return Err(ClickError::new(
                        "missing checked loop initialization completion",
                    ));
                }
                true
            }
            None => false,
        };
        let otherwise = loop_index.and_then(|index| {
            environment
                .function_block
                .structural_clauses()
                .for_loop(index)
                .and_then(StructuralClause::otherwise_proof)
                .and_then(SourceProof::tactics)
                .filter(|tactics| !tactics.is_empty())
                .map(|tactics| (index, tactics))
        });
        let mut otherwise_error = None;
        let mut otherwise_certificate = None;
        let mut prove_otherwise = |loop_entry: &ExecutionState,
                                   exit_state: &ExecutionState,
                                   facts: &crate::kernel::ExecutionFacts,
                                   points_index: Option<usize>| {
            let guard_points = points_index.map(|index| {
                &guard_points_by_context.expect("checked guard point records")[context_index][index]
            });
            let (index, tactics) = otherwise.expect("only installed for an otherwise block");
            match verify_loop_otherwise(
                expansion_capture.as_deref_mut(),
                index,
                tactics,
                loop_entry,
                exit_state,
                facts,
                guard_points,
                &context,
                environment,
            ) {
                Ok((facts, certificate)) => {
                    otherwise_certificate = Some(certificate);
                    Some(facts)
                }
                Err(error) => {
                    otherwise_error = Some(locate_loop_phase_error(
                        environment,
                        error,
                        LoopPhasePlace::Script("otherwise"),
                    ));
                    None
                }
            }
        };
        let scope_exit_facts =
            |state: &ExecutionState,
             iterations: &crate::kernel::IntegerTerm,
             exits: &[(ExecutionState, crate::kernel::ExecutionFacts)],
             facts: &crate::kernel::ExecutionFacts| {
                scoped_loop_exit_facts(
                    loop_index.expect("selected loop"),
                    state,
                    iterations,
                    exits,
                    facts,
                    &context,
                    environment,
                )
            };
        let exit_fact_scope = (loop_index.is_some() && scoped_loop_exit_facts_enabled())
            .then_some(&scope_exit_facts as &crate::kernel::LoopExitFactScope<'_>);
        let mut next_opaque_call = context.next_opaque_call;
        let mut next_kernel_variable = context.next_kernel_variable;
        let transitions_result = match (initialization_proven, preservation_proven) {
            (false, false) => certified_statement_transitions(
                &context.state,
                &context.pure_facts,
                input.clone(),
                environment.function_environment,
                Some(environment.spec_definitions.predicates),
                ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
                &label,
                &mut next_opaque_call,
                &mut next_kernel_variable,
                StatementPrerequisitePolicy::Fast,
                None,
            ),
            _ => certified_loop_exit_transitions_with_proven_phases(
                &context.state,
                &context.pure_facts,
                input.clone(),
                environment.function_environment,
                Some(environment.spec_definitions.predicates),
                &label,
                initialization_proven,
                preservation_proven,
                final_exit_candidates,
                early_exits,
                return_exits,
                back_edges,
                otherwise
                    .map(|_| &mut prove_otherwise as &mut crate::kernel::LoopOtherwiseProof<'_>),
                exit_fact_scope,
                &mut next_opaque_call,
                &mut next_kernel_variable,
            ),
        };
        if let Some(error) = otherwise_error {
            return Err(error);
        }
        let (transitions, loop_rule) = transitions_result?;
        context.next_opaque_call = next_opaque_call;
        context.next_kernel_variable = next_kernel_variable;
        if let Some(certificate) = otherwise_certificate {
            otherwise_certificates.push(PathCertificate {
                case_path: context.case_path.clone(),
                case_offsets: None,
                certificate,
            });
        }
        if matches!(statement, ProgramStatement::Loop { .. }) {
            let loop_index = loop_index.ok_or_else(|| {
                ClickError::new(format!(
                    "execution proof traversal region({statement_index}) is a loop without a loop index"
                ))
            })?;
            let loop_rule = loop_rule.ok_or_else(|| {
                let unresolved = transitions
                    .iter()
                    .flat_map(|transition| transition.obligations.iter())
                    .filter(|obligation| !obligation.is_assumable())
                    .map(|obligation| {
                        obligation
                            .context()
                            .unwrap_or("unlabeled verification condition")
                            .to_string()
                    })
                    .collect::<Vec<_>>();
                let mut unresolved = unresolved;
                unresolved.sort();
                unresolved.dedup();
                ClickError::new(format!(
                    "`{}` loop({loop_index}) did not produce a verified loop rule{}",
                    environment.function_block.signature().name(),
                    if unresolved.is_empty() {
                        String::new()
                    } else {
                        format!(
                            "; unresolved verification conditions: {}",
                            unresolved.join(", ")
                        )
                    }
                ))
            })?;
            verified_loop_rules.push(loop_rule);
        }
        for transition in transitions {
            let mut surface_propositions = context.surface_propositions.clone();
            let mut recorded_states = context.recorded_states.clone();
            if let StatementOutcome::Normal(exit_state)
            | StatementOutcome::Return {
                state: exit_state, ..
            } = &transition.outcome
            {
                let footprint = crate::kernel::RegionFootprint::statement_transition(
                    format!("region({statement_index}).footprint"),
                    statement,
                    &context.state,
                    exit_state,
                    &transition.execution_facts,
                );
                recorded_states.record_effect(Some(&footprint));
                record_code_region_program_state(
                    &mut recorded_states,
                    environment.function_block,
                    CodeRegion::Statement(statement_index),
                    ProgramPointKind::Exit,
                    *exit_state.clone(),
                );
                recorded_states.record_read_events(statement_index, &transition.execution_facts);
                if let Some(result) = &transition.call_result {
                    recorded_states.record_call_transition_result(statement_index, result.clone());
                }
            }
            if matches!(statement, ProgramStatement::Loop { .. }) {
                let loop_index = loop_index.expect("a loop statement has a checked loop index");
                let loop_labels = environment
                    .function_block
                    .structural_clauses()
                    .for_loop(loop_index)
                    .into_iter()
                    .filter_map(StructuralClause::label)
                    .map(str::to_string)
                    .collect::<Vec<_>>();
                for label in &loop_labels {
                    recorded_states.label_loop(loop_index, label);
                }
                let entry_point = ProgramPointRef {
                    region: CodeRegionRef::Loop(loop_index),
                    kind: ProgramPointKind::Entry,
                };
                recorded_states.insert(entry_point, context.state.clone());
                if let StatementOutcome::Normal(exit_state) = &transition.outcome {
                    let exit_point = ProgramPointRef {
                        region: CodeRegionRef::Loop(loop_index),
                        kind: ProgramPointKind::Exit,
                    };
                    recorded_states.insert(exit_point.clone(), *exit_state.clone());
                    // A loop that leaves on one path names that pass's
                    // points after it: its calls, its test, its body's
                    // statements, as the pass recorded them. Several leaving
                    // paths would give one name several states, so then
                    // none is recorded.
                    if let Some([points]) = loop_exit_points
                        .and_then(|points| points.get(context_index))
                        .map(Vec::as_slice)
                    {
                        recorded_states.record_region_points(points);
                    }
                    if let Some(iterations) = &transition.loop_iterations {
                        recorded_states.record_loop_iterations_root(loop_index, iterations.clone());
                    }
                    if let Some(loop_clause) = environment
                        .function_block
                        .structural_clauses()
                        .for_loop(loop_index)
                    {
                        record_loop_exit_invariants(
                            &mut surface_propositions,
                            loop_clause,
                            &transition.loop_invariant_correspondence,
                            loop_index,
                        )?;
                    }
                    if let ProgramStatement::Loop {
                        test: loop_test, ..
                    } = statement
                    {
                        let Some(condition) = loop_test.entry_condition() else {
                            continue;
                        };
                        let exit_condition =
                            SyntaxProposition::Not(Box::new(surface_program_condition(
                                condition,
                                exit_state,
                                Some(&recorded_states),
                            )?));
                        let lowered_exit_condition = lower_fixed_state_proposition(
                            &exit_condition,
                            &transition.pure_facts,
                            environment.parameter_binding(),
                            FixedStateFrame::new(
                                environment.initial_state,
                                exit_state,
                                None,
                                &recorded_states,
                            ),
                            environment.spec_definitions,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "could not lower loop({loop_index}) exit condition: {message}"
                            ))
                        })?;
                        if transition.pure_facts.contains(&lowered_exit_condition) {
                            let exit_surface =
                                surface_at_program_point(&exit_condition, &exit_point)?;
                            surface_propositions
                                .record_lowering(&exit_surface, &lowered_exit_condition)?;
                        }
                    }
                }
            }
            match transition.outcome {
                StatementOutcome::Normal(state) => advanced.push(PlanningExecutionContext {
                    state: *state,
                    pure_facts: transition.pure_facts,
                    surface_propositions,
                    recorded_states,
                    case_path: context.case_path.clone(),
                    next_opaque_call: context.next_opaque_call,
                    next_kernel_variable: context.next_kernel_variable,
                    resume_at_statement: None,
                }),
                StatementOutcome::Jump { target, state } => {
                    let target = environment.function.control_target(target).ok_or_else(|| {
                        ClickError::new("execution proof traversal produced an unknown goto target")
                    })?;
                    advanced.push(PlanningExecutionContext {
                        state: *state,
                        pure_facts: transition.pure_facts,
                        surface_propositions,
                        recorded_states,
                        case_path: context.case_path.clone(),
                        next_opaque_call: context.next_opaque_call,
                        next_kernel_variable: context.next_kernel_variable,
                        resume_at_statement: Some(target.statement_index),
                    });
                }
                StatementOutcome::LoopTestFalse(_)
                | StatementOutcome::Break(_)
                | StatementOutcome::Continue(_)
                | StatementOutcome::Throw { .. }
                | StatementOutcome::Return { .. } => {}
                StatementOutcome::VerificationDiverges => {}
                StatementOutcome::UndefinedBehavior(kind) => {
                    return Err(ClickError::new(format!(
                        "execution proof traversal for {} region({statement_index}) produced undefined behavior: {}{}",
                        environment.function_block.signature().name(),
                        kind.description(),
                        crate::surface::diagnostics::describe_execution_statement_site()
                    )).with_reported_assertion_goal(kind.required_goal().cloned()));
                }
                StatementOutcome::RuntimeError(error) => {
                    return Err(ClickError::new(format!(
                        "execution proof traversal for {} region({statement_index}) could not verify C operation: {}{}\nresource facts in context: {}",
                        environment.function_block.signature().name(),
                        describe_runtime_error(&error, ParameterBinding::default()),
                        crate::surface::diagnostics::describe_execution_statement_site(),
                        context.state.resources().facts().len()
                    ))
                    .with_kind(crate::surface::diagnostics::runtime_refusal_kind(&error)));
                }
            }
        }
    }
    if !otherwise_certificates.is_empty() {
        environment
            .frontier_loop_certificates
            .borrow_mut()
            .otherwise = Some(merge_path_aligned_certificates(
            &environment.frontier_loop_source.claim_label,
            otherwise_certificates,
        )?);
    }
    Ok(advanced)
}

/// A refusal from a loop phase proof, restated at the `loop` tactic that owns
/// it.
fn locate_loop_phase_error(
    environment: &ExecutionProofEnvironment<'_>,
    error: ClickError,
    phase: LoopPhasePlace,
) -> ClickError {
    environment
        .frontier_loop_source
        .locate_phase_error(error, phase)
}

/// Rebuild the decision tree from the guard facts produced by the entry check.
/// Only these explicit deltas are indexed; ambient proof facts are never read.
fn loop_entry_branches(
    entries: &[crate::kernel::LoopPreservationContext],
    environment: &ExecutionProofEnvironment<'_>,
    loop_index: usize,
) -> Result<LoopEntryBranches, ClickError> {
    let guards = entries
        .iter()
        .map(|entry| {
            crate::instrumentation::record_deterministic_work(entry.entry_guard().len());
            entry.entry_guard().iter().cloned().collect::<BTreeSet<_>>()
        })
        .collect::<Vec<_>>();
    fn build(
        entries: &[crate::kernel::LoopPreservationContext],
        guards: &[BTreeSet<Proposition>],
        indices: Vec<usize>,
        mut decided: BTreeSet<crate::kernel::OldConditionTerm>,
        environment: &ExecutionProofEnvironment<'_>,
        loop_index: usize,
    ) -> Result<LoopEntryBranches, ClickError> {
        if indices.len() < 2 {
            return Ok(LoopEntryBranches::Leaf(indices));
        }
        for fact in &guards[indices[0]] {
            crate::instrumentation::record_deterministic_work(1);
            let Proposition::ConditionIs(condition, _) = fact else {
                continue;
            };
            if decided.contains(condition.old_form()) {
                continue;
            }
            let positive = Proposition::condition_is(condition.clone(), true);
            let negative = Proposition::condition_is(condition.clone(), false);
            let (mut yes, mut no) = (Vec::new(), Vec::new());
            for index in &indices {
                crate::instrumentation::record_deterministic_work(1);
                if guards[*index].contains(&positive) {
                    yes.push(*index);
                } else if guards[*index].contains(&negative) {
                    no.push(*index);
                }
            }
            if yes.len() + no.len() != indices.len() {
                continue;
            }
            decided.insert((condition.clone()).old_form().clone());
            if yes.is_empty() || no.is_empty() {
                continue;
            }
            let surface = crate::surface::proof::surface_synthesis::synthesize_surface_proposition(
                &positive,
                environment.parameter_binding(),
                entries[indices[0]].state(),
            )
            .ok_or_else(|| ClickError::new("loop entry guard has no source spelling"))?;
            let condition = surface_at_program_point(
                &surface,
                &ProgramPointRef {
                    region: CodeRegionRef::Region(
                        environment
                            .source_layout
                            .loop_body_entry(loop_index)
                            .expect("loop body"),
                    ),
                    kind: ProgramPointKind::Entry,
                },
            )?;
            return Ok(LoopEntryBranches::Split {
                condition,
                yes: Box::new(build(
                    entries,
                    guards,
                    yes,
                    decided.clone(),
                    environment,
                    loop_index,
                )?),
                no: Box::new(build(
                    entries,
                    guards,
                    no,
                    decided,
                    environment,
                    loop_index,
                )?),
            });
        }
        Ok(LoopEntryBranches::Leaf(indices))
    }
    build(
        entries,
        &guards,
        (0..entries.len()).collect(),
        BTreeSet::new(),
        environment,
        loop_index,
    )
}
