use super::*;

pub(in crate::surface::proof) fn verify_execution_proofs_forward(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    statement: &CStatement,
    contexts: Vec<PlanningExecutionContext>,
    next_statement_index: &mut usize,
    next_loop_index: &mut usize,
    environment: &ExecutionProofEnvironment<'_>,
    verified_loop_rules: &mut Vec<CVerifiedLoopRule>,
) -> Result<Vec<PlanningExecutionContext>, ClickError> {
    match statement {
        CStatement::Seq(first, second) => {
            let contexts = verify_execution_proofs_forward(
                expansion_capture.as_deref_mut(),
                first,
                contexts,
                next_statement_index,
                next_loop_index,
                environment,
                verified_loop_rules,
            )?;
            verify_execution_proofs_forward(
                expansion_capture.as_deref_mut(),
                second,
                contexts,
                next_statement_index,
                next_loop_index,
                environment,
                verified_loop_rules,
            )
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let statement_index = *next_statement_index;
            let source_region = environment
                .source_layout
                .statement(statement_index)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "execution proof traversal could not resolve source statement({statement_index})"
                    ))
                })?;
            let SourceStatementKind::If {
                then_statement_index,
                else_statement_index,
            } = source_region.kind
            else {
                return Err(ClickError::new(format!(
                    "execution proof traversal expected source statement({statement_index}) to be an `if`"
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
        CStatement::While {
            condition,
            invariant_checks,
            effect_checks,
            resource_specs,
            ranking_measures,
            structural_measure,
            body,
            do_while,
            ..
        } => {
            let statement_index = *next_statement_index;
            let loop_index = *next_loop_index;
            *next_loop_index += 1;
            let source_region = environment
                .source_layout
                .statement(statement_index)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "execution proof traversal could not resolve source statement({statement_index})"
                    ))
                })?;
            if !matches!(source_region.kind, SourceStatementKind::Loop { loop_index: found } if found == loop_index)
            {
                return Err(ClickError::new(format!(
                    "execution proof traversal source statement({statement_index}) does not match loop({loop_index})"
                )));
            }
            crate::kernel::c_reject_address_escaped_loop_measures(
                environment.function_block.signature().name(),
                ranking_measures,
                environment.function.source_body(),
            )
            .map_err(ClickError::new)?;
            let loop_clause = environment
                .function_block
                .structural_clauses()
                .iter()
                .find(|clause| clause.region() == &CodeRegion::Loop(loop_index));
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
            let mut break_exits_by_context = Vec::with_capacity(contexts.len());
            for context in &contexts {
                let mut final_exit_candidates = Vec::new();
                let mut break_exits = Vec::new();
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
                    )?;
                    initialization_path_certificates.push(PathCertificate {
                        case_path: context.case_path.clone(),
                        case_offsets: None,
                        certificate: initialization.certificate.clone(),
                    });
                    checked_initializations.push(initialization);
                } else {
                    c_loop_invariants_hold_at_entry(&context.state, invariant_checks, &assumptions)
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{}.loop({loop_index}).initialize`: {message}",
                                environment.function_block.signature().name()
                            ))
                        })?;
                }
                // The loop head invents identities for everything the body can
                // change, from this execution's counter rather than from the
                // base of the identity range.
                let preservation_contexts = if *do_while {
                    c_do_while_preservation_contexts(
                        &context.state,
                        condition,
                        invariant_checks,
                        effect_checks,
                        resource_specs,
                        environment.function.composite_resource_definitions(),
                        body,
                        &assumptions,
                        context.next_kernel_variable,
                    )
                } else {
                    c_loop_preservation_contexts(
                        &context.state,
                        condition,
                        invariant_checks,
                        effect_checks,
                        resource_specs,
                        environment.function.composite_resource_definitions(),
                        body,
                        &assumptions,
                        context.next_kernel_variable,
                    )
                }
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{}.loop({loop_index}).preserve`: {message}",
                        environment.function_block.signature().name()
                    ))
                })?;
                for preservation in preservation_contexts {
                    let mut pure_facts = context.pure_facts.clone();
                    pure_facts.extend_from_slice(preservation.pure_facts());
                    pure_facts.sort();
                    pure_facts.dedup();
                    if let Some(clause) = loop_clause {
                        let (preservation_tactics, first_generated_tactic_index) =
                            if let Some(tactics) = explicit_tactics {
                                (tactics.to_vec(), tactics.len())
                            } else {
                                let body_certificate = plan_automatic_loop_preservation_body(
                                    loop_index,
                                    &preservation,
                                    &pure_facts,
                                    body,
                                    environment,
                                )?;
                                let mut tactics = clause
                                    .preserve_proof()
                                    .and_then(SourceProof::tactics)
                                    .unwrap_or_default()
                                    .iter()
                                    .filter(|tactic| {
                                        matches!(tactic, ProofTactic::UnfoldPredicate(_))
                                    })
                                    .cloned()
                                    .collect::<Vec<_>>();
                                let first_generated_tactic_index = tactics.len();
                                tactics.extend(body_certificate.to_proof_tactics().iter().cloned());
                                tactics.push(ProofTactic::Simp);
                                (tactics, first_generated_tactic_index)
                            };
                        let result = verify_one_loop_preservation_proof(
                            expansion_capture.as_deref_mut(),
                            loop_index,
                            &preservation_tactics,
                            first_generated_tactic_index,
                            &preservation,
                            &pure_facts,
                            invariant_checks,
                            ranking_measures,
                            structural_measure.as_deref(),
                            condition,
                            body,
                            *do_while,
                            environment,
                        )?;
                        verified_loop_rules.extend(result.nested_loop_rules);
                        final_exit_candidates.extend(result.final_exit_candidates);
                        break_exits.extend(result.break_exits);
                        preservation_path_certificates.push(PathCertificate {
                            case_path: context.case_path.clone(),
                            case_offsets: None,
                            certificate: result.certificate,
                        });
                    }
                    iteration_contexts.push(PlanningExecutionContext {
                        state: preservation.state().clone(),
                        pure_facts,
                        surface_propositions: context.surface_propositions.clone(),
                        recorded_snapshots: context.recorded_snapshots.clone(),
                        case_path: context.case_path.clone(),
                        next_opaque_call: context.next_opaque_call,
                        // The head state this context carries holds the
                        // identities the head invented; continue from where
                        // that left the counter, not from where it started.
                        next_kernel_variable: preservation.next_kernel_variable(),
                        resume_at_statement: context.resume_at_statement,
                    });
                }
                final_exit_candidates_by_context.push(final_exit_candidates);
                break_exits_by_context.push(break_exits);
            }
            if initialization_proof.is_some() {
                let legacy_site = ProofSite::LoopPhase {
                    function_name: environment.function_block.signature().name().to_string(),
                    loop_index,
                    phase: "initialize",
                };
                let (claim_label, site, selected_source_index) = environment
                    .frontier_loop_source
                    .map(|source| {
                        (
                            source.claim_label.clone(),
                            source
                                .proof_site
                                .clone()
                                .unwrap_or_else(|| legacy_site.clone()),
                            source.initialize_source_index,
                        )
                    })
                    .unwrap_or_else(|| (legacy_site.description(), legacy_site.clone(), Some(0)));
                let initialization_certificate = merge_path_aligned_certificates(
                    &claim_label,
                    initialization_path_certificates,
                )?;
                if let Some(certificates) = environment.frontier_loop_certificates {
                    certificates.borrow_mut().initialize = Some(initialization_certificate.clone());
                }
                if environment.frontier_loop_source.is_some() {
                    // A smart tactic that stands for the rest of the phase
                    // expands to the invariant steps the planner built. A
                    // smart `have` inside the script is recorded by the
                    // entry planner itself, at its own source index.
                    if selected_source_index.is_some()
                        && let Some(selected) =
                            selected_tactic_index_for_site(expansion_capture.as_deref(), &site)
                        && let Some(initialization) = checked_initializations.first()
                        && let Some(expansion) = initialization
                            .phase_closer_expansion(selected, &initialization_certificate)
                    {
                        record_proof_site_tactic_expansion(
                            expansion_capture.as_deref_mut(),
                            &site,
                            selected,
                            &expansion,
                        );
                    }
                } else {
                    if let Some(source_index) =
                        selected_tactic_index_for_site(expansion_capture.as_deref(), &site)
                        && let Some((_, SourceProof::Script(source_tactics))) = initialization_proof
                        && !source_tactics.iter().any(|tactic| {
                            matches!(
                                tactic,
                                ProofTactic::ApplyTheorem(_)
                                    | ProofTactic::ApplyTheoremUsing { .. }
                            )
                        })
                        && let Some(initialization) = checked_initializations.first()
                        && let Some(expansion) = initialization
                            .phase_closer_expansion(source_index, &initialization_certificate)
                    {
                        record_proof_site_tactic_expansion(
                            expansion_capture.as_deref_mut(),
                            &site,
                            source_index,
                            &expansion,
                        );
                    }
                    finish_proof_site_expansion_capture(
                        expansion_capture.as_deref_mut(),
                        &site,
                        &initialization_certificate,
                    );
                }
            }
            if !preservation_path_certificates.is_empty() {
                let claim_label = environment.frontier_loop_source.map_or_else(
                    || {
                        format!(
                            "{}.loop({loop_index}).preserve",
                            environment.function_block.signature().name()
                        )
                    },
                    |source| source.claim_label.clone(),
                );
                let preservation_certificate =
                    merge_path_aligned_certificates(&claim_label, preservation_path_certificates)?;
                if let Some(certificates) = environment.frontier_loop_certificates {
                    certificates.borrow_mut().preserve = Some(preservation_certificate.clone());
                }
                if environment.frontier_loop_source.is_none() {
                    finish_proof_site_expansion_capture(
                        expansion_capture,
                        &ProofSite::LoopPhase {
                            function_name: environment
                                .function_block
                                .signature()
                                .name()
                                .to_string(),
                            loop_index,
                            phase: "preserve",
                        },
                        &preservation_certificate,
                    );
                // `preserve by simp;` is one smart tactic standing for the
                // whole phase, exactly as `initialize by simp;` is: the
                // planned preservation certificate is its expansion. The
                // driver's own tactics are all generated here, so no
                // source-indexed step claims the occurrence.
                } else if let Some(source) = environment.frontier_loop_source
                    && let Some(preserve_source_index) = source.preserve_source_index
                    && matches!(
                        loop_clause.and_then(StructuralClause::preserve_proof),
                        Some(SourceProof::Tactic(SmartTactic::Simp))
                    )
                    && let Some(site) = source.proof_site.as_ref()
                    && selected_tactic_index_for_site(expansion_capture.as_deref(), site)
                        == Some(preserve_source_index)
                {
                    record_proof_site_tactic_expansion(
                        expansion_capture,
                        site,
                        preserve_source_index,
                        &preservation_certificate.to_proof_tactics(),
                    );
                }
            }
            *next_statement_index = source_region.continuation_node;

            advance_execution_proof_statement(
                statement,
                contexts,
                statement_index,
                Some(loop_index),
                environment,
                verified_loop_rules,
                if loop_clause.is_some() {
                    LoopPreservationSource::ExecutionProof
                } else {
                    LoopPreservationSource::Automatic
                },
                initialization_proof.map(|_| checked_initializations.as_slice()),
                Some(&final_exit_candidates_by_context),
                Some(&break_exits_by_context),
            )
        }
        CStatement::Return(_) => {
            let statement_index = *next_statement_index;
            *next_statement_index = environment
                .source_layout
                .statement(statement_index)
                .map(|region| region.continuation_node)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "execution proof traversal could not resolve source statement({statement_index})"
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
            *next_statement_index = environment
                .source_layout
                .statement(statement_index)
                .map(|region| region.continuation_node)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "execution proof traversal could not resolve source statement({statement_index})"
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
                statement,
                active,
                statement_index,
                None,
                environment,
                verified_loop_rules,
                LoopPreservationSource::Automatic,
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
    condition: &CExpression,
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
            StatementPrerequisitePolicy::Contextual,
            true,
            None,
        )? {
            let next = PlanningExecutionContext {
                state: context.state.clone(),
                pure_facts: transition.pure_facts,
                surface_propositions: context.surface_propositions.clone(),
                recorded_snapshots: context.recorded_snapshots.clone(),
                case_path: {
                    let mut case_path = context.case_path.clone();
                    case_path.push(ProofCaseChoice {
                        condition: surface_c_condition(condition),
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
    statement: &CStatement,
    contexts: Vec<PlanningExecutionContext>,
    statement_index: usize,
    loop_index: Option<usize>,
    environment: &ExecutionProofEnvironment<'_>,
    verified_loop_rules: &mut Vec<CVerifiedLoopRule>,
    loop_preservation_source: LoopPreservationSource,
    initializations: Option<&[CheckedLoopInitialization]>,
    loop_final_exit_candidates: Option<&[Vec<CLoopFinalExitCandidate>]>,
    loop_break_exits: Option<&[Vec<CLoopBreakExit>]>,
) -> Result<Vec<PlanningExecutionContext>, ClickError> {
    let mut advanced = Vec::new();
    for (context_index, mut context) in contexts.into_iter().enumerate() {
        record_code_region_program_snapshot_state(
            &mut context.recorded_snapshots,
            environment.function_block,
            CodeRegion::Statement(statement_index),
            ProgramPointKind::Entry,
            context.state.clone(),
        );
        let label = format!("execution proof traversal at statement({statement_index})");
        let preservation_proven = matches!(
            loop_preservation_source,
            LoopPreservationSource::ExecutionProof
        );
        let final_exit_candidates = loop_final_exit_candidates
            .and_then(|candidates| candidates.get(context_index))
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let break_exits = loop_break_exits
            .and_then(|exits| exits.get(context_index))
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
        let (transitions, loop_rule) = match (initialization_proven, preservation_proven) {
            (false, false) => certified_statement_transitions(
                &context.state,
                &context.pure_facts,
                statement,
                environment.function_environment,
                Some(environment.predicate_environment),
                CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
                &label,
                &mut context.next_opaque_call,
                &mut context.next_kernel_variable,
                StatementPrerequisitePolicy::Contextual,
                StatementFactTransportPolicy::Automatic,
                None,
            )?,
            _ => certified_loop_exit_transitions_with_proven_phases(
                &context.state,
                &context.pure_facts,
                statement,
                environment.function_environment,
                Some(environment.predicate_environment),
                &label,
                initialization_proven,
                preservation_proven,
                final_exit_candidates,
                break_exits,
                &mut context.next_opaque_call,
                &mut context.next_kernel_variable,
            )?,
        };
        if matches!(statement, CStatement::While { .. }) {
            let loop_index = loop_index.ok_or_else(|| {
                ClickError::new(format!(
                    "execution proof traversal source statement({statement_index}) is a loop without a loop index"
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
                    "`{}` loop({loop_index}) did not produce an obligation-free verified loop rule{}",
                    environment.function_block.signature().name(),
                    if unresolved.is_empty() {
                        String::new()
                    } else {
                        format!("; unresolved verification conditions: {}", unresolved.join(", "))
                    }
                ))
            })?;
            verified_loop_rules.push(loop_rule.with_loop_index(loop_index));
        }
        for transition in transitions {
            let mut surface_propositions = context.surface_propositions.clone();
            let mut recorded_snapshots = context.recorded_snapshots.clone();
            if let CStatementOutcome::Normal(exit_state)
            | CStatementOutcome::Return {
                state: exit_state, ..
            } = &transition.outcome
            {
                record_code_region_program_snapshot_state(
                    &mut recorded_snapshots,
                    environment.function_block,
                    CodeRegion::Statement(statement_index),
                    ProgramPointKind::Exit,
                    exit_state.clone(),
                );
            }
            if matches!(statement, CStatement::While { .. }) {
                let loop_index = loop_index.expect("a while statement has a checked loop index");
                let loop_labels = environment
                    .function_block
                    .structural_clauses()
                    .iter()
                    .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
                    .filter_map(StructuralClause::label)
                    .map(str::to_string)
                    .collect::<Vec<_>>();
                let entry_point = ProgramPointRef {
                    region: CodeRegionRef::Loop(loop_index),
                    kind: ProgramPointKind::Entry,
                };
                recorded_snapshots.insert(entry_point, context.state.clone());
                for label in &loop_labels {
                    recorded_snapshots.insert(
                        ProgramPointRef {
                            region: CodeRegionRef::Label(label.clone()),
                            kind: ProgramPointKind::Entry,
                        },
                        context.state.clone(),
                    );
                }
                if let CStatementOutcome::Normal(exit_state) = &transition.outcome {
                    let exit_point = ProgramPointRef {
                        region: CodeRegionRef::Loop(loop_index),
                        kind: ProgramPointKind::Exit,
                    };
                    recorded_snapshots.insert(exit_point.clone(), exit_state.clone());
                    for label in &loop_labels {
                        recorded_snapshots.insert(
                            ProgramPointRef {
                                region: CodeRegionRef::Label(label.clone()),
                                kind: ProgramPointKind::Exit,
                            },
                            exit_state.clone(),
                        );
                    }
                    if let Some(loop_clause) = environment
                        .function_block
                        .structural_clauses()
                        .iter()
                        .find(|clause| clause.region() == &CodeRegion::Loop(loop_index))
                    {
                        record_loop_exit_invariants(
                            &mut surface_propositions,
                            loop_clause,
                            &transition.loop_invariant_correspondence,
                            loop_index,
                        )?;
                    }
                    if let CStatement::While { condition, .. } = statement {
                        let exit_condition =
                            ClickProposition::Not(Box::new(surface_c_condition(condition)));
                        let lowered_exit_condition = lower_fixed_state_proposition(
                            &exit_condition,
                            &transition.pure_facts,
                            environment.parsed_function.parameters(),
                            environment.arguments,
                            environment.initial_state,
                            exit_state,
                            None,
                            &recorded_snapshots,
                            environment.predicate_environment,
                            environment.click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "could not lower loop({loop_index}) exit condition provenance: {message}"
                            ))
                        })?;
                        if transition.pure_facts.contains(&lowered_exit_condition) {
                            let exit_surface = surface_at_snapshot(&exit_condition, &exit_point)?;
                            surface_propositions
                                .record_lowering(&exit_surface, &lowered_exit_condition)?;
                        }
                    }
                }
            }
            match transition.outcome {
                CStatementOutcome::Normal(state) => advanced.push(PlanningExecutionContext {
                    state,
                    pure_facts: transition.pure_facts,
                    surface_propositions,
                    recorded_snapshots,
                    case_path: context.case_path.clone(),
                    next_opaque_call: context.next_opaque_call,
                    next_kernel_variable: context.next_kernel_variable,
                    resume_at_statement: None,
                }),
                CStatementOutcome::Jump { target, state } => {
                    let target = environment.function.control_target(target).ok_or_else(|| {
                        ClickError::new("execution proof traversal produced an unknown goto target")
                    })?;
                    advanced.push(PlanningExecutionContext {
                        state,
                        pure_facts: transition.pure_facts,
                        surface_propositions,
                        recorded_snapshots,
                        case_path: context.case_path.clone(),
                        next_opaque_call: context.next_opaque_call,
                        next_kernel_variable: context.next_kernel_variable,
                        resume_at_statement: Some(target.statement_index),
                    });
                }
                CStatementOutcome::Break(_)
                | CStatementOutcome::Continue(_)
                | CStatementOutcome::Throw { .. }
                | CStatementOutcome::Return { .. } => {}
                CStatementOutcome::VerificationDiverges => {}
                CStatementOutcome::UndefinedBehavior(kind) => {
                    return Err(ClickError::new(format!(
                        "execution proof traversal for {} statement({statement_index}) produced undefined behavior: {}",
                        environment.function_block.signature().name(),
                        kind.description()
                    )));
                }
                CStatementOutcome::RuntimeError(error) => {
                    return Err(ClickError::new(format!(
                        "execution proof traversal for {} statement({statement_index}) produced runtime error: {}\nresource facts in context: {}",
                        environment.function_block.signature().name(),
                        describe_runtime_error(&error, &[], &[]),
                        context.state.resources().facts().len()
                    )));
                }
            }
        }
    }
    Ok(advanced)
}
