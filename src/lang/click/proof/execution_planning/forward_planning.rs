use super::*;

pub(in crate::lang::click::proof) fn verify_execution_proofs_forward(
    statement: &CStatement,
    contexts: Vec<ExecutionProofContext>,
    next_statement_index: &mut usize,
    next_loop_index: &mut usize,
    environment: &ExecutionProofEnvironment<'_>,
    verified_loop_rules: &mut Vec<CVerifiedLoopRule>,
) -> Result<Vec<ExecutionProofContext>, ClickError> {
    match statement {
        CStatement::Seq(first, second) => {
            let contexts = verify_execution_proofs_forward(
                first,
                contexts,
                next_statement_index,
                next_loop_index,
                environment,
                verified_loop_rules,
            )?;
            verify_execution_proofs_forward(
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
            let (then_contexts, else_contexts) =
                split_execution_proof_branch_contexts(condition, contexts)?;
            *next_statement_index = then_statement_index;
            let mut joined = verify_execution_proofs_forward(
                then_branch,
                then_contexts,
                next_statement_index,
                next_loop_index,
                environment,
                verified_loop_rules,
            )?;
            *next_statement_index = else_statement_index;
            joined.extend(verify_execution_proofs_forward(
                else_branch,
                else_contexts,
                next_statement_index,
                next_loop_index,
                environment,
                verified_loop_rules,
            )?);
            *next_statement_index = source_region.continuation_node;
            Ok(joined)
        }
        CStatement::While {
            condition,
            invariant_checks,
            effect_checks,
            body,
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
            let loop_clause = environment
                .function_block
                .structural_clauses()
                .iter()
                .find(|clause| clause.region() == &CodeRegion::Loop(loop_index));
            let explicit_tactics = loop_clause.and_then(explicit_loop_preservation_tactics);
            let default_initialization = Proof::Default;
            let initialization_proof = loop_clause.map(|clause| {
                (
                    clause,
                    clause.initialize_proof().unwrap_or(&default_initialization),
                )
            });
            let mut iteration_contexts = Vec::new();
            let mut initialization_path_certificates = Vec::new();
            let mut preservation_path_certificates = Vec::new();
            let mut effect_path_certificates = BTreeMap::<usize, Vec<PathCertificate>>::new();
            for context in &contexts {
                let assumptions = assumptions_from_propositions(&context.pure_facts);
                if let Some((clause, proof)) = initialization_proof {
                    let certificate = verify_loop_initialization_pure_proof(
                        loop_index,
                        proof,
                        clause,
                        context,
                        invariant_checks,
                        environment,
                    )?;
                    initialization_path_certificates.push(PathCertificate {
                        case_path: context.case_path.clone(),
                        certificate,
                    });
                } else {
                    c_loop_invariants_hold_at_entry(&context.state, invariant_checks, &assumptions)
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{}.loop({loop_index}).initialize`: {message}",
                                environment.function_block.signature().name()
                            ))
                        })?;
                }
                let preservation_contexts = c_loop_preservation_contexts(
                    &context.state,
                    condition,
                    invariant_checks,
                    effect_checks,
                    body,
                    &assumptions,
                )
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
                                    .and_then(Proof::tactics)
                                    .unwrap_or_default()
                                    .iter()
                                    .filter(|tactic| {
                                        matches!(tactic, ProofTactic::UnfoldPredicate(_))
                                    })
                                    .cloned()
                                    .collect::<Vec<_>>();
                                let first_generated_tactic_index = tactics.len();
                                tactics.extend(body_certificate.tactics().iter().cloned());
                                tactics.push(ProofTactic::Simp);
                                (tactics, first_generated_tactic_index)
                            };
                        let result = verify_one_loop_preservation_proof(
                            loop_index,
                            &preservation_tactics,
                            first_generated_tactic_index,
                            &preservation,
                            &pure_facts,
                            invariant_checks,
                            effect_checks,
                            body,
                            environment,
                        )?;
                        preservation_path_certificates.push(PathCertificate {
                            case_path: context.case_path.clone(),
                            certificate: result.certificate,
                        });
                        for (item_index, certificate) in result.effect_certificates {
                            effect_path_certificates
                                .entry(item_index)
                                .or_default()
                                .push(PathCertificate {
                                    case_path: context.case_path.clone(),
                                    certificate,
                                });
                        }
                    }
                    iteration_contexts.push(ExecutionProofContext {
                        state: preservation.state().clone(),
                        pure_facts,
                        surface_propositions: context.surface_propositions.clone(),
                        program_point_states: context.program_point_states.clone(),
                        case_path: context.case_path.clone(),
                        next_opaque_call: context.next_opaque_call,
                        next_verification_variable: context.next_verification_variable,
                    });
                }
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
                    if let Some(phase_start) = selected_source_index
                        && let Some(selected) = selected_tactic_index_for_site(&site)
                        && let Some(local_index) = selected.checked_sub(phase_start)
                        // The parser keeps a single smart tactic as `Tactic`
                        // rather than wrapping it in a one-item `Script`.
                        && initialization_proof.is_some_and(|(_, proof)| match proof {
                            Proof::Tactic(SmartTactic::Simp) => local_index == 0,
                            Proof::Script(source_tactics) => {
                                selected == phase_start
                                    || matches!(
                                        source_tactics.get(local_index),
                                        Some(ProofTactic::Simp)
                                    )
                            }
                            _ => false,
                        })
                    {
                        record_proof_site_tactic_expansion(
                            &site,
                            selected,
                            initialization_certificate.tactics(),
                        );
                    }
                } else {
                    if let Some(source_index) = selected_tactic_index_for_site(&site)
                        && let Some((_, Proof::Script(source_tactics))) = initialization_proof
                        && matches!(source_tactics.get(source_index), Some(ProofTactic::Simp))
                        && !source_tactics.iter().any(|tactic| {
                            matches!(
                                tactic,
                                ProofTactic::ApplyTheorem(_)
                                    | ProofTactic::ApplyTheoremUsing { .. }
                            )
                        })
                    {
                        record_proof_site_tactic_expansion(
                            &site,
                            source_index,
                            initialization_certificate.tactics(),
                        );
                    }
                    finish_proof_site_expansion_capture(&site, &initialization_certificate)?;
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
                    )?;
                }
            }
            for (item_index, paths) in effect_path_certificates {
                let site = ProofSite::StructuralItem {
                    function_name: environment.function_block.signature().name().to_string(),
                    region: CodeRegion::Loop(loop_index),
                    item_index,
                    kind: environment
                        .function_block
                        .structural_clauses()
                        .iter()
                        .find(|clause| clause.region() == &CodeRegion::Loop(loop_index))
                        .and_then(|clause| clause.items().get(item_index))
                        .map(StructuralItem::kind)
                        .ok_or_else(|| {
                            ClickError::new(format!(
                                "`{}.loop({loop_index})`: certified an effect for item {item_index}, which the loop region does not declare",
                                environment.function_block.signature().name()
                            ))
                        })?,
                };
                let certificate = merge_path_aligned_certificates(&site.description(), paths)?;
                if let Some(certificates) = environment.frontier_loop_certificates {
                    certificates
                        .borrow_mut()
                        .effects
                        .insert(item_index, certificate.clone());
                }
                finish_proof_site_expansion_capture(&site, &certificate)?;
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
                initialization_proof.is_some(),
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
            Ok(Vec::new())
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
            advance_execution_proof_statement(
                statement,
                contexts,
                statement_index,
                None,
                environment,
                verified_loop_rules,
                LoopPreservationSource::Automatic,
                false,
            )
        }
    }
}

fn split_execution_proof_branch_contexts(
    condition: &CExpression,
    contexts: Vec<ExecutionProofContext>,
) -> Result<(Vec<ExecutionProofContext>, Vec<ExecutionProofContext>), ClickError> {
    let mut then_contexts = Vec::new();
    let mut else_contexts = Vec::new();
    for context in contexts {
        for transition in certified_condition_transitions(
            &context.state,
            &context.pure_facts,
            condition,
            "execution proof traversal",
            StatementPrerequisitePolicy::Contextual,
            &[],
            true,
        )? {
            let next = ExecutionProofContext {
                state: context.state.clone(),
                pure_facts: transition.pure_facts,
                surface_propositions: context.surface_propositions.clone(),
                program_point_states: context.program_point_states.clone(),
                case_path: {
                    let mut case_path = context.case_path.clone();
                    case_path.push(ProofCaseChoice {
                        condition: surface_c_condition(condition),
                        value: transition.is_true,
                    });
                    case_path
                },
                next_opaque_call: context.next_opaque_call,
                next_verification_variable: context.next_verification_variable,
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

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn plan_point_pure_goal_certificate(
    proof_site: &ProofSite,
    proposition: &ClickProposition,
    proof: &Proof,
    claim_label: &str,
    proof_index: usize,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    program_point_states: &ProgramPointStates,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    surface_propositions: &SurfacePropositionMap,
    prelowered_goal: Option<&Proposition>,
    theorem_environment: &TheoremEnvironment,
) -> Result<(Proposition, TacticCertificate), ClickError> {
    let applied_theorem_script;
    let lowered_applied_theorem_script = matches!(proof, Proof::Script(tactics)
    if tactics.iter().any(|tactic| matches!(
        tactic,
        ProofTactic::ApplyTheorem(_) | ProofTactic::ApplyTheoremUsing { .. }
    ))
        && tactics.iter().all(|tactic| {
            matches!(tactic.class(), TacticClass::Simple(_))
                || matches!(tactic, ProofTactic::Simp | ProofTactic::ApplyTheorem(_))
        }));
    let proof = if let Proof::Script(tactics) = proof
        && tactics.iter().any(|tactic| {
            matches!(
                tactic,
                ProofTactic::ApplyTheorem(_) | ProofTactic::ApplyTheoremUsing { .. }
            )
        })
        && tactics.iter().all(|tactic| {
            matches!(tactic.class(), TacticClass::Simple(_))
                || matches!(tactic, ProofTactic::Simp | ProofTactic::ApplyTheorem(_))
        }) {
        // An applied theorem's conclusion becomes an available fact, so the
        // trailing smart `simp` lowers to the deterministic `assumption` and
        // a bare `apply` lowers to `apply using` with the theorem's own
        // requires as the explicit premise pool.
        applied_theorem_script = Proof::Script(
            tactics
                .iter()
                .map(|tactic| match tactic {
                    ProofTactic::Simp => ProofTactic::Assumption,
                    ProofTactic::ApplyTheorem(application) => {
                        let premises = theorem_environment
                            .get(&application.name)
                            .map(|theorem| {
                                theorem
                                    .requires()
                                    .iter()
                                    .filter_map(Requirement::proposition)
                                    .cloned()
                                    .collect()
                            })
                            .unwrap_or_default();
                        ProofTactic::ApplyTheoremUsing {
                            application: application.clone(),
                            premises,
                        }
                    }
                    other => other.clone(),
                })
                .collect(),
        );
        &applied_theorem_script
    } else {
        proof
    };
    if let Proof::Script(tactics) = proof
        && let Ok(certificate) = TacticCertificate::from_proof_tactics(tactics)
    {
        if lowered_applied_theorem_script
            && let Some(source_index) = selected_tactic_index_for_site(proof_site)
            && let Some(tactic) = certificate.tactics().get(source_index)
        {
            record_proof_site_tactic_expansion(
                proof_site,
                source_index,
                std::slice::from_ref(tactic),
            );
        }
        let fact = if let Some(prelowered_goal) = prelowered_goal {
            prelowered_goal.clone()
        } else {
            lower_point_proposition(
                proposition,
                available,
                parameters,
                arguments,
                pre_state,
                state,
                None,
                program_point_states,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` proof {proof_index}: could not lower pure goal: {message}"
                ))
            })?
        };
        return Ok((fact, certificate));
    }

    let unfolded_predicates = smart_simp_unfold_prefix(proof).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` proof {proof_index} contains a smart pure proof that has no certificate planner"
        ))
    })?;
    let have = ProofHave {
        proposition: proposition.clone(),
        proof: proof.clone(),
    };
    let (fact, plan) = plan_smart_have_at_current_point(
        &have,
        claim_label,
        proof_index,
        available,
        parameters,
        arguments,
        pre_state,
        state,
        program_point_states,
        predicate_environment,
        click_function_environment,
        &unfolded_predicates,
        prelowered_goal,
    )?;
    let mut surface_replay = TacticReplayState {
        surface_propositions: surface_propositions.clone(),
        program_point_states: program_point_states.clone(),
        ..TacticReplayState::default()
    };
    surface_replay
        .surface_propositions
        .record_lowering(proposition, &fact)?;
    if !unfolded_predicates.is_empty() {
        let assumptions = assumptions_from_propositions(available);
        let recorded_unfoldings = surface_replay
            .surface_propositions
            .kernel_facts()
            .flat_map(|kernel| {
                surface_replay
                    .surface_propositions
                    .surfaces(kernel)
                    .filter_map(|surface| {
                        let mut unfolded_surface = unfold_structural_invariant_proposition(
                            predicate_environment,
                            surface,
                            &unfolded_predicates,
                        )
                        .ok()?;
                        if unfolded_surface == *surface {
                            return None;
                        }
                        if let Some(point) = predicate_call_source_site(surface) {
                            unfolded_surface =
                                surface_with_source_site(&unfolded_surface, &point).ok()?;
                        }
                        let unfolded_kernel = unfold_predicates_in_proposition(
                            predicate_environment,
                            click_function_environment,
                            &unfolded_predicates,
                            kernel,
                            &assumptions,
                        )
                        .ok()?;
                        let available_kernel = available
                            .iter()
                            .find(|available| {
                                **available == unfolded_kernel
                                    || quantified_binder_equivalent(
                                        &normalize_direct_atomic_memory_loads(&unfolded_kernel),
                                        &normalize_direct_atomic_memory_loads(available),
                                    )
                            })?
                            .clone();
                        Some((unfolded_surface, available_kernel))
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        for (surface, kernel) in recorded_unfoldings {
            surface_replay
                .surface_propositions
                .record_lowering(&surface, &kernel)?;
        }
        let unfolded_surface = unfold_structural_invariant_proposition(
            predicate_environment,
            proposition,
            &unfolded_predicates,
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        let unfolded_fact = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            &unfolded_predicates,
            &fact,
            &assumptions,
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        surface_replay
            .surface_propositions
            .record_lowering(&unfolded_surface, &unfolded_fact)?;
    }
    let surface_proof = surface_simp_plan_proof(
        &mut surface_replay,
        state,
        available,
        parameters,
        arguments,
        predicate_environment,
        click_function_environment,
        proposition,
        &plan,
        &unfolded_predicates,
    )?;
    let Proof::Script(tactics) = surface_proof else {
        return Err(ClickError::new(format!(
            "`{claim_label}` did not lower to an explicit proof script"
        )));
    };
    let certificate = TacticCertificate::from_proof_tactics(&tactics).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` produced an invalid point-pure certificate: {error:?}"
        ))
    })?;
    if matches!(proof_site, ProofSite::StructuralItem { .. })
        && let Proof::Script(source_tactics) = proof
    {
        let source_index = TACTIC_EXPANSION_PROBE.with(|probe| {
            probe
                .borrow()
                .as_ref()
                .filter(|probe| probe.site == *proof_site)
                .and_then(|probe| probe.source_index)
        });
        if let Some(source_index) = source_index
            && matches!(source_tactics.get(source_index), Some(ProofTactic::Simp))
            && source_index <= certificate.tactics().len()
        {
            record_proof_site_tactic_expansion(
                proof_site,
                source_index,
                &certificate.tactics()[source_index..],
            );
        }
    }
    Ok((fact, certificate))
}

fn advance_execution_proof_statement(
    statement: &CStatement,
    contexts: Vec<ExecutionProofContext>,
    statement_index: usize,
    loop_index: Option<usize>,
    environment: &ExecutionProofEnvironment<'_>,
    verified_loop_rules: &mut Vec<CVerifiedLoopRule>,
    loop_preservation_source: LoopPreservationSource,
    initialization_proven: bool,
) -> Result<Vec<ExecutionProofContext>, ClickError> {
    let mut advanced = Vec::new();
    for mut context in contexts {
        record_code_region_program_point_state(
            &mut context.program_point_states,
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
        let (transitions, loop_rule) = match (initialization_proven, preservation_proven) {
            (false, false) => certified_statement_transitions(
                &context.state,
                &context.pure_facts,
                statement,
                environment.function_environment,
                CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
                &label,
                &mut context.next_opaque_call,
                &mut context.next_verification_variable,
                StatementPrerequisitePolicy::Contextual,
                StatementFactTransportPolicy::Automatic,
                &[],
            )?,
            _ => certified_loop_exit_transitions_with_proven_phases(
                &context.state,
                &context.pure_facts,
                statement,
                environment.function_environment,
                &label,
                initialization_proven,
                preservation_proven,
                &mut context.next_opaque_call,
                &mut context.next_verification_variable,
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
            verified_loop_rules.push(loop_rule);
        }
        for transition in transitions {
            let mut surface_propositions = context.surface_propositions.clone();
            let mut program_point_states = context.program_point_states.clone();
            if let CStatementOutcome::Normal(exit_state)
            | CStatementOutcome::Return {
                state: exit_state, ..
            } = &transition.outcome
            {
                record_code_region_program_point_state(
                    &mut program_point_states,
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
                program_point_states.insert(entry_point, context.state.clone());
                for label in &loop_labels {
                    program_point_states.insert(
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
                    program_point_states.insert(exit_point.clone(), exit_state.clone());
                    for label in &loop_labels {
                        program_point_states.insert(
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
                        let mut invariant_targets = transition.pure_facts.iter().filter(|fact| {
                            !context.pure_facts.contains(fact)
                                && !matches!(
                                    fact,
                                    Proposition::CMemoryEffectSummary { .. }
                                        | Proposition::CMemoryMutatesOnly { .. }
                                        | Proposition::CHeapLifetimeRetired { .. }
                                )
                        });
                        for surface in loop_clause
                            .items()
                            .iter()
                            .filter(|item| item.kind() == StructuralItemKind::Invariant)
                            .filter_map(StructuralItem::proposition)
                        {
                            let target = invariant_targets.next().ok_or_else(|| {
                                ClickError::new(format!(
                                    "execution proof traversal loop({loop_index}) omitted an exported fact for an invariant"
                                ))
                            })?;
                            let exit_surface = surface_with_source_site(surface, &exit_point)?;
                            surface_propositions.record_lowering(&exit_surface, target)?;
                        }
                    }
                    if let CStatement::While { condition, .. } = statement {
                        let exit_condition =
                            ClickProposition::Not(Box::new(surface_c_condition(condition)));
                        let lowered_exit_condition = lower_point_proposition(
                            &exit_condition,
                            &transition.pure_facts,
                            environment.parsed_function.parameters(),
                            environment.arguments,
                            environment.initial_state,
                            exit_state,
                            None,
                            &program_point_states,
                            environment.predicate_environment,
                            environment.click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "could not lower loop({loop_index}) exit condition provenance: {message}"
                            ))
                        })?;
                        if transition.pure_facts.contains(&lowered_exit_condition) {
                            let exit_surface =
                                surface_with_source_site(&exit_condition, &exit_point)?;
                            surface_propositions
                                .record_lowering(&exit_surface, &lowered_exit_condition)?;
                        }
                    }
                }
            }
            match transition.outcome {
                CStatementOutcome::Normal(state) => advanced.push(ExecutionProofContext {
                    state,
                    pure_facts: transition.pure_facts,
                    surface_propositions,
                    program_point_states,
                    case_path: context.case_path.clone(),
                    next_opaque_call: context.next_opaque_call,
                    next_verification_variable: context.next_verification_variable,
                }),
                CStatementOutcome::Return { .. } => {}
                CStatementOutcome::VerificationDiverges => {}
                CStatementOutcome::UndefinedBehavior(kind) => {
                    return Err(ClickError::new(format!(
                        "execution proof traversal for {} statement({statement_index}) produced undefined behavior: {kind:?}",
                        environment.function_block.signature().name()
                    )));
                }
                CStatementOutcome::RuntimeError(error) => {
                    return Err(ClickError::new(format!(
                        "execution proof traversal for {} statement({statement_index}) produced runtime error: {error:?}\navailable resources: {:?}",
                        environment.function_block.signature().name(),
                        context.state.resources().facts()
                    )));
                }
            }
        }
    }
    Ok(advanced)
}
