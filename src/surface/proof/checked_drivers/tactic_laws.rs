use super::*;
use crate::kernel::prove_pure_proposition_from_context;
use crate::surface::proof::proof_object::ExecutionProofState;

/// The one mid-execution `have` law: checked fixed-state proof first, generated
/// smart plan second, direct derivation last, with the entry-prerequisite,
/// surface-lowering, and certificate-fact recording every caller shares.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn check_mid_execution_have(
    have: &ProofHave,
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    pure_facts: &mut Vec<Proposition>,
) -> Result<Option<ProofCertificate>, ClickError> {
    let function_block = proof_context.function_block;
    let parsed_function = proof_context.parsed_function;
    let arguments = proof_context.arguments;
    let predicate_environment = proof_context.predicate_environment;
    let click_function_environment = proof_context.click_function_environment;
    let theorem_environment = proof_context.theorem_environment;
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;

    let state: &CState = &execution.core.state;
    let unfolded_predicates: &[String] = &execution.core.unfolded_predicates;

    let _have_span =
        crate::instrumentation::OperationTiming::new("have", claim_label, "contract have check");
    let mut have_facts = pure_facts.clone();
    have_facts.extend(
        execution
            .core
            .effect_facts
            .iter()
            .map(|fact| fact.proposition().clone()),
    );
    for fact in execution.presentation.surface_propositions.kernel_facts() {
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
        proof_context.old_reference_state(&execution.core.frontier, state),
        &state,
        None,
        None,
        ExecutionView::new(
            &execution.core.frontier,
            &execution.core.effect_facts,
            &execution.presentation.recorded_snapshots,
            &execution.presentation.surface_propositions,
            proof_context.constants.function_entry_state.as_ref(),
        ),
        &execution.presentation.surface_propositions,
        predicate_environment,
        click_function_environment,
        function_block.requires(),
        function_block.requirement_label_indices(),
        None,
        unfolded_predicates,
    )?;
    let smart_unfolds = smart_simp_unfold_prefix(&have.proof);
    // Search may materialize a Surface-expressible operation
    // plan, but the goal is proved only when those operations
    // advance the checked fixed-state Proof below.
    let smart_result = match (&checked_proof_result, &smart_unfolds) {
        (Some(_), _) => None,
        (None, Some(unfolded_predicates)) => {
            let checked_goal = lower_fixed_state_proposition(
                &have.proposition,
                &facts_for_simple_goal_lowering(&have_facts),
                parsed_function.parameters(),
                arguments,
                proof_context.old_reference_state(&execution.core.frontier, state),
                state,
                None,
                &execution.presentation.recorded_snapshots,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` have proof {tactic_index}: could not lower pure goal: {message}"
                ))
            })?;
            Some(construct_smart_have_plan(
                ExecutionView::new(
                    &execution.core.frontier,
                    &execution.core.effect_facts,
                    &execution.presentation.recorded_snapshots,
                    &execution.presentation.surface_propositions,
                    proof_context.constants.function_entry_state.as_ref(),
                ),
                state,
                &have_facts,
                parsed_function.parameters(),
                arguments,
                predicate_environment,
                click_function_environment,
                have,
                claim_label,
                tactic_index,
                unfolded_predicates,
                &checked_goal,
            )?)
        }
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
                        proof_context.old_reference_state(&execution.core.frontier, state),
                        &state,
                        None,
                        None,
                        ExecutionView::new(
        &execution.core.frontier,
        &execution.core.effect_facts,
        &execution.presentation.recorded_snapshots,
        &execution.presentation.surface_propositions,
        proof_context.constants.function_entry_state.as_ref(),
    ),
                        &execution.presentation.surface_propositions,
                        predicate_environment,
                        click_function_environment,
                        function_block.requires(),
                        function_block.requirement_label_indices(),
                        Some((&fact, &proof)),
                        unfolded_predicates,
                    )?
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "`{claim_label}` have proof {tactic_index}: generated smart operations did not produce a checked Proof"
                        ))
                    })?;
            (checked.0, checked.1)
        }
        (None, None) => {
            let fact = prove_have_in_current_state(
                have,
                theorem_environment,
                claim_label,
                tactic_index,
                &have_facts,
                &execution.core.effect_facts,
                parsed_function.parameters(),
                arguments,
                proof_context.old_reference_state(&execution.core.frontier, state),
                &state,
                &execution.presentation.recorded_snapshots,
                &execution.presentation.surface_propositions,
                predicate_environment,
                click_function_environment,
                function_block.requires(),
            )?;
            (fact, None)
        }
    };
    let retained_certificate = surface_certificate;
    // Carry any kernel-issued standard-theorem authority selected
    // inside the fixed-state Proof back to the enclosing entry proof.
    if execution
        .core
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
            if let Some(derivation) = kernel_standard_theorem_derivation_in_current_state(
                theorem_environment,
                application,
                parsed_function.parameters(),
                arguments,
                proof_context.old_reference_state(&execution.core.frontier, state),
                &state,
                &execution.presentation.recorded_snapshots,
                predicate_environment,
                click_function_environment,
                &have_facts,
            )? {
                let mut conclusion = derivation.proposition();
                while let Proposition::Implies(_, body) = conclusion {
                    conclusion = body;
                }
                execution
                    .core
                    .function_entry_execution_prerequisites
                    .insert(conclusion.clone());
                execution.core.function_entry_derivations.insert(derivation);
            }
        }
    }
    // Record the search-time lowering only after the selected
    // Surface operations have closed the checked Proof. Recording
    // it earlier could make a nontrivial snapshot equality appear
    // reflexive and circularly validate `normalize()`.
    execution
        .presentation
        .surface_propositions
        .record_lowering(&have.proposition, &fact)?;
    if execution
        .core
        .frontier
        .execution_start_state
        .as_ref()
        .is_none_or(|start| start == state)
        && let Some(derivation) =
            prove_pure_proposition_from_context(&assumptions_from_propositions(&have_facts), &fact)
    {
        execution
            .core
            .function_entry_execution_prerequisites
            .insert(fact.clone());
        execution.core.function_entry_derivations.insert(derivation);
    }
    if !pure_facts.contains(&fact) {
        pure_facts.push(fact.clone());
    }
    Ok(retained_certificate)
}

pub(in crate::surface::proof) fn execute_frontier_local_loop(
    expansion_capture: Option<&mut ExpansionCapture>,
    loop_template: &StructuralClause,
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut Vec<Proposition>,
    source_index: usize,
) -> Result<StructuralClause, ClickError> {
    let function_block = proof_context.function_block;
    let parsed_function = proof_context.parsed_function;
    let function_environment = proof_context.function_environment;
    let predicate_environment = proof_context.predicate_environment;
    let click_function_environment = proof_context.click_function_environment;
    let resource_environment = proof_context.resource_environment;
    let theorem_environment = proof_context.theorem_environment;
    let arguments = proof_context.arguments;
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;

    let state: &mut CState = &mut execution.core.state;
    let unfolded_predicates: &[String] = &execution.core.unfolded_predicates;

    if execution.core.frontier.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `loop` requires the execution frontier to be at a loop, but execution has reached function exit"
        )));
    }
    let statement_index = execution.core.frontier.next_statement_index;
    let source_region = proof_context.constants.source_layout.statement(statement_index).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `loop` could not resolve source statement({statement_index})"
        ))
    })?;
    let SourceStatementKind::Loop { loop_index } = source_region.kind else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `loop` requires the execution frontier to be at a loop; current frontier is statement({statement_index})"
        )));
    };
    if execution
        .presentation
        .frontier_loop_clauses
        .iter()
        .any(|clause| clause.region() == &CodeRegion::Loop(loop_index))
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: loop({loop_index}) already has a frontier-local proof on this execution path"
        )));
    }
    let function_with_prior_loops = function_block
        .with_bound_frontier_loop_clauses(&execution.presentation.frontier_loop_clauses.to_vec());
    let bound_function_block =
        function_with_prior_loops.with_frontier_loop_clause(loop_template, loop_index);
    validate_region_proof_clauses(&bound_function_block, parsed_function)?;

    let initial_state = execution.core.frontier.execution_start_state(state).clone();
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
    if execution.core.frontier.is_at_function_entry() {
        let entry_state = c_function_entry_state(&initial_state, &annotated, arguments)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `loop` could not bind function arguments"
                ))
            })?;
        execution.core.frontier.execution_start_state = Some(initial_state.clone());
        execution.core.frontier.position = FrontierPosition::StatementEntry {
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
        proof_context.constants.proof_site.clone(),
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
        surface_propositions: &execution.presentation.surface_propositions,
        source_layout: &source_layout,
        frontier_loop_certificates: Some(&loop_certificates),
        frontier_loop_source: Some(&loop_source),
    };
    let case_path = execution
        .presentation
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
                    if unfolded_predicates.contains(name)
            )
        })
        .cloned()
        .collect();
    let _exit_contexts = verify_execution_proofs_forward(
        expansion_capture,
        &current_loop,
        vec![PlanningExecutionContext {
            state: state.clone(),
            pure_facts: loop_pure_facts,
            surface_propositions: execution.presentation.surface_propositions.clone(),
            recorded_snapshots: execution.presentation.recorded_snapshots.clone(),
            case_path,
            next_opaque_call: execution.core.next_opaque_call,
            next_kernel_variable: execution.core.next_kernel_variable,
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
        execution
            .core
            .frontier_loop_rules
            .iter()
            .cloned()
            .chain(std::iter::once(loop_rule.clone())),
    );

    if let FrontierPosition::StatementEntry { remaining } = &execution.core.frontier.position {
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
        execution.core.frontier.position = FrontierPosition::StatementEntry {
            remaining: sequence_from_statements(&statements)
                .expect("the current loop always contributes one statement")
                .into(),
        };
    }

    let loop_context = proof_context.with_loop_binding(
        &bound_function_block,
        &annotated,
        &local_function_environment,
    );
    let assumptions = assumptions_from_propositions(available_pure_facts);
    execute_step_from_frontier_position(
        execution,
        &loop_context,
        available_pure_facts,
        &assumptions,
        "loop",
        StatementPrerequisitePolicy::Exact,
        StatementFactTransportPolicy::Automatic,
        LoopStepPolicy::ApplyVerifiedRule,
        None,
    )?;
    let state: &mut CState = &mut execution.core.state;
    if let Some(exit_condition) = loop_exit_condition {
        let exit_point = ProgramPointRef {
            region: CodeRegionRef::Loop(loop_index),
            kind: ProgramPointKind::Exit,
        };
        let lowered_exit_condition = lower_fixed_state_proposition(
            &exit_condition,
            available_pure_facts,
            parsed_function.parameters(),
            arguments,
            &initial_state,
            state,
            None,
            &execution.presentation.recorded_snapshots,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not lower loop({loop_index}) exit condition provenance: {message}"
            ))
        })?;
        if available_pure_facts.contains(&lowered_exit_condition) {
            let exit_surface = surface_at_snapshot(&exit_condition, &exit_point)?;
            execution
                .presentation
                .surface_propositions
                .record_lowering(&exit_surface, &lowered_exit_condition)?;
        }
    }
    execution
        .presentation
        .frontier_loop_clauses
        .push(loop_template.bound_to_loop(loop_index));
    execution.core.frontier_loop_rules.push(loop_rule);
    Ok(expanded_loop)
}

/// The premise planner is only a query. The theorem application advances
/// through `Proof::apply_step`, so the returned certificate is the provenance
/// of the semantic work already performed, not a second representation that
/// ordinary verification must check.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn checked_have_with_proof(
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
    view: ExecutionView<'_>,
    surface_propositions: &SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    original_requirements: &[Requirement],
    requirement_label_indices: &BTreeMap<String, usize>,
    generated_plan: Option<(&Proposition, &SourceProof)>,
    unfolded_predicates: &[String],
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
            let goal = lower_fixed_state_proposition(
                &have.proposition,
                &facts_for_simple_goal_lowering(available),
                parameters,
                arguments,
                pre_state,
                state,
                result,
                &view.recorded_snapshots,
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
    let proof = Proof::for_fixed_state_surface_goal_with_requirements(
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
        &view.recorded_snapshots,
        surface_propositions,
        predicate_environment,
        click_function_environment,
        theorem_environment,
        unfolded_predicates,
        &view.effect_facts,
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
    let body = proof.completed_certificate()?;
    let certificate = ProofCertificate::from_steps(vec![ProofStep::Have {
        proposition: have.proposition.clone(),
        proof: Box::new(body),
    }]);
    Ok(Some((goal, Some(certificate))))
}
