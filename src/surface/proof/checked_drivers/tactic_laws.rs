use super::*;
use crate::surface::proof::proof_object::ExecutionProofState;

pub(in crate::surface::proof) fn execute_frontier_local_loop(
    expansion_capture: Option<&mut ExpansionCapture>,
    loop_template: &StructuralClause,
    proof_locals: &BTreeMap<String, ContractExpression>,
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
    // The loop's clauses were written inside this frontier's proof scope: a
    // proof `match` arm's bindings, `let { ... } = unfold(...)` names, call-result
    // binders. The bound clause keeps its written spelling, which expansion
    // prints, and carries that scope, which every lowering of it resolves.
    let scoped_template = loop_template.with_scope(proof_locals.clone());
    let mut current_loop_clauses = vec![scoped_template.bound_to_loop(loop_index)];
    let mut nested_loop_clauses = Vec::new();
    for proof in [
        loop_template.initialize_proof(),
        loop_template.preserve_proof(),
    ]
    .into_iter()
    .flatten()
    {
        proof.collect_termination_loop_clauses(&mut nested_loop_clauses);
    }
    for (offset, clause) in nested_loop_clauses.into_iter().enumerate() {
        current_loop_clauses.push(
            clause
                .with_scope(proof_locals.clone())
                .bound_to_loop(loop_index + offset + 1),
        );
    }
    let bound_function_block = function_with_prior_loops
        .with_frontier_loop_clause(&scoped_template, loop_index)
        .with_bound_frontier_loop_clauses(&current_loop_clauses[1..]);
    validate_region_proof_clauses(&bound_function_block, parsed_function)?;

    let initial_state = execution.core.frontier.execution_start_state(state).clone();
    // Re-annotation of a frontier-local loop must carry the proof's original
    // entry facts. Current frontier facts may include body/post observations;
    // those are never allowed to establish an inherited resource frame.
    let entry_assumptions =
        assumptions_from_propositions(proof_context.constants.execution_start_facts.as_slice());
    // The frame comes from the contract's checked entry transition, so it is
    // evaluated at the checked function-entry state rather than at the
    // frontier's start state: a proof that unfolds a consumed instance before
    // its first `step()` no longer owns that instance where the frontier
    // begins, and re-evaluating the transition there would fail on a proof
    // step that is none of the frame's business.
    let annotated = annotated_function_with_assumptions(
        &bound_function_block,
        parsed_function,
        &initial_state,
        arguments,
        predicate_environment,
        click_function_environment,
        resource_environment,
        Some(ResourceFrameEntry {
            assumptions: &entry_assumptions,
            checked_entry_state: proof_context.constants.function_entry_state.as_ref(),
        }),
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

    let source_layout = SourceExecutionLayout::for_function(parsed_function)?;
    let loop_certificates = std::cell::RefCell::new(LoopProofCertificates::default());
    let loop_source = FrontierLoopProofSource::new(
        loop_template,
        proof_context.constants.proof_site.clone(),
        claim_label,
        source_index,
    );
    // `old(...)` in this loop's clauses is the function entry, not the point
    // the C execution happened to start from. A proof that unfolds a binder
    // before its first `step()` starts the frontier in a state that does not
    // hold the instance at all, and one that refolds it there starts in a
    // state holding a later generation; reading `old(name.field)` out of
    // either makes the same invariant mean two different things. The checked
    // contract entry state is the one reference, exactly as
    // `ExecutionProofContext::old_reference_state` resolves it elsewhere.
    let old_reference_state = proof_context
        .constants
        .function_entry_state
        .clone()
        .unwrap_or_else(|| initial_state.clone());
    let proof_environment = ExecutionProofEnvironment {
        initial_state: &old_reference_state,
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
        function_source_registry: proof_context.function_source_registry(),
        frontier_loop_certificates: Some(&loop_certificates),
        frontier_loop_source: Some(&loop_source),
        proof_locals: proof_locals.clone(),
    };
    let case_path = execution
        .presentation
        .case_assumptions
        .iter()
        .map(|choice| ProofCaseChoice {
            condition: choice.condition.clone(),
            value: choice.value,
            match_arm: choice.match_arm.clone(),
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
            next_kernel_variable: execution.core.kernel_variable_mark(),
            resume_at_statement: None,
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
        .with_loop_index(loop_index)
        .with_composite_resource_definitions(
            annotated.composite_resource_definitions().iter().cloned(),
        );
    for rule in verified_loop_rules {
        execution.core.frontier_loop_rules.push(rule);
    }
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
    if let Some(exit_condition) = loop_exit_condition.filter(|_| {
        execution
            .presentation
            .recorded_snapshots
            .get(&SnapshotSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Loop(loop_index),
                kind: ProgramPointKind::Exit,
            }))
            .is_some()
    }) {
        let exit_point = ProgramPointRef {
            region: CodeRegionRef::Loop(loop_index),
            kind: ProgramPointKind::Exit,
        };
        let exit_surface = surface_at_snapshot(&exit_condition, &exit_point)?;
        let lowered_exit_condition = lower_fixed_state_proposition(
            &exit_surface,
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
            execution
                .presentation
                .surface_propositions
                .record_lowering(&exit_surface, &lowered_exit_condition)?;
        }
    }
    execution
        .presentation
        .frontier_loop_clauses
        .push(scoped_template.bound_to_loop(loop_index));
    execution.core.frontier_loop_rules.push(loop_rule);
    Ok(expanded_loop)
}
