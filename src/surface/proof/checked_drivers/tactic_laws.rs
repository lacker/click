use super::*;
use crate::surface::proof::proof_object::ExecutionProofState;

/// `statement` with its next source operation, the one
/// `split_next_source_operation` takes first, replaced by `replacement`.
fn with_next_source_operation_replaced(
    statement: &ProgramStatement,
    replacement: ProgramStatement,
) -> ProgramStatement {
    match statement {
        ProgramStatement::Seq(statements) => ProgramStatement::Seq(statements.with_statement(
            0,
            Arc::new(with_next_source_operation_replaced(
                statements.first(),
                replacement,
            )),
        )),
        _ => replacement,
    }
}

/// Whether a loop tactic binds no clause beyond its own loop's.
fn nested_loop_clauses_bound(current_loop_clauses: &[StructuralClause]) -> bool {
    current_loop_clauses.len() == 1
}

pub(in crate::surface::proof) fn execute_frontier_local_loop(
    expansion_capture: Option<&mut ExpansionCapture>,
    loop_template: &StructuralClause,
    proof_locals: &BTreeMap<String, ContractExpression>,
    entry_facts: &ProofFacts,
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut PureFactList,
    source_index: usize,
) -> Result<StructuralClause, ClickError> {
    let function_block = proof_context.function_block;
    let parsed_function = proof_context.parsed_function;
    let function_environment = proof_context.function_environment;
    let predicate_environment = proof_context.spec_definitions.predicates;
    let click_function_environment = proof_context.spec_definitions.functions;
    let resource_environment = proof_context.resource_environment;
    let theorem_environment = proof_context.theorem_environment;
    let arguments = proof_context.arguments;
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;

    let state: &mut ExecutionState = &mut execution.core.state;

    if execution.core.frontier.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `loop` requires the execution frontier to be at a loop, but execution has reached function exit"
        )));
    }
    let statement_index = execution.core.frontier.next_statement_index;
    let source_region = proof_context.constants.source_layout.statement(statement_index).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `loop` could not resolve region({statement_index})"
        ))
    })?;
    let SourceStatementKind::Loop { loop_index } = source_region.kind else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `loop` requires the execution frontier to be at a loop; current frontier is region({statement_index})"
        )));
    };
    // Inside a loop's clauses and phases, `iter` is the iterator that loop
    // advances: each clause reads its own loop's.
    let scope_for = |index: usize| {
        let mut scope = proof_locals.clone();
        scope.extend(crate::surface::loop_iterator_bindings(
            function_block.signature(),
            index,
        ));
        scope
    };
    let loop_proof_locals = scope_for(loop_index);
    let _iterator_spelling = crate::surface::diagnostics::LoopPhaseSpelling::enter(loop_index);
    let proof_locals = &loop_proof_locals;
    if execution
        .presentation
        .frontier_loop_clauses
        .binds_loop(loop_index)
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: loop({loop_index}) already has a frontier-local proof on this execution path"
        )));
    }
    // The block with every frontier clause of this path bound. Binding is
    // a fold in order, so when the previous loop's block bound exactly the
    // clauses this path holds now (no nested clause of its own, and only its
    // clause pushed since), that block is this one, already checked.
    let function_with_prior_loops = execution
        .presentation
        .loop_annotation
        .as_deref()
        .filter(|cached| {
            !cached.bound_nested_clauses
                && cached.function_block == std::ptr::from_ref(function_block) as usize
                && execution
                    .presentation
                    .frontier_loop_clauses
                    .suffix_since(&cached.frontier_clauses)
                    .is_some_and(|added| added == [cached.bound_clause.clone()])
        })
        .map_or_else(
            || {
                function_block.with_bound_frontier_loop_clauses(
                    &execution.presentation.frontier_loop_clauses.to_vec(),
                )
            },
            |cached| cached.bound_function_block.clone(),
        );
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
                .with_scope(scope_for(loop_index + offset + 1))
                .bound_to_loop(loop_index + offset + 1),
        );
    }
    let mut bound_function_block = function_with_prior_loops
        .with_frontier_loop_clause(&scoped_template, loop_index)
        .with_bound_frontier_loop_clauses(&current_loop_clauses[1..]);
    refuse_rebound_loop_labels(&bound_function_block, claim_label, tactic_index)?;
    // Each clause's check depends on it and the loop count alone, so the
    // clauses an earlier loop's check passed are not checked again.
    let loop_count = proof_context
        .constants
        .source_layout
        .loop_region_count(|| count_loop_regions(parsed_function));
    let function_name = bound_function_block.signature().name().to_string();
    bound_function_block.validate_structural_clauses(loop_count, |clause| {
        validate_region_proof_clause(&function_name, clause, loop_count)
    })?;

    let initial_state = execution.core.frontier.execution_start_state(state).clone();
    // Re-annotation of a frontier-local loop must carry the proof's original
    // entry facts. Current frontier facts may include body/post observations;
    // those are never allowed to establish an inherited resource frame.
    let entry_assumptions =
        assumptions_from_propositions(&*proof_context.constants.execution_start_facts);
    // The frame comes from the contract's checked entry transition, so it is
    // evaluated at the checked function-entry state rather than at the
    // frontier's start state: a proof that unfolds a consumed instance before
    // its first `step()` no longer owns that instance where the frontier
    // begins, and re-evaluating the transition there would fail on a proof
    // step that is none of the frame's business.
    // The proof's own layout of this function: built once for the claim,
    // with the whole-function indexes every loop reads.
    let source_layout = proof_context.constants.source_layout.clone();
    let frame_entry = Some(ResourceFrameEntry {
        assumptions: &entry_assumptions,
        checked_entry_state: proof_context.constants.function_entry_state.as_ref(),
    });
    let pointer_element_types =
        source_layout.local_pointer_element_types(|| local_pointer_element_types(parsed_function));
    // The previous loop's annotation of this function, when this loop's
    // block differs from that one's only by this loop's own clause: the
    // previous loop's clause is the one frontier clause bound since, this
    // loop binds no nested clause and no label, and every other input is the
    // one the previous annotation was made from.
    let extendable = execution
        .presentation
        .loop_annotation
        .as_deref()
        .filter(|cached| {
            nested_loop_clauses_bound(&current_loop_clauses)
                && scoped_template.label().is_none()
                && cached.function_block == std::ptr::from_ref(function_block) as usize
                && cached.parsed_function == std::ptr::from_ref(parsed_function) as usize
                && Arc::ptr_eq(
                    &cached.start_facts,
                    &proof_context.constants.execution_start_facts,
                )
                && cached.function_entry_state == proof_context.constants.function_entry_state
                && cached.initial_state == initial_state
                && cached.arguments.as_slice() == arguments
                && execution
                    .presentation
                    .frontier_loop_clauses
                    .suffix_since(&cached.frontier_clauses)
                    .is_some_and(|added| added == [cached.bound_clause.clone()])
        });
    let spliced = match extendable {
        Some(cached) => annotated_loop_function_extending(
            &cached.annotation,
            &bound_function_block,
            parsed_function,
            &initial_state,
            arguments,
            SpecDefinitions::new(predicate_environment, click_function_environment),
            frame_entry,
            Some(pointer_element_types),
            loop_index,
        )?,
        None => None,
    };
    let annotation = match spliced {
        Some(annotation) => annotation,
        None => annotated_loop_function(
            &bound_function_block,
            parsed_function,
            &initial_state,
            arguments,
            SpecDefinitions::new(predicate_environment, click_function_environment),
            resource_environment,
            frame_entry,
            Some(pointer_element_types),
            loop_index,
        )?,
    };
    #[cfg(debug_assertions)]
    if crate::surface::lowering::loop_annotation_check_enabled() {
        crate::instrumentation::uncharged_debug_check(|| {
            let whole = annotated_function_with_assumptions(
                &bound_function_block,
                parsed_function,
                &initial_state,
                arguments,
                SpecDefinitions::new(predicate_environment, click_function_environment),
                resource_environment,
                frame_entry,
                Some(pointer_element_types),
            )
            .unwrap_or_else(|error| {
                panic!(
                    "the whole-function walk refuses loop({loop_index}): {}",
                    error.message()
                )
            });
            assert!(
                &whole == annotation.function(),
                "loop({loop_index})'s annotation differs from the whole-function walk's"
            );
        });
    }
    let annotated = annotation.function().clone();
    let known_current_loop = annotation.current_loop().cloned();
    execution.presentation.loop_annotation = Some(Arc::new(LoopAnnotationCache {
        function_block: std::ptr::from_ref(function_block) as usize,
        parsed_function: std::ptr::from_ref(parsed_function) as usize,
        start_facts: proof_context.constants.execution_start_facts.clone(),
        function_entry_state: proof_context.constants.function_entry_state.clone(),
        initial_state: initial_state.clone(),
        arguments: arguments.to_vec(),
        frontier_clauses: execution.presentation.frontier_loop_clauses.clone(),
        bound_function_block: bound_function_block.clone(),
        bound_nested_clauses: current_loop_clauses.len() > 1,
        bound_clause: scoped_template.bound_to_loop(loop_index),
        annotation,
    }));
    if execution.core.frontier.is_at_function_entry() {
        let entry_state = program_function_entry_state(&initial_state, &annotated, arguments)
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
    #[cfg(debug_assertions)]
    if crate::surface::lowering::loop_annotation_check_enabled()
        && let Some(known) = &known_current_loop
    {
        crate::instrumentation::uncharged_debug_check(|| {
            assert!(
                kernel_loop_by_index(annotated.body(), loop_index, &mut 0) == Some(known),
                "loop({loop_index})'s lowered loop differs from the one its body holds"
            );
        });
    }
    let current_loop = known_current_loop
        .or_else(|| {
            kernel_loop_by_index(annotated.body(), loop_index, &mut found_loop_index).cloned()
        })
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `loop` could not lower loop({loop_index}) at region({statement_index})"
            ))
        })?;

    let loop_certificates = std::cell::RefCell::new(LoopProofCertificates::default());
    let loop_source = FrontierLoopProofSource::new(
        loop_template,
        proof_context.constants.proof_site.clone(),
        claim_label,
        tactic_index,
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
        spec_definitions: SpecDefinitions::new(predicate_environment, click_function_environment),
        resource_environment,
        theorem_environment,
        function: &annotated,
        arguments,
        surface_propositions: &execution.presentation.surface_propositions,
        source_layout: &source_layout,
        function_source_registry: proof_context.function_source_registry(),
        frontier_loop_certificates: &loop_certificates,
        frontier_loop_source: &loop_source,
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
    // The loop's executions start from copies of the path's facts. Built
    // on the path's own list first, its context is built once here and
    // carried by every copy, rather than once by each.
    available_pure_facts.context();
    let exit_contexts = verify_execution_proofs_forward(
        expansion_capture,
        &current_loop,
        vec![PlanningExecutionContext {
            state: state.clone(),
            pure_facts: available_pure_facts.clone(),
            surface_propositions: execution.presentation.surface_propositions.clone(),
            recorded_states: execution.presentation.recorded_states.clone(),
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
        ProgramStatement::While { condition, .. } => Some(ClickProposition::Not(Box::new(
            surface_program_condition(condition, &execution.core.state)?,
        ))),
        _ => None,
    };
    let certificates = loop_certificates.borrow().clone();
    execution.presentation.loop_return_proofs.insert(
        loop_index,
        PlannedLoopReturns {
            paths: Arc::new(certificates.returns.clone()),
            entry_facts: entry_facts.clone(),
        },
    );
    let mut expanded_loop = loop_template.bound_to_loop(loop_index);
    expanded_loop.initialize_proof = Some(SourceProof::Script(
        certificates
            .initialize
            .as_ref()
            .map(|certificate| certificate.to_proof_tactics().to_vec())
            .unwrap_or_else(|| vec![ProofTactic::Known]),
    ));
    expanded_loop.preserve_proof = Some(SourceProof::Script(
        certificates
            .preserve
            .as_ref()
            .map(|certificate| certificate.to_proof_tactics().to_vec())
            .unwrap_or_else(|| vec![ProofTactic::Known]),
    ));
    // The claim's environment with every frontier rule before this one,
    // extended from the one the previous loop on this path built.
    let earlier_rules = Arc::new(LoopRuleEnvironment::extending(
        execution.presentation.loop_rule_environment.as_deref(),
        function_environment,
        &execution.core.frontier_loop_rules,
    ));
    let local_function_environment = earlier_rules
        .environment
        .clone()
        .with_verified_loop_rules(std::iter::once(loop_rule.clone()));
    execution.presentation.loop_rule_environment = Some(earlier_rules);

    if let FrontierPosition::StatementEntry { remaining } = &execution.core.frontier.position {
        // The current loop, annotated, in place of the source operation the
        // frontier is at; the statements after it keep their tree, so this
        // rebuilds only the path to that operation rather than every
        // statement after the loop.
        execution.core.frontier.position = FrontierPosition::StatementEntry {
            remaining: with_next_source_operation_replaced(remaining, current_loop).into(),
        };
    }

    let loop_context = proof_context.with_loop_binding(
        &bound_function_block,
        &annotated,
        &local_function_environment,
    );
    execute_step_from_frontier_position(
        execution,
        &loop_context,
        available_pure_facts,
        "loop",
        StatementPrerequisitePolicy::Exact,
        LoopStepPolicy::ApplyVerifiedRule,
    )?;
    execution.record_terminal_loop_return_proofs(&certificates.returns)?;
    // A loop that leaves on one path names that pass's points after it: its
    // calls, its test and its body's statements, as the pass recorded them.
    // Several leaving paths would give one name several states, so then none
    // is recorded.
    match certificates.exit_points.get(&loop_index).map(Vec::as_slice) {
        Some([points]) => execution
            .presentation
            .recorded_states
            .record_region_points(points),
        Some(paths) if paths.len() > 1 => execution
            .presentation
            .recorded_states
            .record_ambiguous_exit_points(loop_index, paths),
        _ => {}
    }
    // The rule was verified on its own copy of this proof's state, counting
    // identities from this proof's mark, and applying it leaves the ones it
    // invented in the state here: the head's havoc of every local the body
    // writes is what those locals hold after the loop. The counter has to
    // move past them, or the next thing this proof invents (a join's fresh
    // local, a heap block) is given one of them and two values become one.
    let rule_mark = exit_contexts
        .iter()
        .map(|context| context.next_kernel_variable)
        .max()
        .unwrap_or(0);
    if rule_mark > execution.core.kernel_variable_mark() {
        execution
            .core
            .advance_kernel_variable_mark(rule_mark)
            .map_err(|message| {
                ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
            })?;
    }
    let state: &mut ExecutionState = &mut execution.core.state;
    if let Some(exit_condition) = loop_exit_condition.filter(|_| {
        execution
            .presentation
            .recorded_states
            .get(&ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Loop(loop_index),
                kind: ProgramPointKind::Exit,
            }))
            .is_some()
    }) {
        let exit_point = ProgramPointRef {
            region: CodeRegionRef::Loop(loop_index),
            kind: ProgramPointKind::Exit,
        };
        let exit_surface = surface_at_program_point(&exit_condition, &exit_point)?;
        let lowered_exit_condition = lower_fixed_state_proposition(
            &exit_surface,
            available_pure_facts,
            ParameterBinding::new(parsed_function.parameters(), arguments),
            FixedStateFrame::new(&initial_state, state, None, &execution.presentation.recorded_states),
            SpecDefinitions::new(predicate_environment, click_function_environment),
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

/// A loop label names one loop on an execution path. `at(label.exit, ...)`
/// and `label` regions resolve through the clause that declared it, so a
/// second `loop as label` at another loop would make the same name mean two
/// program points.
fn refuse_rebound_loop_labels(
    function_block: &FunctionBlock,
    claim_label: &str,
    tactic_index: usize,
) -> Result<(), ClickError> {
    // The clause list keeps the labels naming two regions: with none, the
    // walk below finds nothing.
    if !function_block.structural_clauses().has_rebound_label() {
        return Ok(());
    }
    let mut bound = BTreeMap::<&str, &CodeRegion>::new();
    for clause in function_block.structural_clauses() {
        let Some(label) = clause.label() else {
            continue;
        };
        if let Some(previous) = bound.insert(label, clause.region())
            && previous != clause.region()
        {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: loop label `{label}` already names {} on this execution path; give each loop its own label",
                match previous {
                    CodeRegion::Function => "function".to_string(),
                    CodeRegion::Loop(index) => format!("loop({index})"),
                    CodeRegion::Statement(index) => format!("region({index})"),
                }
            )));
        }
    }
    Ok(())
}
