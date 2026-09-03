use super::*;
use crate::kernel::abstract_c_state_for_interface_join_across;
use std::sync::Arc;

///
/// The legacy cursor wrapper above materializes its vector at the boundary.
/// Proof-owned structural joins call this operation directly, so checking an
/// interface does not clone or re-index unrelated ambient facts.
#[allow(clippy::too_many_arguments)]
pub(super) fn apply_branch_interface_with_proof_facts(
    target: &ProgramPointRef,
    assertions: &[ProofAssertion],
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut ProofFacts,
    stable_join_locals: &BTreeMap<String, CValue>,
    sibling_join_states: Option<&[&CState]>,
    needs_abstraction: bool,
) -> Result<(), ClickError> {
    let tactic_index = proof_context.tactic_index;
    let parameters = proof_context.parsed_function.parameters();
    let arguments = proof_context.arguments;
    let predicate_environment = proof_context.predicate_environment;
    let click_function_environment = proof_context.click_function_environment;
    let resource_environment = proof_context.resource_environment;
    let claim_label = proof_context.claim_label;

    let state: &mut CState = &mut execution.core.state;

    let mut concrete_facts = available_pure_facts.clone();
    let mut established_interface_resources = Vec::new();
    for assertion in assertions {
        match assertion {
            ProofAssertion::Fact(surface_fact) => {
                let fact = lower_fixed_state_proposition_with_assumptions(
                        surface_fact,
                        concrete_facts.assumptions(),
                        parameters,
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
                            "`{claim_label}` tactic {tactic_index}: could not lower `branch ensuring` fact: {message}"
                        ))
                })?;
                execution
                    .presentation
                    .surface_propositions
                    .record_lowering(surface_fact, &fact)?;
                if !concrete_facts.contains_top_level(&fact)
                    && !concrete_facts.assumptions().proves(&fact)
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `branch ensuring` did not establish fact: {}",
                        describe_missing_pure_fact(
                            &fact,
                            &concrete_facts.to_vec(),
                            state.resources().facts(),
                            parameters,
                            arguments,
                            &[]
                        )
                    )));
                }
                if !concrete_facts.contains_top_level(&fact) {
                    concrete_facts = concrete_facts.with_kernel_checked_fact(fact);
                }
            }
            ProofAssertion::Resource(resource) => {
                let expected =
                    lower_resource_clause_at_state(resource, parameters, arguments, state)?;
                let is_observed_core = resource_is_direct_observed_core(
                    resource,
                    &established_interface_resources,
                    resource_environment,
                    claim_label,
                    tactic_index,
                )?;
                if !is_observed_core
                    && !state
                        .resources()
                        .satisfies_fact(&expected, concrete_facts.assumptions())
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `branch ensuring` did not establish resource fact: {}",
                        describe_missing_resource_fact(
                            &expected,
                            &concrete_facts.to_vec(),
                            state.resources().facts(),
                            parameters,
                            arguments,
                            &[]
                        )
                    )));
                }
                established_interface_resources.push(resource.clone());
            }
        }
    }
    if !needs_abstraction {
        *available_pure_facts = concrete_facts;
        return Ok(());
    }
    let entry_state = execution.core.frontier.execution_start_state(state).clone();
    let abstraction = match sibling_join_states {
        Some(states) => {
            abstract_c_state_for_interface_join_across(state, states, stable_join_locals)
        }
        None => abstract_c_state_for_join(state, stable_join_locals),
    };
    let mut abstract_state = abstraction.map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not abstract `branch` target state: {message}"
        ))
    })?;

    // Branch abstraction discards incidental source-boundary snapshots, but
    // an explicit proof mark is a deliberate historical dependency. Preserve
    // marks that were common to every continuing arm.
    execution
        .presentation
        .recorded_snapshots
        .retain(|selector, _| matches!(selector, SnapshotSelector::Mark(_)));
    execution
        .presentation
        .recorded_snapshots
        .insert(target.clone(), abstract_state.clone());
    execution.presentation.case_assumptions.clear();
    execution.core.execution_abstraction = true;

    let mut exported_resources = ResourceContext::new();
    // This vector contains only facts explicitly exported by the interface
    // (and their local definitional projections), so materializing it is
    // output-sized rather than proportional to the ambient proof context.
    let mut exported_pure_facts = Vec::new();
    for assertion in assertions {
        if let ProofAssertion::Resource(resource) = assertion {
            let fact =
                lower_resource_clause_at_state(resource, parameters, arguments, &abstract_state)?;
            exported_resources = exported_resources.unchecked_with_fact(fact);
            append_lowered_resource_clause_loadable_fact(
                resource,
                parameters,
                exported_resources
                    .facts()
                    .last()
                    .expect("exported resource was just appended"),
                &abstract_state,
                &mut exported_pure_facts,
            );
            // An `old(...)`-interface ensure needs the exported view's
            // loadability in its entry-memory form. Export it exactly
            // when the clause lowers at entry at all and the pre-advance
            // proof state establishes it, the same gate `fact` assertions
            // pass through.
            let mut entry_loadables = Vec::new();
            if let Ok(entry_lowered) =
                lower_resource_clause_at_state(resource, parameters, arguments, &entry_state)
            {
                append_lowered_resource_clause_loadable_fact(
                    resource,
                    parameters,
                    &entry_lowered,
                    &entry_state,
                    &mut entry_loadables,
                );
            }
            if !entry_loadables.is_empty() {
                let mut pre_advance_facts = concrete_facts.clone();
                for fact in &execution.core.effect_facts {
                    if !pre_advance_facts.contains_top_level(fact.proposition()) {
                        pre_advance_facts =
                            pre_advance_facts.with_kernel_checked_fact(fact.proposition().clone());
                    }
                }
                for fact in entry_loadables {
                    if pre_advance_facts.assumptions().proves(&fact)
                        && !exported_pure_facts.contains(&fact)
                    {
                        exported_pure_facts.push(fact);
                    }
                }
            }
        }
    }
    abstract_state = abstract_state.with_resource_context(exported_resources.clone());
    execution
        .presentation
        .recorded_snapshots
        .insert(target.clone(), abstract_state.clone());

    for assertion in assertions {
        if let ProofAssertion::Fact(surface_fact) = assertion {
            let fact = lower_fixed_state_proposition(
                    surface_fact,
                    &exported_pure_facts,
                    parameters,
                    arguments,
                    &entry_state,
                    &abstract_state,
                    None,
                    &execution.presentation.recorded_snapshots,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not abstract `branch ensuring` fact: {message}"
                    ))
                })?;
            execution
                .presentation
                .surface_propositions
                .record_lowering(surface_fact, &fact)?;
            if !exported_pure_facts.contains(&fact) {
                exported_pure_facts.push(fact);
            }
        }
    }

    let exported_assumptions = assumptions_from_propositions(&exported_pure_facts);
    exported_resources = ResourceContext::new()
            .try_compose_with_facts(exported_resources.facts().iter().cloned(), &exported_assumptions)
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: invalid `branch ensuring` resource interface: {error:?}"
                ))
            })?;
    abstract_state = abstract_state.with_resource_context(exported_resources);
    execution
        .presentation
        .recorded_snapshots
        .insert(target.clone(), abstract_state.clone());
    *state = abstract_state;
    *available_pure_facts = ProofFacts::from_ordered(&exported_pure_facts);
    Ok(())
}

pub(super) fn append_execution_effect_facts(
    target: &mut Vec<ExecutionPureFact>,
    source: &[ExecutionPureFact],
) {
    for fact in source {
        // Verified-call rule results are kernel-certified transition facts,
        // just like memory-effect summaries. Keep them available to later
        // explicit check without making the surface certificate restate
        // opaque call identities or intermediate-memory equalities.
        if (is_memory_effect_proposition(fact.proposition()) || fact.is_certified())
            && !target.contains(fact)
        {
            target.push(fact.clone());
        }
    }
}

pub(super) fn fact_transport_transition_facts(
    facts: &[ExecutionPureFact],
    source: &Proposition,
) -> Vec<ExecutionPureFact> {
    let source_memories = c_condition_fact_memories(source);
    let matching_effect = facts.iter().position(|fact| {
        let before = match fact.proposition() {
            Proposition::CMemoryMutatesOnly { before, .. }
            | Proposition::CMemoryEffectSummary { before, .. }
            | Proposition::CHeapAllocationFreed { before, .. } => before,
            _ => return false,
        };
        source_memories.contains(before)
    });
    let Some(start) = matching_effect else {
        return facts.to_vec();
    };
    let end = facts[start + 1..]
        .iter()
        .position(|fact| is_memory_effect_proposition(fact.proposition()))
        .map(|offset| start + 1 + offset)
        .unwrap_or(facts.len());
    facts[start..end].to_vec()
}

fn is_memory_effect_proposition(proposition: &Proposition) -> bool {
    matches!(
        proposition,
        Proposition::CMemoryMutatesOnly { .. }
            | Proposition::CMemoryEffectSummary { .. }
            | Proposition::CHeapAllocationFreed { .. }
    )
}

fn resource_is_direct_observed_core(
    required: &ResourceClause,
    established: &[ResourceClause],
    resource_environment: &ResourceEnvironment,
    claim_label: &str,
    tactic_index: usize,
) -> Result<bool, ClickError> {
    for parent in established {
        let ResourceClause::Declared {
            kind: ResourceKind::Composite,
            name,
            ..
        } = parent
        else {
            continue;
        };
        let Some(definition) = resource_environment.get(name) else {
            continue;
        };
        let Some(body) = definition.composite_body() else {
            continue;
        };
        let substitutions =
            resource_argument_substitutions(definition, parent, claim_label, tactic_index)?;
        for child in body.contains() {
            let child = instantiate_resource_clause(child, &substitutions).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not instantiate observed child of `{name}`: {message}"
                ))
            })?;
            let core = match child {
                ResourceClause::Quantified { .. } => continue,
                ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => {
                    ResourceClause::ViewMemory(segment)
                }
                ResourceClause::Declared {
                    kind,
                    name,
                    arguments,
                    parameter_types,
                    ..
                } => ResourceClause::Declared {
                    access: ResourceAccessMode::View,
                    kind,
                    name,
                    arguments,
                    parameter_types,
                },
            };
            if &core == required {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn execute_branch_step_from_frontier_position(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut Vec<Proposition>,
    tactic_name: &str,
    requested_branch: Option<bool>,
    prerequisite_policy: StatementPrerequisitePolicy,
    branch_step_policy: BranchStepPolicy,
    complete_empty_branch: bool,
    mut construction: Option<Construction<'_>>,
    context: Option<&PureFactContext>,
) -> Result<bool, ClickError> {
    let function_block = proof_context.function_block;
    let function = proof_context.function;
    let parameters = proof_context.parsed_function.parameters();
    let arguments = proof_context.arguments;
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;

    let state: &mut CState = &mut execution.core.state;

    let statement_index = execution.core.frontier.next_statement_index;
    let source_region = proof_context.constants.source_layout.statement(statement_index).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve source statement({statement_index})"
        ))
    })?;
    let (execution_start_state, mut current_state, statement, remaining) =
        next_top_level_statement_from_frontier_position(
            ExecutionView::new(
                &execution.core.frontier,
                &execution.core.effect_facts,
                &execution.presentation.recorded_snapshots,
                &execution.presentation.surface_propositions,
                proof_context.constants.function_entry_state.as_ref(),
            ),
            state,
            function,
            arguments,
            claim_label,
            tactic_index,
            tactic_name,
        )?;
    let CStatement::If {
        condition,
        then_branch,
        else_branch,
    } = statement
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires the next C statement to be an `if`"
        )));
    };
    let SourceStatementKind::If {
        then_statement_index,
        else_statement_index,
    } = source_region.kind
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` found a C `if` outside its source region"
        )));
    };

    let construction_snapshot_overrides = construction.is_some().then(|| {
        construction_snapshot_overrides(
            &execution.presentation.recorded_snapshots,
            function_block,
            &[CodeRegion::Statement(statement_index)],
            ProgramPointKind::Entry,
        )
    });
    record_statement_program_snapshot_state(
        &mut execution.presentation.recorded_snapshots,
        function_block,
        statement_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    let construction_snapshot_overrides = construction_snapshot_overrides.unwrap_or_default();
    let current_resources = current_state.resources().facts().to_vec();
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    let condition_transitions = certified_condition_transitions(
        &current_state,
        available_pure_facts,
        &condition,
        &transition_label,
        prerequisite_policy,
        true,
        context,
    )?;
    let condition_was_proven = condition_transitions.len() == 1;
    if matches!(branch_step_policy, BranchStepPolicy::RequireProven)
        && condition_transitions.len() != 1
    {
        let expected = requested_branch.map_or("one exact truth value", |take_then| {
            if take_then { "true" } else { "false" }
        });
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not prove that the next C `if` condition `{}` is {expected}; got {} feasible condition paths\n  condition path facts: {:?}\n{}",
            describe_c_expression(&condition),
            condition_transitions.len(),
            condition_transitions
                .iter()
                .map(|transition| &transition.path_facts)
                .collect::<Vec<_>>(),
            describe_proof_context(
                available_pure_facts,
                &current_resources,
                parameters,
                arguments,
                &[]
            )
        )));
    }
    let condition_transition = match branch_step_policy {
        BranchStepPolicy::RequireProven => condition_transitions
            .into_iter()
            .next()
            .expect("one condition transition was required"),
        BranchStepPolicy::Explore => {
            let requested_branch = requested_branch.expect("branch exploration selects an arm");
            let Some(transition) = condition_transitions
                .into_iter()
                .find(|transition| transition.is_true == requested_branch)
            else {
                return Ok(false);
            };
            transition
        }
    };
    let selected_then = condition_transition.is_true;
    if requested_branch.is_some_and(|take_then| selected_then != take_then) {
        let actual = if selected_then { "then" } else { "else" };
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requested the {} branch, but current pure facts prove the {actual} branch",
            if requested_branch == Some(true) {
                "then"
            } else {
                "else"
            }
        )));
    }

    if matches!(branch_step_policy, BranchStepPolicy::Explore)
        && !condition_was_proven
        && matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning)
    {
        let occurrence = execution.core.next_path_choice;
        execution.core.next_path_choice += 1;
        let statement_condition = surface_at_snapshot(
            &surface_c_condition(&condition),
            &ProgramPointRef {
                region: CodeRegionRef::Statement(statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        // Prefer a form in terms of the shared function-entry snapshot.
        // It remains available after independently explored paths are merged,
        // whereas a later statement-entry state can legitimately differ
        // across those paths and is therefore not retained in the common
        // check interface. Sorting networks are the representative case:
        // the second comparison's current operand is an entry value selected
        // by the first comparison.
        let condition = proof_context
            .constants
            .function_entry_state
            .as_ref()
            .and_then(|entry_state| {
                condition_transition.path_facts.iter().find_map(|fact| {
                    let Proposition::ConditionIs(_, _) = fact else {
                        return None;
                    };
                    let surface =
                        synthesize_surface_proposition(fact, parameters, arguments, entry_state)?;
                    let surface = surface_at_snapshot(
                        &surface,
                        &ProgramPointRef {
                            region: CodeRegionRef::Function,
                            kind: ProgramPointKind::Entry,
                        },
                    )
                    .ok()?;
                    Some(if condition_transition.is_true {
                        surface
                    } else {
                        negate_click_proposition(&surface)
                    })
                })
            })
            .unwrap_or(statement_condition);
        if let Some(construction) = construction.as_mut() {
            let environments = construction.environments;
            let restore = apply_construction_snapshot_view(
                &mut execution.presentation.recorded_snapshots,
                &construction_snapshot_overrides,
            );
            construct_proof_step_for_planned_operation(
                execution,
                proof_context,
                construction.sink,
                &current_state,
                function_block,
                parameters,
                arguments,
                environments,
                &ConstructionEvidence::CertifiedPathAssumption {
                    occurrence,
                    condition,
                    value: condition_transition.is_true,
                    facts: condition_transition.path_facts.clone(),
                    theorem: condition_transition.theorem.clone(),
                },
            );
            restore_construction_snapshot_view(
                &mut execution.presentation.recorded_snapshots,
                restore,
            );
            let certificate_facts = &mut execution.presentation.surface_record.certificate_facts;
            for fact in &condition_transition.path_facts {
                certificate_facts.insert(fact.clone());
            }
        }
    }
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        let restore = apply_construction_snapshot_view(
            &mut execution.presentation.recorded_snapshots,
            &construction_snapshot_overrides,
        );
        append_condition_transition_certificate(
            execution,
            proof_context,
            &condition_transition,
            &current_state,
            available_pure_facts,
            function_block,
            parameters,
            arguments,
            construction.as_mut().map(Construction::reborrow),
        );
        restore_construction_snapshot_view(&mut execution.presentation.recorded_snapshots, restore);
    }
    execution
        .core
        .record_condition_transition(
            function,
            arguments,
            condition_transition.theorem.clone(),
            condition_transition.context.clone(),
            &condition_transition.path_facts,
            &[],
        )
        .map_err(|refusal| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` recorded condition evidence the proof object rejected: {}",
                describe_evidence_refusal(&refusal, parameters, arguments)
            ))
        })?;
    let state: &mut CState = &mut execution.core.state;
    *available_pure_facts = condition_transition.pure_facts;
    current_state = crate::kernel::resolve_pending_heap_allocations(
        &current_state,
        &assumptions_from_propositions(available_pure_facts),
    );
    let selected_branch = if selected_then {
        *then_branch
    } else {
        *else_branch
    };
    execution.core.frontier.next_statement_index = if selected_then {
        then_statement_index
    } else {
        else_statement_index
    };
    execution.core.frontier.execution_start_state = Some(execution_start_state);
    *state = current_state;
    // The selected arm is spliced before the `if`'s tail so the frontier's
    // own statement tree keeps every downstream statement reachable; the
    // patched source layout carries arm-final control successors, so no
    // continuation record is needed.
    if complete_empty_branch && matches!(selected_branch, CStatement::Skip) {
        // The empty arm completes this branch region immediately; the patched
        // layout supplies its control successor and statically completed
        // branch regions.
        let skip_index = execution.core.frontier.next_statement_index;
        for exited in proof_context
            .constants
            .source_layout
            .exited_branch_regions(skip_index)
            .to_vec()
        {
            record_statement_program_snapshot_state(
                &mut execution.presentation.recorded_snapshots,
                function_block,
                exited,
                ProgramPointKind::Exit,
                state.clone(),
            );
        }
        let successor = proof_context
            .constants
            .source_layout
            .statement(skip_index)
            .map(|region| region.continuation_node);
        match remaining {
            Some(tail) => {
                if let Some(successor) = successor {
                    execution.core.frontier.next_statement_index = successor;
                }
                execution.core.frontier.position = FrontierPosition::StatementEntry {
                    remaining: tail.into(),
                };
            }
            None => match resume_after_completed_region(&mut execution.core.frontier) {
                Some(tail) => {
                    execution.core.frontier.position = FrontierPosition::StatementEntry {
                        remaining: tail.into(),
                    };
                }
                None if finish_exhausted_region(&mut execution.core.frontier) => {}
                None => {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached the end of the function without a return"
                    )));
                }
            },
        }
    } else {
        let spliced = match remaining {
            Some(tail) => c_seq(selected_branch, tail),
            None => selected_branch,
        };
        execution.core.frontier.position = FrontierPosition::StatementEntry {
            remaining: spliced.into(),
        };
    }
    record_current_statement_entry(
        &execution.core.frontier,
        &mut execution.presentation.recorded_snapshots,
        state,
        function_block,
        function,
        arguments,
        claim_label,
        tactic_index,
        tactic_name,
    )?;
    Ok(true)
}

#[allow(clippy::too_many_arguments)]
fn execute_concrete_loop_head_step(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut Vec<Proposition>,
    tactic_name: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    statement_index: usize,
    loop_index: usize,
    continuation_node: usize,
    execution_start_state: CState,
    current_state: CState,
    loop_statement: CStatement,
    remaining: Option<CStatement>,
    mut construction: Option<Construction<'_>>,
) -> Result<(), ClickError> {
    let function_block = proof_context.function_block;
    let function = proof_context.function;
    let parameters = proof_context.parsed_function.parameters();
    let arguments = proof_context.arguments;
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;

    execution.core.concrete_loop_execution = true;
    let CStatement::While {
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        do_while,
        body,
    } = loop_statement.clone()
    else {
        unreachable!("concrete loop stepping requires a while statement");
    };

    let construction_snapshot_overrides = construction.is_some().then(|| {
        construction_snapshot_overrides(
            &execution.presentation.recorded_snapshots,
            function_block,
            &[
                CodeRegion::Statement(statement_index),
                CodeRegion::Loop(loop_index),
            ],
            ProgramPointKind::Entry,
        )
    });
    record_statement_program_snapshot_state(
        &mut execution.presentation.recorded_snapshots,
        function_block,
        statement_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    record_loop_program_snapshot_state(
        &mut execution.presentation.recorded_snapshots,
        function_block,
        loop_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    let construction_snapshot_overrides = construction_snapshot_overrides.unwrap_or_default();

    let loop_head = CStatement::While {
        condition: condition.clone(),
        invariant: invariant.clone(),
        invariant_checks: invariant_checks.clone(),
        effect_checks: effect_checks.clone(),
        do_while: false,
        body: body.clone(),
    };

    let state: &mut CState = &mut execution.core.state;
    execution.core.frontier.execution_start_state = Some(execution_start_state);
    *state = current_state.clone();

    // C's `do ... while` enters its body before evaluating the condition. The
    // continuation is an ordinary while head: after the first body, every
    // iteration checks the condition before re-entering the body.
    if do_while {
        if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning)
            && let Some(construction) = construction.as_mut()
        {
            let environments = construction.environments;
            construct_proof_step_for_planned_operation(
                execution,
                proof_context,
                construction.sink,
                &current_state,
                function_block,
                parameters,
                arguments,
                environments,
                &ConstructionEvidence::CertifiedStatementStep {
                    planned_transition: None,
                },
            );
        }
        let loop_head = match remaining {
            Some(remaining) => c_seq(loop_head, remaining),
            None => loop_head,
        };
        execution
            .core
            .frontier
            .continuations
            .push(ProofExecutionContinuation {
                remaining: Some(loop_head.into()),
                next_statement_index: statement_index,
                loop_exit_statement_index: continuation_node,
            });
        execution.core.frontier.next_statement_index = proof_context.constants.source_layout
            .loop_body_entry(loop_index)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve the source body of loop({loop_index})"
                ))
            })?;
        execution.core.frontier.position = FrontierPosition::StatementEntry {
            remaining: body.into(),
        };
        record_statement_program_snapshot_state(
            &mut execution.presentation.recorded_snapshots,
            function_block,
            execution.core.frontier.next_statement_index,
            ProgramPointKind::Entry,
            current_state,
        );
        return Ok(());
    }

    let current_resources = current_state.resources().facts().to_vec();
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    let condition_transitions = certified_condition_transitions(
        &current_state,
        available_pure_facts,
        &condition,
        &transition_label,
        prerequisite_policy,
        true,
        None,
    )?;
    if condition_transitions.len() != 1 {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not prove one exact truth value for loop({loop_index}) condition `{}`; got {} feasible condition paths\n{}",
            describe_c_expression(&condition),
            condition_transitions.len(),
            describe_proof_context(
                available_pure_facts,
                &current_resources,
                parameters,
                arguments,
                &[]
            )
        )));
    }
    let condition_transition = condition_transitions
        .into_iter()
        .next()
        .expect("one condition transition was required");
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        let restore = apply_construction_snapshot_view(
            &mut execution.presentation.recorded_snapshots,
            &construction_snapshot_overrides,
        );
        append_condition_transition_certificate(
            execution,
            proof_context,
            &condition_transition,
            &current_state,
            available_pure_facts,
            function_block,
            parameters,
            arguments,
            construction.as_mut().map(Construction::reborrow),
        );
        restore_construction_snapshot_view(&mut execution.presentation.recorded_snapshots, restore);
    }
    execution
        .core
        .record_condition_transition(
            function,
            arguments,
            condition_transition.theorem.clone(),
            condition_transition.context.clone(),
            &condition_transition.path_facts,
            &[],
        )
        .map_err(|refusal| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` recorded condition evidence the proof object rejected: {}",
                describe_evidence_refusal(&refusal, parameters, arguments)
            ))
        })?;
    *available_pure_facts = condition_transition.pure_facts;

    if condition_transition.is_true {
        let loop_head = match remaining {
            Some(remaining) => c_seq(loop_head, remaining),
            None => loop_head,
        };
        execution
            .core
            .frontier
            .continuations
            .push(ProofExecutionContinuation {
                remaining: Some(loop_head.into()),
                next_statement_index: statement_index,
                loop_exit_statement_index: continuation_node,
            });
        execution.core.frontier.next_statement_index = proof_context.constants.source_layout
            .loop_body_entry(loop_index)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve the source body of loop({loop_index})"
                ))
            })?;
        execution.core.frontier.position = FrontierPosition::StatementEntry {
            remaining: (*body).into(),
        };
        record_statement_program_snapshot_state(
            &mut execution.presentation.recorded_snapshots,
            function_block,
            execution.core.frontier.next_statement_index,
            ProgramPointKind::Entry,
            current_state,
        );
        return Ok(());
    }

    record_statement_program_snapshot_state(
        &mut execution.presentation.recorded_snapshots,
        function_block,
        statement_index,
        ProgramPointKind::Exit,
        current_state.clone(),
    );
    record_loop_program_snapshot_state(
        &mut execution.presentation.recorded_snapshots,
        function_block,
        loop_index,
        ProgramPointKind::Exit,
        current_state.clone(),
    );
    // A loop at the end of a branch arm completes the recorded chain of
    // enclosing branch regions when it exits.
    for exited in proof_context
        .constants
        .source_layout
        .exited_branch_regions(statement_index)
        .to_vec()
    {
        record_statement_program_snapshot_state(
            &mut execution.presentation.recorded_snapshots,
            function_block,
            exited,
            ProgramPointKind::Exit,
            current_state.clone(),
        );
    }
    let next = if let Some(remaining) = remaining {
        execution.core.frontier.next_statement_index = continuation_node;
        Some(remaining)
    } else {
        resume_after_completed_region(&mut execution.core.frontier)
    };
    let Some(remaining) = next else {
        if finish_exhausted_region(&mut execution.core.frontier) {
            return Ok(());
        }
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached the end of the function without a return"
        )));
    };
    execution.core.frontier.position = FrontierPosition::StatementEntry {
        remaining: remaining.into(),
    };
    record_statement_program_snapshot_state(
        &mut execution.presentation.recorded_snapshots,
        function_block,
        execution.core.frontier.next_statement_index,
        ProgramPointKind::Entry,
        current_state,
    );
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn next_top_level_statement_from_frontier_position(
    view: ExecutionView<'_>,
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
) -> Result<NextTopLevelStatement, ClickError> {
    match &view.frontier.position {
        FrontierPosition::FunctionEntry => {
            let execution_start_state = state.clone();
            let current_state = c_function_entry_state(&execution_start_state, function, arguments)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not bind function arguments"
                    ))
                })?;
            let (statement, remaining) =
                split_next_source_operation(function.body()).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` failed: {message}"
                    ))
                })?;
            Ok((execution_start_state, current_state, statement, remaining))
        }
        FrontierPosition::StatementEntry { remaining } => {
            let execution_start_state = view
                .frontier
                .execution_start_state
                .clone()
                .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` has no execution start state"
                ))
            })?;
            let (statement, remaining) =
                split_next_source_operation(remaining).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` failed: {message}"
                    ))
                })?;
            Ok((execution_start_state, state.clone(), statement, remaining))
        }
        FrontierPosition::FunctionExit { .. } => Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` cannot run after execution already reached function exit"
        ))),
        FrontierPosition::RegionBoundary => Err(ClickError::new(match view.frontier.region {
            ExecutionRegionKind::BranchArm => format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` ran past the end of its branch body; an arm of `branch` must stop at the shared continuation"
            ),
            _ => format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` cannot run past the loop back-edge boundary"
            ),
        })),
    }
}

pub(super) fn record_loop_program_snapshot_state(
    recorded_snapshots: &mut RecordedSnapshots,
    function_block: &FunctionBlock,
    loop_index: usize,
    kind: ProgramPointKind,
    state: CState,
) {
    record_code_region_program_snapshot_state(
        recorded_snapshots,
        function_block,
        CodeRegion::Loop(loop_index),
        kind,
        state,
    );
}

/// Swaps the listed program points to their pre-recording values (or removes
/// points the recording introduced) so a surface step can be written against
/// the view its own check will have; returns what must be put back.
fn construction_snapshot_overrides(
    recorded_snapshots: &RecordedSnapshots,
    function_block: &FunctionBlock,
    regions: &[CodeRegion],
    kind: ProgramPointKind,
) -> Vec<(ProgramPointRef, Option<CState>)> {
    let mut points = BTreeSet::new();
    for region in regions {
        let point_region = match region {
            CodeRegion::Function => CodeRegionRef::Function,
            CodeRegion::Loop(index) => CodeRegionRef::Loop(*index),
            CodeRegion::Statement(index) => CodeRegionRef::Statement(*index),
        };
        points.insert(ProgramPointRef {
            region: point_region,
            kind,
        });
        for label in function_block
            .structural_clauses()
            .iter()
            .filter(|clause| clause.region() == region)
            .filter_map(StructuralClause::label)
        {
            points.insert(ProgramPointRef {
                region: CodeRegionRef::Label(label.to_string()),
                kind,
            });
        }
    }
    points
        .into_iter()
        .map(|point| {
            let prior = recorded_snapshots.get(&point).cloned();
            (point, prior)
        })
        .collect()
}

fn apply_construction_snapshot_view(
    recorded_snapshots: &mut RecordedSnapshots,
    overrides: &[(ProgramPointRef, Option<CState>)],
) -> Vec<(ProgramPointRef, Option<CState>)> {
    let mut restore = Vec::with_capacity(overrides.len());
    for (point, prior) in overrides {
        restore.push((point.clone(), recorded_snapshots.get(point).cloned()));
        match prior {
            Some(state) => {
                recorded_snapshots.insert(point.clone(), state.clone());
            }
            None => {
                recorded_snapshots.remove(point);
            }
        }
    }
    restore
}

fn restore_construction_snapshot_view(
    recorded_snapshots: &mut RecordedSnapshots,
    restore: Vec<(ProgramPointRef, Option<CState>)>,
) {
    for (point, value) in restore {
        match value {
            Some(state) => {
                recorded_snapshots.insert(point, state);
            }
            None => {
                recorded_snapshots.remove(&point);
            }
        }
    }
}

pub(super) fn record_statement_program_snapshot_state(
    recorded_snapshots: &mut RecordedSnapshots,
    function_block: &FunctionBlock,
    statement_index: usize,
    kind: ProgramPointKind,
    state: CState,
) {
    record_code_region_program_snapshot_state(
        recorded_snapshots,
        function_block,
        CodeRegion::Statement(statement_index),
        kind,
        state,
    );
}

pub(super) fn record_code_region_program_snapshot_state(
    recorded_snapshots: &mut RecordedSnapshots,
    function_block: &FunctionBlock,
    region: CodeRegion,
    kind: ProgramPointKind,
    state: CState,
) {
    let point_region = match region {
        CodeRegion::Function => CodeRegionRef::Function,
        CodeRegion::Loop(index) => CodeRegionRef::Loop(index),
        CodeRegion::Statement(index) => CodeRegionRef::Statement(index),
    };
    recorded_snapshots.insert(
        ProgramPointRef {
            region: point_region,
            kind,
        },
        state.clone(),
    );
    for label in function_block
        .structural_clauses()
        .iter()
        .filter(|clause| clause.region() == &region)
        .filter_map(StructuralClause::label)
    {
        recorded_snapshots.insert(
            ProgramPointRef {
                region: CodeRegionRef::Label(label.to_string()),
                kind,
            },
            state.clone(),
        );
    }
}

pub(super) const SNAPSHOT_ANNOTATION_DEPTH_LIMIT: usize = 32;

pub(super) fn surface_at_snapshot<K: RecordedSnapshotKey + ?Sized>(
    surface: &ClickProposition,
    key: &K,
) -> Result<ClickProposition, ClickError> {
    let selector = key.to_selector();
    annotate_surface_at_snapshot(surface, &selector, SnapshotAnnotation::Reread)
}

#[derive(Clone, Copy)]
enum SnapshotAnnotation {
    /// Re-read every operand in the selected snapshot, replacing an existing `at`
    /// selector: fact transport across a statement re-reads the source
    /// form at the statement's exit, having proved the cells unchanged.
    Reread,
}

fn annotate_surface_at_snapshot(
    surface: &ClickProposition,
    selector: &SnapshotSelector,
    annotation: SnapshotAnnotation,
) -> Result<ClickProposition, ClickError> {
    if matches!(
        surface,
        ClickProposition::Loadable { .. }
            | ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
    ) {
        return Ok(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(surface.clone()),
        });
    }
    let expression_at_snapshot = |expression: &ContractExpression| match (annotation, expression) {
        (_, ContractExpression::Old(_)) => expression.clone(),
        (SnapshotAnnotation::Reread, ContractExpression::At { expression, .. }) => {
            ContractExpression::At {
                selector: selector.clone(),
                expression: expression.clone(),
            }
        }
        (_, expression) => ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(expression.clone()),
        },
    };
    fn annotate(
        proposition: &ClickProposition,
        expression_at_snapshot: &impl Fn(&ContractExpression) -> ContractExpression,
        selector: &SnapshotSelector,
        depth: usize,
    ) -> Result<ClickProposition, ClickError> {
        if depth >= SNAPSHOT_ANNOTATION_DEPTH_LIMIT {
            return Err(ClickError::new(
                "Surface Click snapshot annotation exceeded its structural depth bound",
            ));
        }
        Ok(match proposition {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => ClickProposition::Comparison {
                left: expression_at_snapshot(left),
                operator: *operator,
                right: expression_at_snapshot(right),
            },
            ClickProposition::Defined { .. } => ClickProposition::At {
                selector: selector.clone(),
                proposition: Box::new(proposition.clone()),
            },
            ClickProposition::At { .. } => proposition.clone(),
            ClickProposition::And(left, right) => ClickProposition::And(
                Box::new(annotate(left, expression_at_snapshot, selector, depth + 1)?),
                Box::new(annotate(
                    right,
                    expression_at_snapshot,
                    selector,
                    depth + 1,
                )?),
            ),
            ClickProposition::Or(left, right) => ClickProposition::Or(
                Box::new(annotate(left, expression_at_snapshot, selector, depth + 1)?),
                Box::new(annotate(
                    right,
                    expression_at_snapshot,
                    selector,
                    depth + 1,
                )?),
            ),
            ClickProposition::Not(body) => ClickProposition::Not(Box::new(annotate(
                body,
                expression_at_snapshot,
                selector,
                depth + 1,
            )?)),
            ClickProposition::Implies(left, right) => ClickProposition::Implies(
                Box::new(annotate(left, expression_at_snapshot, selector, depth + 1)?),
                Box::new(annotate(
                    right,
                    expression_at_snapshot,
                    selector,
                    depth + 1,
                )?),
            ),
            ClickProposition::ForAll { c_type, name, body } => ClickProposition::ForAll {
                c_type: *c_type,
                name: name.clone(),
                body: Box::new(annotate(body, expression_at_snapshot, selector, depth + 1)?),
            },
            ClickProposition::Exists { c_type, name, body } => ClickProposition::Exists {
                c_type: *c_type,
                name: name.clone(),
                body: Box::new(annotate(body, expression_at_snapshot, selector, depth + 1)?),
            },
            ClickProposition::RangeAll {
                start,
                end,
                item,
                body,
            } => ClickProposition::RangeAll {
                start: expression_at_snapshot(start),
                end: expression_at_snapshot(end),
                item: item.clone(),
                body: Box::new(annotate(body, expression_at_snapshot, selector, depth + 1)?),
            },
            ClickProposition::RangeAny {
                start,
                end,
                item,
                body,
            } => ClickProposition::RangeAny {
                start: expression_at_snapshot(start),
                end: expression_at_snapshot(end),
                item: item.clone(),
                body: Box::new(annotate(body, expression_at_snapshot, selector, depth + 1)?),
            },
            ClickProposition::PredicateCall { name, arguments } => {
                ClickProposition::PredicateCall {
                    name: name.clone(),
                    arguments: arguments.iter().map(expression_at_snapshot).collect(),
                }
            }
            ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. } => proposition.clone(),
        })
    }
    annotate(surface, &expression_at_snapshot, selector, 0)
}

pub(super) fn predicate_call_snapshot_selector(
    surface: &ClickProposition,
) -> Option<SnapshotSelector> {
    let ClickProposition::PredicateCall { arguments, .. } = surface else {
        return None;
    };
    arguments.iter().find_map(|argument| {
        let ContractExpression::At { selector, .. } = argument else {
            return None;
        };
        Some(selector.clone())
    })
}

/// Returns a snapshot selector explicitly carried by a proposition produced
/// by [`surface_at_snapshot`]. Callers must still
/// re-lower any newly anchored form and check that it denotes the exact
/// retained kernel fact.
pub(super) fn surface_snapshot_selector(surface: &ClickProposition) -> Option<SnapshotSelector> {
    let expression_site = |expression: &ContractExpression| match expression {
        ContractExpression::At { selector, .. } => Some(selector.clone()),
        _ => None,
    };
    match surface {
        ClickProposition::Comparison { left, right, .. } => {
            expression_site(left).or_else(|| expression_site(right))
        }
        ClickProposition::At { selector, .. } => Some(selector.clone()),
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            surface_snapshot_selector(left).or_else(|| surface_snapshot_selector(right))
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => surface_snapshot_selector(body),
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => expression_site(start)
            .or_else(|| expression_site(end))
            .or_else(|| surface_snapshot_selector(body)),
        ClickProposition::PredicateCall { arguments, .. } => {
            arguments.iter().find_map(expression_site)
        }
        ClickProposition::Separate { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::Loadable { .. }
        | ClickProposition::Defined { .. } => None,
    }
}

#[cfg(test)]
thread_local! {
    static PLANNING_STATEMENT_TRANSITIONS: std::cell::RefCell<Vec<(String, usize, String)>> = const {
        std::cell::RefCell::new(Vec::new())
    };
}

#[cfg(test)]
pub(super) fn count_planning_statement_transitions<R>(operation: impl FnOnce() -> R) -> (R, usize) {
    let before = PLANNING_STATEMENT_TRANSITIONS.with(|transitions| transitions.borrow().len());
    let result = operation();
    let after = PLANNING_STATEMENT_TRANSITIONS.with(|transitions| transitions.borrow().len());
    (result, after - before)
}

#[cfg(test)]
pub(super) fn collect_planning_statement_transitions<R>(
    operation: impl FnOnce() -> R,
) -> (R, Vec<(String, usize, String)>) {
    let before = PLANNING_STATEMENT_TRANSITIONS.with(|transitions| transitions.borrow().len());
    let result = operation();
    let transitions =
        PLANNING_STATEMENT_TRANSITIONS.with(|transitions| transitions.borrow()[before..].to_vec());
    (result, transitions)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn execute_step_from_frontier_position(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut Vec<Proposition>,
    _assumptions: &PureFactContext,
    tactic_name: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    fact_transport_policy: StatementFactTransportPolicy,
    loop_step_policy: LoopStepPolicy,
    mut construction: Option<Construction<'_>>,
) -> Result<Vec<Proposition>, ClickError> {
    execute_step_from_frontier_position_selecting_path(
        execution,
        proof_context,
        available_pure_facts,
        _assumptions,
        tactic_name,
        prerequisite_policy,
        fact_transport_policy,
        loop_step_policy,
        construction.as_mut().map(Construction::reborrow),
        None,
        None,
    )
}

pub(super) struct ExecutionPointStepSuccessor {
    pub(super) execution: ExecutionProofState,
    pub(super) pure_facts: Vec<Proposition>,
    pub(super) introduced_facts: Vec<Proposition>,
}

/// Executes one source statement into one checked proof successor.
///
/// Execution uncertainty stays inside the symbolic kernel state. Only an
/// explicit proof `if`, C `branch`, or loop construct may change the number of
/// proof goals; a linear statement step never publishes hidden siblings.
#[allow(clippy::too_many_arguments)]
pub(super) fn execute_step_successor_from_frontier_position(
    execution: &ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &[Proposition],
    tactic_name: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    fact_transport_policy: StatementFactTransportPolicy,
    loop_step_policy: LoopStepPolicy,
    context: Option<&PureFactContext>,
) -> Result<ExecutionPointStepSuccessor, ClickError> {
    let mut successor = execution.clone();
    let mut successor_facts = available_pure_facts.to_vec();
    let assumptions = assumptions_from_propositions(&successor_facts);
    let introduced_facts = execute_step_from_frontier_position_selecting_path(
        &mut successor,
        proof_context,
        &mut successor_facts,
        &assumptions,
        tactic_name,
        prerequisite_policy,
        fact_transport_policy,
        loop_step_policy,
        None,
        None,
        context,
    )?;
    Ok(ExecutionPointStepSuccessor {
        execution: successor,
        pure_facts: successor_facts,
        introduced_facts,
    })
}

#[allow(clippy::too_many_arguments)]
fn execute_step_from_frontier_position_selecting_path(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut Vec<Proposition>,
    _assumptions: &PureFactContext,
    tactic_name: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    fact_transport_policy: StatementFactTransportPolicy,
    loop_step_policy: LoopStepPolicy,
    mut construction: Option<Construction<'_>>,
    selected_path_fact: Option<&Proposition>,
    context: Option<&PureFactContext>,
) -> Result<Vec<Proposition>, ClickError> {
    let function_block = proof_context.function_block;
    let function = proof_context.function;
    let parameters = proof_context.parsed_function.parameters();
    let arguments = proof_context.arguments;
    let function_environment = proof_context.function_environment;
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;

    let state: &mut CState = &mut execution.core.state;

    #[cfg(test)]
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        PLANNING_STATEMENT_TRANSITIONS.with(|transitions| {
            transitions.borrow_mut().push((
                claim_label.to_owned(),
                tactic_index,
                tactic_name.to_owned(),
            ));
        });
    }
    let statement_index = execution.core.frontier.next_statement_index;
    let source_region = proof_context.constants.source_layout.statement(statement_index).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve source statement({statement_index})"
        ))
    })?;
    if matches!(source_region.kind, SourceStatementKind::If { .. }) {
        let entered = execute_branch_step_from_frontier_position(
            execution,
            proof_context,
            available_pure_facts,
            "step",
            None,
            prerequisite_policy,
            BranchStepPolicy::RequireProven,
            false,
            construction.as_mut().map(Construction::reborrow),
            context,
        )?;
        debug_assert!(entered);
        return Ok(Vec::new());
    }
    let loop_index = match source_region.kind {
        SourceStatementKind::Loop { loop_index } => Some(loop_index),
        SourceStatementKind::Plain | SourceStatementKind::If { .. } => None,
    };
    let (execution_start_state, current_state, source_statement, remaining) =
        next_top_level_statement_from_frontier_position(
            ExecutionView::new(
                &execution.core.frontier,
                &execution.core.effect_facts,
                &execution.presentation.recorded_snapshots,
                &execution.presentation.surface_propositions,
                proof_context.constants.function_entry_state.as_ref(),
            ),
            state,
            function,
            arguments,
            claim_label,
            tactic_index,
            tactic_name,
        )?;
    if matches!(source_statement, CStatement::While { .. }) && loop_index.is_none() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve the source loop at statement({statement_index})"
        )));
    }
    if let (Some(loop_index), CStatement::While { .. }) = (loop_index, &source_statement)
        && matches!(loop_step_policy, LoopStepPolicy::EnterBody)
    {
        execute_concrete_loop_head_step(
            execution,
            proof_context,
            available_pure_facts,
            tactic_name,
            prerequisite_policy,
            statement_index,
            loop_index,
            source_region.continuation_node,
            execution_start_state,
            current_state,
            source_statement,
            remaining,
            construction.as_mut().map(Construction::reborrow),
        )?;
        return Ok(Vec::new());
    }
    let step_statement = source_statement;

    // The surface step for this statement is written from the proof state
    // *before* the statement runs. Its own check establishes this
    // statement's entry snapshots only while re-executing it, so construction
    // must see the program points exactly as they were before these entry
    // recordings: points the recording adds or overwrites here are presented
    // at their prior value (or absence) while the step is written.
    let mut construction_regions = vec![CodeRegion::Statement(statement_index)];
    if let Some(loop_index) = loop_index {
        construction_regions.push(CodeRegion::Loop(loop_index));
    }
    let construction_snapshot_overrides = construction.is_some().then(|| {
        construction_snapshot_overrides(
            &execution.presentation.recorded_snapshots,
            function_block,
            &construction_regions,
            ProgramPointKind::Entry,
        )
    });
    record_statement_program_snapshot_state(
        &mut execution.presentation.recorded_snapshots,
        function_block,
        statement_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    if let Some(loop_index) = loop_index {
        record_loop_program_snapshot_state(
            &mut execution.presentation.recorded_snapshots,
            function_block,
            loop_index,
            ProgramPointKind::Entry,
            current_state.clone(),
        );
    }
    let construction_snapshot_overrides = construction_snapshot_overrides.unwrap_or_default();
    let current_resources = current_state.resources().facts().to_vec();
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    let mut transitions = certified_statement_transitions(
        &current_state,
        available_pure_facts,
        &step_statement,
        function_environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &transition_label,
        &mut execution.core.next_opaque_call,
        &mut execution.core.next_kernel_variable,
        prerequisite_policy,
        fact_transport_policy,
        context,
    )?
    .0;
    if let Some(selected_path_fact) = selected_path_fact {
        transitions.retain(|transition| transition.path_facts.contains(selected_path_fact));
    }
    if transitions.len() > 1
        && transitions
            .iter()
            .all(|transition| matches!(transition.outcome, CStatementOutcome::Return { .. }))
    {
        // A single source return can have several valid operational outcomes,
        // notably when it returns an unresolved malloc result. This is not C
        // control flow and needs no proof-level case split: all successors
        // complete the function at the same statement boundary.
        if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning)
            && let Some(construction) = construction.as_mut()
        {
            let environments = construction.environments;
            let restore = apply_construction_snapshot_view(
                &mut execution.presentation.recorded_snapshots,
                &construction_snapshot_overrides,
            );
            construct_proof_step_for_planned_operation(
                execution,
                proof_context,
                construction.sink,
                &current_state,
                function_block,
                parameters,
                arguments,
                environments,
                &ConstructionEvidence::CertifiedStatementStep {
                    planned_transition: None,
                },
            );
            restore_construction_snapshot_view(
                &mut execution.presentation.recorded_snapshots,
                restore,
            );
        }

        let mut common_pure_facts = transitions[0].pure_facts.clone();
        common_pure_facts.retain(|fact| {
            transitions
                .iter()
                .skip(1)
                .all(|transition| transition.pure_facts.contains(fact))
        });
        let mut common_introduced_facts = transitions[0].introduced_facts.clone();
        common_introduced_facts.retain(|fact| {
            transitions
                .iter()
                .skip(1)
                .all(|transition| transition.introduced_facts.contains(fact))
        });
        execution
            .core
            .record_statement_outcomes(
                function,
                arguments,
                &transitions
                    .iter()
                    .map(|transition| {
                        (
                            transition.theorem.clone(),
                            transition.execution_facts.as_slice(),
                            transition.obligations.as_slice(),
                        )
                    })
                    .collect::<Vec<_>>(),
                transitions[0].context.clone(),
            )
            .map_err(|refusal| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` recorded statement evidence the proof object rejected: {}",
                    describe_evidence_refusal(&refusal, parameters, arguments)
                ))
            })?;
        let mut completed_outcomes = Vec::new();
        for transition in transitions {
            let mut completed_execution_facts = transition.execution_facts;
            append_execution_effect_facts(
                &mut completed_execution_facts,
                &execution.core.effect_facts,
            );
            let return_assumptions = assumptions_from_propositions(&transition.pure_facts);
            let (outcome, obligations) = c_function_outcome_from_statement_outcome(
                &execution_start_state,
                function,
                transition.outcome,
                transition.obligations,
                &return_assumptions,
            );
            completed_outcomes.push((outcome, completed_execution_facts, obligations));
        }
        let state: &mut CState = &mut execution.core.state;
        let completed = c_function_execution_candidates_from_outcomes(
            execution_start_state.clone(),
            function.clone(),
            arguments.to_vec(),
            completed_outcomes,
        );
        let execution_state = execution_start_state.clone();
        set_function_exit_execution(
            &mut execution.core.frontier,
            claim_label,
            tactic_index,
            tactic_name,
            execution_start_state,
            completed,
        )?;
        execution.core.frontier.next_statement_index = source_region.continuation_node;
        *available_pure_facts = common_pure_facts;
        *state = execution_state;
        return Ok(common_introduced_facts);
    }
    if transitions.len() != 1 {
        if matches!(prerequisite_policy, StatementPrerequisitePolicy::Exact) {
            let safe = transitions
                .iter()
                .filter(|transition| {
                    matches!(
                        transition.outcome,
                        CStatementOutcome::Normal(_) | CStatementOutcome::Return { .. }
                    )
                })
                .collect::<Vec<_>>();
            if let [safe] = safe.as_slice()
                && let Some(required) = safe
                    .pure_facts
                    .iter()
                    .find(|fact| !exact_fact_is_available(fact, available_pure_facts))
            {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` is missing exact prerequisite needed to select the safe statement transition: {required:?}"
                )));
            }
        }
        if let Some(kind) = transitions
            .iter()
            .find_map(|transition| match &transition.outcome {
                CStatementOutcome::UndefinedBehavior(kind) => Some(kind.clone()),
                _ => None,
            })
        {
            let outcome = CFunctionOutcome::UndefinedBehavior(kind);
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced {}\n{}",
                describe_function_outcome(&outcome, parameters, arguments),
                describe_proof_context(
                    available_pure_facts,
                    &current_resources,
                    parameters,
                    arguments,
                    &[]
                )
            )));
        }
        if let Some(error) = transitions
            .iter()
            .find_map(|transition| match &transition.outcome {
                CStatementOutcome::RuntimeError(error) => Some(error),
                _ => None,
            })
        {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced runtime error: {}\n{}",
                describe_runtime_error(error, parameters, arguments),
                describe_proof_context(
                    available_pure_facts,
                    &current_resources,
                    parameters,
                    arguments,
                    &[]
                )
            )));
        }
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires exactly one statement successor for {step_statement:?}, got {}\n{}",
            transitions.len(),
            describe_proof_context(
                available_pure_facts,
                &current_resources,
                parameters,
                arguments,
                &[]
            )
        )));
    }
    let transition = transitions
        .into_iter()
        .next()
        .expect("one statement transition was required");
    let introduced_facts = transition.introduced_facts.clone();
    if matches!(loop_step_policy, LoopStepPolicy::ApplyVerifiedRule)
        && let Some(loop_index) = loop_index
        && matches!(transition.outcome, CStatementOutcome::Normal(_))
        && let Some(loop_clause) = function_block
            .structural_clauses()
            .iter()
            .find(|clause| clause.region() == &CodeRegion::Loop(loop_index))
    {
        // The verified loop rule exports its effect summaries first, followed
        // by one lowered fact for each invariant check in declaration order,
        // followed by facts from the false loop-condition path. Preserve that
        // structural association instead of searching the ambient context for
        // a proposition that happens to match.
        // Isolate the rule's exported facts as the exact successor suffix
        // beyond the unchanged input prefix. A membership filter would
        // misalign the positional invariant mapping whenever an exported
        // fact is already available in a richer goal context.
        let exported: Vec<&Proposition> = if transition.pure_facts.len()
            >= available_pure_facts.len()
            && transition.pure_facts[..available_pure_facts.len()] == available_pure_facts[..]
        {
            transition.pure_facts[available_pure_facts.len()..]
                .iter()
                .collect()
        } else {
            transition
                .pure_facts
                .iter()
                .filter(|fact| !available_pure_facts.contains(fact))
                .collect()
        };
        let mut invariant_targets = exported.into_iter().filter(|fact| {
            !matches!(
                fact,
                Proposition::CMemoryEffectSummary { .. }
                    | Proposition::CMemoryMutatesOnly { .. }
                    | Proposition::CHeapAllocationFreed { .. }
            )
        });
        let mut mapped_invariants = Vec::new();
        for surface in loop_clause
            .items()
            .iter()
            .filter(|item| item.kind() == StructuralItemKind::Invariant)
            .filter_map(StructuralItem::proposition)
        {
            let target = if let Some((_, target)) = mapped_invariants
                .iter()
                .find(|(mapped_surface, _)| *mapped_surface == surface)
            {
                *target
            } else {
                invariant_targets.next().ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: verified loop summary omitted an exported fact for an invariant"
                    ))
                })?
            };
            mapped_invariants.push((surface, target));
            let exit_point = ProgramPointRef {
                region: CodeRegionRef::Loop(loop_index),
                kind: ProgramPointKind::Exit,
            };
            let exit_surface = surface_at_snapshot(surface, &exit_point)?;
            execution
                .presentation
                .surface_propositions
                .record_lowering(&exit_surface, target)?;
        }
    }
    let mut deferred_transport_operations = Vec::new();
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        let restore = apply_construction_snapshot_view(
            &mut execution.presentation.recorded_snapshots,
            &construction_snapshot_overrides,
        );
        deferred_transport_operations = append_statement_transition_certificate(
            execution,
            proof_context,
            &transition,
            if loop_index.is_some() {
                loop_step_policy
            } else {
                LoopStepPolicy::EnterBody
            },
            &current_state,
            function_block,
            parameters,
            arguments,
            construction.as_mut().map(Construction::reborrow),
        );
        restore_construction_snapshot_view(&mut execution.presentation.recorded_snapshots, restore);
    }
    execution
        .core
        .record_statement_transition(
            function,
            arguments,
            transition.theorem.clone(),
            transition.context.clone(),
            &transition.execution_facts,
            &transition.obligations,
        )
        .map_err(|refusal| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` recorded statement evidence the proof object rejected: {}",
                describe_evidence_refusal(&refusal, parameters, arguments)
            ))
        })?;
    let state: &mut CState = &mut execution.core.state;
    // A direct memory-snapshot transport needs no surface `transport`
    // tactic, but its target still needs a stable source form for a
    // later proof step. Record that form during both planning and
    // explicit certificate validation; otherwise check immediately forgets
    // evaluator guards such as `defined(x + 1)` that planning retained.
    let exit_point = ProgramPointRef {
        region: CodeRegionRef::Statement(statement_index),
        kind: ProgramPointKind::Exit,
    };
    for transport in transition
        .fact_transports
        .iter()
        .filter(|transport| !transport.statement_local)
    {
        let surfaces = execution
            .presentation
            .surface_propositions
            .surfaces(&transport.source)
            .cloned()
            .collect::<Vec<_>>();
        for surface in surfaces {
            let exit_surface = surface_at_snapshot(&surface, &exit_point)?;
            execution
                .presentation
                .surface_propositions
                .record_lowering(&exit_surface, &transport.target)?;
        }
    }
    // Preserve a surface name for each store while its exact source statement
    // is still known. The certified equation records the address evaluated
    // before the write and the memory immediately after it; a later attempt
    // to reconstruct that name from the final state can only re-evaluate the
    // address and loses this association for deep, state-dependent indices.
    let store_exit_point = ProgramPointRef {
        region: CodeRegionRef::Statement(statement_index),
        kind: ProgramPointKind::Exit,
    };
    for equation in crate::kernel::certified_store_equations(&transition.execution_facts) {
        if let Some(ClickProposition::Comparison {
            left,
            operator,
            right,
        }) = synthesize_surface_proposition(&equation, parameters, arguments, &current_state)
        {
            let store_entry_point = ProgramPointRef {
                region: CodeRegionRef::Statement(statement_index),
                kind: ProgramPointKind::Entry,
            };
            let at =
                |point: &ProgramPointRef, expression: ContractExpression| ContractExpression::At {
                    selector: SnapshotSelector::ProgramPoint(point.clone()),
                    expression: Box::new(expression),
                };
            // The neutral pointer addition makes the Index use the outer
            // exit snapshot's memory while its base and index retain their
            // entry values.
            let exit_load = if let ContractExpression::Index(base, index) = left {
                ContractExpression::Index(
                    Box::new(ContractExpression::Add(
                        Box::new(at(&store_entry_point, *base)),
                        Box::new(ContractExpression::CFragment(CExpression::Value(int32(0)))),
                    )),
                    Box::new(at(&store_entry_point, *index)),
                )
            } else {
                left
            };
            let surface = ClickProposition::Comparison {
                left: at(&store_exit_point, exit_load),
                operator,
                right: at(&store_entry_point, right),
            };
            execution
                .presentation
                .surface_propositions
                .record_lowering(&surface, &equation)?;
        }
    }
    let execution_pure_facts = transition.execution_facts;
    append_execution_effect_facts(&mut execution.core.effect_facts, &execution_pure_facts);
    let transition_obligations = transition.obligations;
    let successor_pure_facts = transition.pure_facts;
    let outcome = transition.outcome;
    if let Some(statement_exit_state) = match &outcome {
        CStatementOutcome::Normal(state)
        | CStatementOutcome::Break(state)
        | CStatementOutcome::Continue(state)
        | CStatementOutcome::Return { state, .. } => Some(state.clone()),
        CStatementOutcome::UndefinedBehavior(_) | CStatementOutcome::RuntimeError(_) => None,
        CStatementOutcome::VerificationDiverges => None,
    } {
        record_statement_program_snapshot_state(
            &mut execution.presentation.recorded_snapshots,
            function_block,
            statement_index,
            ProgramPointKind::Exit,
            statement_exit_state,
        );
        if let Some(loop_index) = loop_index {
            record_loop_program_snapshot_state(
                &mut execution.presentation.recorded_snapshots,
                function_block,
                loop_index,
                ProgramPointKind::Exit,
                match &outcome {
                    CStatementOutcome::Normal(state)
                    | CStatementOutcome::Break(state)
                    | CStatementOutcome::Continue(state)
                    | CStatementOutcome::Return { state, .. } => state.clone(),
                    CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_)
                    | CStatementOutcome::VerificationDiverges => unreachable!(),
                },
            );
        }
    }

    match outcome {
        CStatementOutcome::Normal(next_state) => {
            // Completing this statement statically completes the recorded
            // chain of enclosing branch regions it ends.
            for exited in proof_context
                .constants
                .source_layout
                .exited_branch_regions(statement_index)
                .to_vec()
            {
                record_statement_program_snapshot_state(
                    &mut execution.presentation.recorded_snapshots,
                    function_block,
                    exited,
                    ProgramPointKind::Exit,
                    next_state.clone(),
                );
            }
            let remaining = if let Some(remaining) = remaining {
                execution.core.frontier.next_statement_index = source_region.continuation_node;
                Some(remaining)
            } else {
                resume_after_completed_region(&mut execution.core.frontier)
            };
            *available_pure_facts = successor_pure_facts;
            execution.core.frontier.execution_start_state = Some(execution_start_state);
            *state = next_state.clone();
            match remaining {
                Some(remaining) => {
                    execution.core.frontier.position = FrontierPosition::StatementEntry {
                        remaining: remaining.into(),
                    };
                    record_statement_program_snapshot_state(
                        &mut execution.presentation.recorded_snapshots,
                        function_block,
                        execution.core.frontier.next_statement_index,
                        ProgramPointKind::Entry,
                        next_state,
                    );
                }
                None if finish_exhausted_region(&mut execution.core.frontier) => {
                    // The region's boundary state is also the entry state of
                    // its statically known continuation, exactly as the arm
                    // recorded it when continuations were popped at runtime.
                    record_statement_program_snapshot_state(
                        &mut execution.presentation.recorded_snapshots,
                        function_block,
                        source_region.continuation_node,
                        ProgramPointKind::Entry,
                        next_state,
                    );
                }
                None => {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached the end of the function without a return"
                    )));
                }
            }
        }
        CStatementOutcome::Return { .. } => {
            if matches!(&outcome, CStatementOutcome::Return { .. }) {
                record_completed_continuation_exits(&mut execution.core.frontier);
            }
            let return_assumptions = assumptions_from_propositions(&successor_pure_facts);
            let (outcome, obligations) = c_function_outcome_from_statement_outcome(
                &execution_start_state,
                function,
                outcome,
                transition_obligations,
                &return_assumptions,
            );
            let mut completed_execution_facts = execution_pure_facts;
            append_execution_effect_facts(
                &mut completed_execution_facts,
                &execution.core.effect_facts,
            );
            let completed = c_function_execution_candidates_from_outcomes(
                execution_start_state.clone(),
                function.clone(),
                arguments.to_vec(),
                vec![(outcome, completed_execution_facts, obligations)],
            );
            let execution_state = execution_start_state.clone();
            set_function_exit_execution(
                &mut execution.core.frontier,
                claim_label,
                tactic_index,
                tactic_name,
                execution_start_state,
                completed,
            )?;
            execution.core.frontier.next_statement_index = source_region.continuation_node;
            *state = execution_state;
        }
        CStatementOutcome::Break(next_state) | CStatementOutcome::Continue(next_state) => {
            *state = next_state;
        }
        CStatementOutcome::VerificationDiverges => {
            let mut completed_execution_facts = execution_pure_facts;
            append_execution_effect_facts(
                &mut completed_execution_facts,
                &execution.core.effect_facts,
            );
            let completed = c_function_execution_candidates_from_outcomes(
                execution_start_state.clone(),
                function.clone(),
                arguments.to_vec(),
                vec![(
                    CFunctionOutcome::VerificationDiverges,
                    completed_execution_facts,
                    transition_obligations,
                )],
            );
            let execution_state = execution_start_state.clone();
            set_function_exit_execution(
                &mut execution.core.frontier,
                claim_label,
                tactic_index,
                tactic_name,
                execution_start_state,
                completed,
            )?;
            execution.core.frontier.next_statement_index = source_region.continuation_node;
            *state = execution_state;
        }
        CStatementOutcome::UndefinedBehavior(kind) => {
            let outcome = CFunctionOutcome::UndefinedBehavior(kind);
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced {}\n{}",
                describe_function_outcome(&outcome, parameters, arguments),
                describe_proof_context(
                    available_pure_facts,
                    &current_resources,
                    parameters,
                    arguments,
                    &execution_pure_facts
                )
            )));
        }
        CStatementOutcome::RuntimeError(error) => {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced runtime error: {}\n{}",
                describe_runtime_error(&error, parameters, arguments),
                describe_proof_context(
                    available_pure_facts,
                    &current_resources,
                    parameters,
                    arguments,
                    &execution_pure_facts
                )
            )));
        }
    }
    // Standalone fact-transport steps are written against the post-statement
    // state, so their construction runs after the statement's exit snapshots
    // are in place. Each transport adds its target to the certificate-visible
    // certificate facts, and finishing the transports retires the stale
    // pre-statement sources, mirroring what the certificate's own check
    // carries across this statement.
    if construction.is_some() {
        // Construction reads the post-statement state while it records into
        // the execution; the transports do not change the state.
        let exit_state = (*execution.core.state).clone();
        for operation in &deferred_transport_operations {
            if let Some(construction) = construction.as_mut() {
                let environments = construction.environments;
                construct_proof_step_for_planned_operation(
                    execution,
                    proof_context,
                    construction.sink,
                    &exit_state,
                    function_block,
                    parameters,
                    arguments,
                    environments,
                    operation,
                );
            }
            let certificate_facts = &mut execution.presentation.surface_record.certificate_facts;
            match operation {
                ConstructionEvidence::CertifiedFactTransport { target, .. } => {
                    certificate_facts.insert(target.clone());
                }
                ConstructionEvidence::FinishCertifiedFactTransports(sources) => {
                    certificate_facts.retain(|fact| {
                        !sources.iter().any(|source| {
                            source == fact
                                || exactly_available_fact(source, std::slice::from_ref(fact))
                                    .is_some()
                        })
                    });
                }
                _ => {}
            }
        }
    }
    Ok(introduced_facts)
}

/// Execution exhausted the frontier's own statement tree with no enclosing
/// continuation. A bounded region — a loop-preservation body or a branch
/// arm — reaches its typed boundary; a whole-function region has no boundary
/// short of `return`, so the caller keeps its end-of-function error.
pub(super) fn finish_exhausted_region(frontier: &mut ExecutionFrontier) -> bool {
    match frontier.region {
        ExecutionRegionKind::LoopBody | ExecutionRegionKind::BranchArm => {
            debug_assert!(frontier.continuations.is_empty());
            frontier.position = FrontierPosition::RegionBoundary;
            true
        }
        ExecutionRegionKind::Function => false,
    }
}

pub(super) fn resume_after_completed_region(
    frontier: &mut ExecutionFrontier,
) -> Option<CStatement> {
    while let Some(continuation) = frontier.continuations.pop() {
        frontier.next_statement_index = continuation.next_statement_index;
        if let Some(remaining) = continuation.remaining {
            return Some(Arc::unwrap_or_clone(remaining));
        }
    }
    None
}

fn record_completed_continuation_exits(frontier: &mut ExecutionFrontier) {
    while frontier.continuations.pop().is_some() {}
}

#[allow(clippy::too_many_arguments)]
pub(super) fn record_current_statement_entry(
    frontier: &ExecutionFrontier,
    recorded_snapshots: &mut RecordedSnapshots,
    state: &CState,
    function_block: &FunctionBlock,
    function: &CFunction,
    arguments: &[CExpression],
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
) -> Result<(), ClickError> {
    let current_state = match &frontier.position {
        FrontierPosition::FunctionEntry => c_function_entry_state(state, function, arguments)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not bind function arguments"
                ))
            })?,
        FrontierPosition::StatementEntry { .. } => state.clone(),
        FrontierPosition::FunctionExit { .. } | FrontierPosition::RegionBoundary => {
            return Ok(())
        }
    };
    record_statement_program_snapshot_state(
        recorded_snapshots,
        function_block,
        frontier.next_statement_index,
        ProgramPointKind::Entry,
        current_state,
    );
    Ok(())
}

pub(super) const BOUNDED_EXECUTE_STEP_LIMIT: usize = 10_000;

#[derive(Clone)]
pub(super) struct BoundedProofFrontier {
    pub(super) execution: ExecutionProofState,
    pub(super) pure_facts: Vec<Proposition>,
    /// This path's construction sink while planning constructs steps.
    pub(super) sink: Option<ProofCertificateBuilder>,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn bounded_execute_from_frontier_position(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut Vec<Proposition>,
    prerequisite_policy: StatementPrerequisitePolicy,
    mut construction: Option<Construction<'_>>,
) -> Result<(), ClickError> {
    let function = proof_context.function;
    let arguments = proof_context.arguments;
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;

    // Each explored path constructs its own surface steps from a clean
    // builder; the paths are merged back into one step sequence (with `if`
    // structure at genuine forks) once the frontiers are complete. Every
    // path starts from the certificate-visible certificate facts at this point.
    // Each explored path constructs its own surface steps into its own sink,
    // seeded with the planning anchor; the paths are merged back into one
    // step sequence (with `if` structure at genuine forks) once complete.
    let mut pending = vec![BoundedProofFrontier {
        execution: execution.clone(),
        pure_facts: available_pure_facts.clone(),
        sink: construction
            .as_ref()
            .map(|construction| ProofCertificateBuilder {
                last_step_entry: construction.sink.last_step_entry.clone(),
                ..ProofCertificateBuilder::default()
            }),
    }];
    let mut completed = Vec::new();
    let mut executed_steps = 0;

    while let Some(mut frontier) = pending.pop() {
        if frontier.execution.core.frontier.is_at_function_exit() {
            completed.push(frontier);
            continue;
        }
        if executed_steps == BOUNDED_EXECUTE_STEP_LIMIT {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute` exhausted its {BOUNDED_EXECUTE_STEP_LIMIT}-step budget at statement({})",
                frontier.execution.core.frontier.next_statement_index
            )));
        }
        executed_steps += 1;

        let statement_index = frontier.execution.core.frontier.next_statement_index;
        let source_region = proof_context
            .constants.source_layout
            .statement(statement_index)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `execute` could not resolve source statement({})",
                    frontier.execution.core.frontier.next_statement_index
                ))
            })?;
        if matches!(source_region.kind, SourceStatementKind::If { .. }) {
            for take_then in [false, true] {
                let mut branch = frontier.clone();
                let entered = execute_branch_step_from_frontier_position(
                    &mut branch.execution,
                    proof_context,
                    &mut branch.pure_facts,
                    "execute",
                    Some(take_then),
                    prerequisite_policy,
                    BranchStepPolicy::Explore,
                    false,
                    construction.as_ref().map(|construction| Construction {
                        environments: construction.environments,
                        sink: branch
                            .sink
                            .as_mut()
                            .expect("construction implies a branch sink"),
                    }),
                    None,
                )?;
                if entered {
                    pending.push(branch);
                }
            }
            continue;
        }

        if matches!(
            frontier_statement(&frontier.execution, function),
            Ok(CStatement::Switch { .. })
        ) {
            let statement = frontier_statement(&frontier.execution, function).map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `execute` could not inspect switch: {error}"
                ))
            })?;
            let mut next_opaque_call = frontier.execution.core.next_opaque_call;
            let mut next_kernel_variable = frontier.execution.core.next_kernel_variable;
            let (transitions, _) = certified_statement_transitions(
                &frontier.execution.core.state,
                &frontier.pure_facts,
                &statement,
                proof_context.function_environment,
                CExecutionSemantics::APPLY_VERIFIED_RULES,
                "`execute` switch path planning",
                &mut next_opaque_call,
                &mut next_kernel_variable,
                StatementPrerequisitePolicy::Contextual,
                StatementFactTransportPolicy::Automatic,
                None,
            )?;
            if transitions.len() > 1
                && !transitions.iter().all(|transition| {
                    matches!(transition.outcome, CStatementOutcome::Return { .. })
                })
            {
                let path_choices = transitions
                    .iter()
                    .map(|transition| {
                        switch_surface_path_choices(
                            transition,
                            &frontier.execution.core.state,
                            proof_context,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let choice_count = path_choices.iter().map(Vec::len).max().unwrap_or_default();
                if choice_count == 0 || path_choices.iter().any(Vec::is_empty) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `execute` could not construct checked proof branches for switch paths"
                    )));
                }
                for (transition, choices) in transitions.iter().zip(path_choices) {
                    if transition.path_facts.is_empty() {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: switch path had no checked path fact"
                        )));
                    }
                    let mut branch = frontier.clone();
                    if let Some(construction) = construction.as_ref() {
                        let base_occurrence = branch.execution.core.next_path_choice;
                        for (choice_index, (condition, value)) in choices.into_iter().enumerate() {
                            construct_proof_step_for_planned_operation(
                                &mut branch.execution,
                                proof_context,
                                branch
                                    .sink
                                    .as_mut()
                                    .expect("construction implies a branch sink"),
                                &frontier.execution.core.state,
                                proof_context.function_block,
                                proof_context.parsed_function.parameters(),
                                proof_context.arguments,
                                construction.environments,
                                &ConstructionEvidence::CertifiedPathAssumption {
                                    occurrence: base_occurrence + choice_index,
                                    condition,
                                    value,
                                    facts: transition.path_facts.clone(),
                                    theorem: transition.theorem.clone(),
                                },
                            );
                        }
                        for fact in &transition.path_facts {
                            branch
                                .execution
                                .presentation
                                .surface_record
                                .certificate_facts
                                .insert(fact.clone());
                            if !branch.pure_facts.contains(fact) {
                                branch.pure_facts.push(fact.clone());
                            }
                        }
                        branch.execution.core.next_path_choice += choice_count;
                    }
                    let assumptions = assumptions_from_propositions(&branch.pure_facts);
                    execute_step_from_frontier_position_selecting_path(
                        &mut branch.execution,
                        proof_context,
                        &mut branch.pure_facts,
                        &assumptions,
                        "execute",
                        prerequisite_policy,
                        StatementFactTransportPolicy::Automatic,
                        LoopStepPolicy::EnterBody,
                        construction.as_ref().map(|construction| Construction {
                            environments: construction.environments,
                            sink: branch
                                .sink
                                .as_mut()
                                .expect("construction implies a branch sink"),
                        }),
                        None,
                        None,
                    )
                    .map_err(|error| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `execute` failed after switch path split: {}",
                            error.message()
                        ))
                    })?;
                    pending.push(branch);
                }
                continue;
            }
        }

        let assumptions = assumptions_from_propositions(&frontier.pure_facts);
        execute_step_from_frontier_position(
            &mut frontier.execution,
            proof_context,
            &mut frontier.pure_facts,
            &assumptions,
            "execute",
            prerequisite_policy,
            StatementFactTransportPolicy::Automatic,
            LoopStepPolicy::EnterBody,
            construction.as_ref().map(|construction| Construction {
                environments: construction.environments,
                sink: frontier
                    .sink
                    .as_mut()
                    .expect("construction implies a frontier sink"),
            }),
        )
        .map_err(|error| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute` failed after {executed_steps} small execution steps: {}",
                error.message()
            ))
        })?;
        pending.push(frontier);
    }

    let synthesized_paths = construction.as_mut().map(|construction| {
        let paths = completed
            .iter()
            .map(|frontier| frontier.sink.clone().unwrap_or_default())
            .collect::<Vec<_>>();
        (construction, synthesize_surface_alternatives(paths))
    });
    merge_bounded_execution_frontiers(
        execution,
        available_pure_facts,
        function,
        arguments,
        completed,
        claim_label,
        tactic_index,
    )?;
    if let Some((construction, synthesized)) = synthesized_paths {
        match synthesized {
            Ok(steps) => {
                for step in steps {
                    construction.sink.push_step(step);
                }
            }
            Err(message) => construction.sink.block(format!(
                "could not lower certified branch alternatives: {message}"
            )),
        }
    }
    Ok(())
}

fn frontier_statement(
    execution: &ExecutionProofState,
    function: &CFunction,
) -> Result<CStatement, String> {
    let remaining = match &execution.core.frontier.position {
        FrontierPosition::FunctionEntry => function.body().clone(),
        FrontierPosition::StatementEntry { remaining } => remaining.as_ref().clone(),
        FrontierPosition::FunctionExit { .. } => {
            return Err("frontier is already at function exit".to_string());
        }
        FrontierPosition::RegionBoundary => {
            return Err("frontier is already at a region boundary".to_string());
        }
    };
    split_next_source_operation(&remaining).map(|(statement, _)| statement)
}

fn switch_surface_path_choices(
    transition: &CertifiedStatementTransition,
    state: &CState,
    proof_context: &ExecutionProofContext<'_>,
) -> Result<Vec<(ClickProposition, bool)>, ClickError> {
    transition
        .path_facts
        .iter()
        .filter_map(|fact| {
            let Proposition::ConditionIs(condition, value) = fact else {
                return None;
            };
            let positive = Proposition::ConditionIs(condition.clone(), true);
            let surface = synthesize_surface_proposition(
                &positive,
                proof_context.parsed_function.parameters(),
                proof_context.arguments,
                state,
            )?;
            Some(Ok((surface, *value)))
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
pub(super) fn merge_bounded_execution_frontiers(
    execution: &mut ExecutionProofState,
    available_pure_facts: &mut Vec<Proposition>,
    function: &CFunction,
    arguments: &[CExpression],
    mut completed: Vec<BoundedProofFrontier>,
    claim_label: &str,
    tactic_index: usize,
) -> Result<(), ClickError> {
    if completed.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `execute` produced no complete execution paths"
        )));
    }

    let execution_start_state = completed[0]
        .execution.core.frontier
        .execution_start_state
        .clone()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute` has no execution start execution.core.state"
            ))
        })?;
    let mut common_pure_facts = completed[0].pure_facts.clone();
    common_pure_facts.retain(|fact| {
        completed
            .iter()
            .skip(1)
            .all(|frontier| frontier.pure_facts.contains(fact))
    });
    let mut common_snapshots = completed[0]
        .execution
        .presentation
        .recorded_snapshots
        .clone();
    common_snapshots.retain(|selector, snapshot_state| {
        completed.iter().skip(1).all(|frontier| {
            frontier
                .execution
                .presentation
                .recorded_snapshots
                .get(selector)
                == Some(snapshot_state)
        })
    });

    let mut paths = Vec::new();
    for frontier in &completed {
        let function_execution = frontier
            .execution
            .core
            .frontier
            .execution()
            .expect("completed bounded frontier should have an execution");
        for path in function_execution.paths() {
            let mut facts = path.execution_facts();
            for fact in &frontier.pure_facts {
                let fact = ExecutionPureFact::new(fact.clone());
                if !facts.contains(&fact) {
                    facts.push(fact);
                }
            }
            paths.push((path.outcome().clone(), facts, path.obligations().to_vec()));
        }
    }
    let function_execution = c_function_execution_candidates_from_outcomes(
        execution_start_state.clone(),
        function.clone(),
        arguments.to_vec(),
        paths,
    );

    let mut merged = completed.remove(0);
    merged.execution.presentation.recorded_snapshots = common_snapshots;
    merged.execution.core.frontier.position = FrontierPosition::FunctionExit {
        execution: function_execution,
    };
    merged.execution.core.state = execution_start_state.into();
    merged.pure_facts = common_pure_facts;
    *execution = merged.execution;
    *available_pure_facts = merged.pure_facts;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn execute_rest_from_frontier_position(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut Vec<Proposition>,
    mut construction: Option<Construction<'_>>,
) -> Result<(), ClickError> {
    let function = proof_context.function;

    loop {
        let can_execute_one_step = match &execution.core.frontier.position {
            FrontierPosition::FunctionEntry => split_next_execution_step(function.body()).is_ok(),
            FrontierPosition::StatementEntry { remaining } => {
                split_next_execution_step(remaining).is_ok()
            }
            FrontierPosition::FunctionExit { .. } | FrontierPosition::RegionBoundary => {
                return Ok(());
            }
        };
        if !can_execute_one_step {
            break;
        }

        let assumptions = assumptions_from_propositions(available_pure_facts);
        execute_step_from_frontier_position(
            execution,
            proof_context,
            available_pure_facts,
            &assumptions,
            "execute",
            StatementPrerequisitePolicy::Planning,
            StatementFactTransportPolicy::Automatic,
            LoopStepPolicy::ApplyVerifiedRule,
            construction.as_mut().map(Construction::reborrow),
        )?;
    }

    if !execution.core.frontier.is_at_function_exit() {
        bounded_execute_from_frontier_position(
            execution,
            proof_context,
            available_pure_facts,
            StatementPrerequisitePolicy::Planning,
            construction.as_mut().map(Construction::reborrow),
        )?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn execute_until_statement(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut Vec<Proposition>,
    statement_index: usize,
    prerequisite_policy: StatementPrerequisitePolicy,
    mut construction: Option<Construction<'_>>,
) -> Result<(), ClickError> {
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;

    if proof_context
        .constants
        .source_layout
        .statement(statement_index)
        .is_none()
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: function has no source statement({statement_index}); it contains {} statement regions",
            proof_context.constants.source_layout.statement_count()
        )));
    }

    if execution.core.frontier.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `execute_until(statement({statement_index}))` cannot run after execution already reached function exit"
        )));
    }
    if statement_index < execution.core.frontier.next_statement_index {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `execute_until(statement({statement_index}))` cannot move backward from statement({})",
            execution.core.frontier.next_statement_index
        )));
    }

    while execution.core.frontier.next_statement_index != statement_index {
        let region_start = execution.core.frontier.next_statement_index;
        let assumptions = assumptions_from_propositions(available_pure_facts);
        execute_step_from_frontier_position(
            execution,
            proof_context,
            available_pure_facts,
            &assumptions,
            "execute_until",
            prerequisite_policy,
            StatementFactTransportPolicy::Automatic,
            LoopStepPolicy::ApplyVerifiedRule,
            construction.as_mut().map(Construction::reborrow),
        )?;
        if execution.core.frontier.is_at_function_exit() {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute_until(statement({statement_index}))` reached function exit before its target"
            )));
        }
        if execution.core.frontier.next_statement_index > statement_index {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute_until(statement({statement_index}))` target is not reachable from the current execution path; advancing statement({region_start}) moved the frontier to statement({})",
                execution.core.frontier.next_statement_index
            )));
        }
    }
    Ok(())
}

fn split_next_execution_step(
    statement: &CStatement,
) -> Result<(CStatement, Option<CStatement>), String> {
    let (source_statement, remaining) = split_next_source_operation(statement)?;
    if matches!(source_statement, CStatement::If { .. }) {
        return Err("next statement is an `if`; use `step()` or `step()`".to_string());
    }
    Ok((source_statement, remaining))
}

pub(super) fn split_next_source_operation(
    statement: &CStatement,
) -> Result<(CStatement, Option<CStatement>), String> {
    match statement {
        CStatement::Seq(first, second) => {
            let (source_statement, first_remaining) = split_next_source_operation(first)?;
            let remaining = match first_remaining {
                Some(first_remaining) => c_seq(first_remaining, second.as_ref().clone()),
                None => second.as_ref().clone(),
            };
            Ok((source_statement, Some(remaining)))
        }
        statement => Ok((statement.clone(), None)),
    }
}

pub(super) fn flatten_top_level_sequence(
    statement: &CStatement,
    statements: &mut Vec<CStatement>,
) -> Result<(), String> {
    match statement {
        CStatement::Seq(first, second) => {
            flatten_top_level_sequence(first, statements)?;
            flatten_top_level_sequence(second, statements)
        }
        statement => {
            statements.push(statement.clone());
            Ok(())
        }
    }
}

pub(super) fn sequence_from_statements(statements: &[CStatement]) -> Option<CStatement> {
    let mut level = statements.to_vec();
    while level.len() > 1 {
        let mut next_level = Vec::with_capacity(level.len().div_ceil(2));
        let mut statements = level.into_iter();
        while let Some(first) = statements.next() {
            next_level.push(match statements.next() {
                Some(second) => c_seq(first, second),
                None => first,
            });
        }
        level = next_level;
    }
    level.pop()
}

fn set_function_exit_execution(
    frontier: &mut ExecutionFrontier,
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
    execution_start_state: CState,
    execution: CFunctionExecutionCandidates,
) -> Result<(), ClickError> {
    if frontier.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` cannot run after execution already reached function exit"
        )));
    }
    frontier.execution_start_state = Some(execution_start_state);
    frontier.position = FrontierPosition::FunctionExit { execution };
    Ok(())
}

#[cfg(test)]
mod cursor_sequence_tests {
    use super::*;

    #[test]
    fn large_straight_line_cursor_advances_on_a_small_stack() {
        std::thread::Builder::new()
            .name("large-straight-line-cursor".to_string())
            .stack_size(256 * 1024)
            .spawn(|| {
                let statements = vec![CStatement::Skip; 10_000];
                let mut remaining = sequence_from_statements(&statements)
                    .expect("the generated block should not be empty");
                let mut count = 0;
                loop {
                    let (statement, tail) = split_next_source_operation(&remaining)
                        .expect("a balanced sequence should have a next operation");
                    assert_eq!(statement, CStatement::Skip);
                    count += 1;
                    let Some(tail) = tail else {
                        break;
                    };
                    remaining = tail;
                }
                assert_eq!(count, 10_000);
            })
            .expect("the small-stack cursor thread should start")
            .join()
            .expect("large straight-line cursor advancement should be stack bounded");
    }
}

/// The driver's account of a refused record call: the proof object's reason,
/// then what it expected and what it was offered when the judgment concerned
/// statements or a premise.
pub(super) fn describe_evidence_refusal(
    refusal: &crate::kernel::proof::EvidenceRefusal,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    let mut text = refusal.reason.to_string();
    if let Some(expected) = &refusal.expected {
        text.push_str(&format!(
            "; the source statement to consume next is `{}`",
            describe_statement_head(expected)
        ));
    }
    if let Some(proved) = &refusal.proved {
        text.push_str(&format!(
            ", the theorem proves `{}`",
            describe_statement_head(proved)
        ));
    }
    if let Some(premise) = &refusal.premise {
        text.push_str(&format!(
            "; the premise is {}",
            describe_pure_fact(premise, parameters, arguments)
        ));
    }
    text
}

/// A one-line C spelling of a statement's head, enough to recognize it in
/// a diagnostic: the first statement of a sequence, a loop or branch by its
/// condition, a body by its operation.
fn describe_statement_head(statement: &CStatement) -> String {
    match statement {
        CStatement::Seq(first, _) => describe_statement_head(first),
        CStatement::Skip => "skip".to_string(),
        CStatement::Break => "break".to_string(),
        CStatement::Continue => "continue".to_string(),
        CStatement::ContinueWithStep { .. } => "continue".to_string(),
        CStatement::Declare { name, .. } => format!("declare {name}"),
        CStatement::Assign { name, expression } => {
            format!("{name} = {}", describe_c_expression(expression))
        }
        CStatement::CallAssign {
            target,
            function_name,
            arguments,
        } => format!(
            "{target} = {function_name}({})",
            arguments
                .iter()
                .map(describe_c_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        CStatement::Call {
            function_name,
            arguments,
        } => format!(
            "{function_name}({})",
            arguments
                .iter()
                .map(describe_c_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        CStatement::HeapAllocate {
            target,
            bytes,
            zeroed,
        } => {
            let function = if *zeroed { "calloc" } else { "malloc" };
            format!("{target} = {function}({})", describe_c_expression(bytes))
        }
        CStatement::HeapFree { pointer } => format!("free({})", describe_c_expression(pointer)),
        CStatement::Assert { condition, .. } => {
            format!("assert({})", describe_c_expression(condition))
        }
        CStatement::Return(expression) => format!("return {}", describe_c_expression(expression)),
        CStatement::Store { pointer, value } | CStatement::TypedStore { pointer, value, .. } => {
            format!(
                "*{} = {}",
                describe_c_expression(pointer),
                describe_c_expression(value)
            )
        }
        CStatement::Update {
            target, operand, ..
        } => format!(
            "update {} with {}",
            describe_c_expression(target),
            describe_c_expression(operand)
        ),
        CStatement::If { condition, .. } => format!("if ({})", describe_c_expression(condition)),
        CStatement::While { condition, .. } => {
            format!("while ({})", describe_c_expression(condition))
        }
        CStatement::Switch { expression, .. } => {
            format!("switch ({})", describe_c_expression(expression))
        }
    }
}
