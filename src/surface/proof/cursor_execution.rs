use super::*;
use crate::kernel::CheckedCallEventScope;
use crate::kernel::ExecutionFactSource;
use crate::kernel::abstract_c_state_for_interface_join_across;
use std::sync::Arc;

/// Checks a branch interface directly against the structural join's
/// persistent proof facts, without cloning or re-indexing unrelated facts.
#[allow(clippy::too_many_arguments)]
pub(super) fn apply_branch_interface_with_proof_facts(
    target: &ProgramPointRef,
    assertions: &[ProofAssertion],
    written_assertions: &[ProofAssertion],
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut ProofFacts,
    stable_join_locals: &BTreeMap<String, CValue>,
    sibling_join_states: Option<&[&CState]>,
    // `join_next_kernel_variable` is the counter every sibling arm abstracts
    // from: the highest of the arms' own. The arms' abstractions are compared
    // for equality, so they must count from one shared lower bound rather
    // than each from its own.
    join_next_kernel_variable: u64,
    needs_abstraction: bool,
) -> Result<(), ClickError> {
    // Lower the resolved proof-local values, but retain their written names
    // for later certificates. Internal pointer values are not source syntax.
    assert_eq!(assertions.len(), written_assertions.len());
    let tactic_index = proof_context.tactic_index;
    let parameters = proof_context.parsed_function.parameters();
    let arguments = proof_context.arguments;
    let predicate_environment = proof_context.spec_definitions.predicates;
    let click_function_environment = proof_context.spec_definitions.functions;
    let resource_environment = proof_context.resource_environment;
    let claim_label = proof_context.claim_label;

    let state: &mut CState = &mut execution.core.state;

    let mut concrete_facts = available_pure_facts.clone();
    let mut established_interface_resources = Vec::new();
    for (assertion, written) in assertions.iter().zip(written_assertions) {
        match assertion {
            ProofAssertion::Fact(surface_fact) => {
                let ProofAssertion::Fact(written_fact) = written else {
                    unreachable!("resolved interface assertion retains its written kind");
                };
                let fact = lower_fixed_state_proposition_with_assumptions(
                        surface_fact,
                        concrete_facts.assumptions(),
                        parameters,
                        arguments,
                        proof_context.old_reference_state(&execution.core.frontier, state),
                        state,
                        None,
                        &execution.presentation.recorded_snapshots,
                        SpecDefinitions::new(predicate_environment, click_function_environment),
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `branch ensuring` fact: {message}"
                        ))
                })?;
                execution
                    .presentation
                    .surface_propositions
                    .record_lowering(written_fact, &fact)?;
                if !crate::kernel::proof::checked_branch_fact_is_available(&concrete_facts, &fact) {
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
                let expected = lower_interface_resource_clause(
                    resource,
                    parameters,
                    arguments,
                    state,
                    concrete_facts.assumptions(),
                )?;
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
    // `old(...)` in an interface fact means the function's entry, also
    // inside a loop body, where the region's own start is a later state.
    let old_reference = proof_context
        .old_reference_state(&execution.core.frontier, state)
        .clone();
    let abstraction = match sibling_join_states {
        Some(states) => abstract_c_state_for_interface_join_across(
            state,
            states,
            stable_join_locals,
            join_next_kernel_variable,
        ),
        None => abstract_c_state_for_join(state, stable_join_locals, join_next_kernel_variable),
    };
    let abstraction = abstraction.map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not abstract `branch` target state: {message}"
        ))
    })?;
    let mut abstract_state = abstraction.state;
    let mut join_kernel_variable_mark = abstraction.next_kernel_variable;

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
            // A named instance may carry a different model in each arm. The
            // rejoined proof holds it with a fresh model, drawn after the
            // abstraction's own identities; the kernel's check of the join
            // draws the same one.
            let with_fresh_model;
            let resource = match resource {
                ResourceClause::Named {
                    binding,
                    resource: declared,
                } if binding.schema.is_some() => {
                    let schema = binding.schema.as_ref().expect("checked just above");
                    let (fields, next) = crate::kernel::interface_join_instance_fields(
                        schema,
                        binding.identity,
                        join_kernel_variable_mark,
                    )
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not give interface resource `{}` a fresh model",
                            binding.name
                        ))
                    })?;
                    join_kernel_variable_mark = next;
                    with_fresh_model = ResourceClause::Named {
                        binding: ResourceInstanceBinding {
                            fields: Some(fields),
                            ..binding.clone()
                        },
                        resource: declared.clone(),
                    };
                    &with_fresh_model
                }
                other => other,
            };
            let fact = lower_interface_resource_clause(
                resource,
                parameters,
                arguments,
                &abstract_state,
                concrete_facts.assumptions(),
            )
            .map_err(|_| {
                // The clause was read in this arm's own state above, so what
                // fails here is reading it in the state the arms join in.
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: the `ensuring` interface names `{}`, which each arm holds, but its arguments cannot be read in the state the arms join in. Fold the resource that owns the memory they read inside each arm and name that owner in `ensuring` instead",
                    crate::surface::validation::describe_resource_clause(resource),
                ))
            })?;
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
                    if pre_advance_facts.assumptions().proves_exact(&fact)
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

    for (assertion, written) in assertions.iter().zip(written_assertions) {
        if let ProofAssertion::Fact(surface_fact) = assertion {
            let ProofAssertion::Fact(written_fact) = written else {
                unreachable!("resolved interface assertion retains its written kind");
            };
            let fact = lower_fixed_state_proposition(
                    surface_fact,
                    &exported_pure_facts,
                    parameters,
                    arguments,
                    &old_reference,
                    &abstract_state,
                    None,
                    &execution.presentation.recorded_snapshots,
                    SpecDefinitions::new(predicate_environment, click_function_environment),
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not abstract `branch ensuring` fact: {message}"
                    ))
                })?;
            execution
                .presentation
                .surface_propositions
                .record_lowering(written_fact, &fact)?;
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
    // The abstraction issued identities from the execution's one counter, and
    // the joined execution continues from where it left it. Keeping the old
    // counter here is what would let the next loop head, opaque call or heap
    // allocation hand a live abstracted value's identity to something else.
    // The kernel owns the counter, so this moves it forward through the
    // kernel's checked forward-only setter rather than writing the field.
    execution
        .core
        .advance_kernel_variable_mark(join_kernel_variable_mark)
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `branch` join abstraction: {message}"
            ))
        })?;
    *available_pure_facts = ProofFacts::from_ordered(&exported_pure_facts);
    Ok(())
}

pub(super) fn append_execution_effect_facts(
    target: &mut ExecutionFacts,
    source: &(impl ExecutionFactSource + ?Sized),
) {
    let source = source.persistent_facts();
    let mut seen = BTreeSet::new();
    let accepted = source
        .iter()
        .enumerate()
        .filter_map(|(index, fact)| {
            // Keep kernel-certified transition facts as well as memory summaries,
            // without restating opaque call identities in surface certificates.
            ((is_memory_effect_proposition(fact.proposition()) || fact.is_certified())
                && !target.contains(fact)
                && seen.insert(fact))
            .then_some(index)
        })
        .collect::<Vec<_>>();
    target.extend_shared(&source.selected(&accepted));
}

pub(super) fn fact_transport_transition_facts(
    facts: &(impl ExecutionFactSource + ?Sized),
    source: &Proposition,
) -> ExecutionFacts {
    let source_memories = c_condition_fact_memories(source);
    let matching_effect = facts.fact_iter().position(|fact| {
        let before = match fact.proposition() {
            Proposition::CMemoryMutatesOnly { before, .. }
            | Proposition::CMemoryEffectSummary { before, .. }
            | Proposition::CHeapAllocationFreed { before, .. } => before,
            _ => return false,
        };
        source_memories.contains(before)
    });
    let Some(start) = matching_effect else {
        return facts.persistent_facts();
    };
    let end = facts
        .fact_iter()
        .skip(start + 1)
        .position(|fact| is_memory_effect_proposition(fact.proposition()))
        .map(|offset| start + 1 + offset)
        .unwrap_or(facts.len());
    facts
        .fact_iter()
        .skip(start)
        .take(end - start)
        .cloned()
        .collect()
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
                ResourceClause::Named { .. } => continue,
                ResourceClause::Quantified { .. } | ResourceClause::Conditional { .. } => continue,
                ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => {
                    ResourceClause::ViewMemory(segment)
                }
                ResourceClause::MemoryAggregate { .. } | ResourceClause::Iterated(_) => continue,
                ResourceClause::Declared {
                    kind,
                    name,
                    arguments,
                    parameter_types,
                    ..
                } => ResourceClause::Declared {
                    type_schema: None,
                    resource_type_arguments: Vec::new(),
                    resource_arguments: Vec::new(),
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
/// The pure facts a step refusal lists as its proof context.
///
/// A step run inside a proof context hands the kernel that context as its
/// assumptions and passes the fact slice only as the statement-local delta,
/// so listing the slice alone shows `pure facts: []` beside a `requires` the
/// step did see. List the context the kernel checked against.
fn listed_context_pure_facts(
    delta: &[Proposition],
    context: Option<&PureFactContext>,
) -> Vec<Proposition> {
    let Some(context) = context else {
        return delta.to_vec();
    };
    let mut facts = context.pure_facts();
    facts.extend_from_slice(delta);
    facts.sort();
    facts.dedup();
    facts
}

pub(super) fn execute_branch_step_from_frontier_position(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut PureFactList,
    tactic_name: &str,
    requested_branch: Option<bool>,
    prerequisite_policy: StatementPrerequisitePolicy,
    complete_empty_branch: bool,
    context: Option<&PureFactContext>,
) -> Result<bool, ClickError> {
    let function_block = proof_context.function_block;
    let function = proof_context.function;
    let parameters = proof_context.parsed_function.parameters();
    let arguments = proof_context.arguments;
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;

    let checked_call_events = execution.core.checked_call_events();
    let _checked_call_event_scope = CheckedCallEventScope::start(&checked_call_events);

    let state: &mut CState = &mut execution.core.state;

    let statement_index = execution.core.frontier.next_statement_index;
    let _site_scope = crate::surface::diagnostics::CStatementSiteScope::enter(
        &proof_context.constants.source_layout,
        statement_index,
        proof_context.parsed_function,
    );
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

    record_statement_program_snapshot_state(
        &mut execution.presentation.recorded_snapshots,
        function_block,
        statement_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    let current_resources = current_state.resources().facts().to_vec();
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    let condition_transitions = certified_condition_transitions(
        &current_state,
        available_pure_facts,
        &condition,
        &transition_label,
        prerequisite_policy,
        context,
    )?;
    if condition_transitions.len() != 1 {
        let expected = requested_branch.map_or("one exact truth value", |take_then| {
            if take_then { "true" } else { "false" }
        });
        // The path facts of an undecided C condition carry the whole memory
        // snapshot each load reads. Spelling them in the bounded source
        // vocabulary keeps the useful part -- which condition each arm
        // assumes -- without the repeated `CMemory` dump.
        let paths = condition_transitions
            .iter()
            .enumerate()
            .map(|(index, transition)| {
                format!(
                    "\n  condition path {index}: {}",
                    describe_pure_facts_for_diagnostic(
                        &transition.path_facts,
                        parameters,
                        arguments
                    )
                )
            })
            .collect::<String>();
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not prove that the next C `if` condition `{}` is {expected}; got {} feasible condition paths{paths}\n{}",
            describe_c_expression(&condition),
            condition_transitions.len(),
            describe_proof_context(
                &listed_context_pure_facts(available_pure_facts, context),
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
    {
        let _allocation_resolution = crate::instrumentation::OperationTiming::new(
            function.name(),
            claim_label,
            "branch allocation resolution",
        );
        // Condition certification selects pending allocation and pthread-create
        // outcomes. Retain that exact checked successor: recomputing from the
        // old state can lose the selected resources or their mutation ancestry.
        current_state = execution.core.reached_state().clone();
    }
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
    execution.core.state = current_state.into();
    // The selected arm is spliced before the `if`'s tail so the frontier's
    // own statement tree keeps every downstream statement reachable; the
    // patched source layout carries arm-final control successors, so no
    // continuation record is needed.
    if complete_empty_branch && matches!(selected_branch, CStatement::Skip) {
        // The empty arm completes this branch region immediately; the patched
        // layout supplies its control successor and statically completed
        // branch regions.
        let skip_index = execution.core.frontier.next_statement_index;
        let state = (*execution.core.state).clone();
        let state = execution
            .core
            .record_automatic_lifetime_end(
                &state,
                proof_context
                    .constants
                    .source_layout
                    .automatic_exits(skip_index, false),
            )
            .map_err(|error| {
                ClickError::new(format!(
                    "{}{}",
                    crate::surface::diagnostics::describe_runtime_error_over_locals(&error, &state),
                    crate::surface::diagnostics::describe_c_statement_site(),
                ))
                .with_kind(runtime_refusal_kind(&error))
            })?;
        execution.core.state = state.clone().into();
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
        &execution.core.state,
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
    available_pure_facts: &mut PureFactList,
    tactic_name: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    statement_index: usize,
    loop_index: usize,
    continuation_node: usize,
    execution_start_state: CState,
    current_state: CState,
    loop_statement: CStatement,
    remaining: Option<CStatement>,
    context: Option<&PureFactContext>,
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
        resource_specs,
        ranking_measures,
        structural_measure,
        do_while,
        body,
        ..
    } = loop_statement.clone()
    else {
        unreachable!("concrete loop stepping requires a while statement");
    };

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

    let loop_head = CStatement::While {
        condition: condition.clone(),
        invariant: invariant.clone(),
        invariant_checks: invariant_checks.clone(),
        effect_checks: effect_checks.clone(),
        resource_specs: resource_specs.clone(),
        ranking_measures: ranking_measures.clone(),
        structural_measure: structural_measure.clone(),
        do_while: false,
        backedge_target: None,
        natural_exit_target: None,
        body: body.clone(),
    };

    let state: &mut CState = &mut execution.core.state;
    execution.core.frontier.execution_start_state = Some(execution_start_state);
    *state = current_state.clone();

    // C's `do ... while` enters its body before evaluating the condition. The
    // continuation is an ordinary while head: after the first body, every
    // iteration checks the condition before re-entering the body.
    if do_while {
        // Entering the body records no evidence of its own. When the loop is
        // the first thing this trace executes, the proof object would start
        // matching evidence from the frontier position set below, which
        // holds the body alone, and would find no loop head left when the
        // condition is decided. A `Skip` theorem consumes nothing and makes
        // the proof object start from the source as it stands here, loop
        // included, so its own `do`-`while` rule performs the descent.
        if execution.core.evidence_state.is_none() {
            let transition_label =
                format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
            let mut next_opaque_call = execution.core.next_opaque_call;
            let mut next_kernel_variable = execution.core.kernel_variable_mark();
            let (transitions, _) = certified_statement_transitions(
                &current_state,
                available_pure_facts,
                &CStatement::Skip,
                proof_context.function_environment,
                Some(proof_context.spec_definitions.predicates),
                CExecutionSemantics::APPLY_VERIFIED_RULES,
                &transition_label,
                &mut next_opaque_call,
                &mut next_kernel_variable,
                StatementPrerequisitePolicy::Retained,
                StatementFactTransportPolicy::None,
                None,
            )?;
            let [transition] = transitions.as_slice() else {
                return Err(ClickError::new(format!(
                    "{transition_label} could not certify the entry of loop({loop_index})"
                )));
            };
            execution
                .core
                .record_statement_transition_with_loan_evidence(
                    function,
                    arguments,
                    transition.theorem.clone(),
                    transition.context.clone(),
                    &transition.execution_facts,
                    &transition.obligations,
                    &transition.loan_evidence,
                )
                .map_err(|refusal| {
                    ClickError::new(format!(
                        "{transition_label} recorded loop entry evidence the proof object rejected: {}",
                        describe_evidence_refusal(&refusal, parameters, arguments)
                    ))
                })?;
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
                exceptional: None,
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
        // A step decides the loop condition from the same whole proof
        // context it runs every other statement in.
        context,
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
                exceptional: None,
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

    let current_state = execution
        .core
        .record_automatic_lifetime_end(
            &current_state,
            proof_context
                .constants
                .source_layout
                .automatic_exits(statement_index, false),
        )
        .map_err(|error| {
            ClickError::new(format!(
                "{}{}",
                crate::surface::diagnostics::describe_runtime_error_over_locals(
                    &error,
                    &current_state
                ),
                crate::surface::diagnostics::describe_c_statement_site(),
            ))
            .with_kind(runtime_refusal_kind(&error))
        })?;
    execution.core.state = current_state.clone().into();
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
            let (execution_start_state, current_state) = if view.frontier.entry_member_prefix {
                (
                    view.frontier.execution_start_state.clone().ok_or_else(|| {
                        ClickError::new("checked entry member change lost its caller state")
                    })?,
                    state.clone(),
                )
            } else {
                let execution_start_state = state.clone();
                let current_state = c_function_entry_state(&execution_start_state, function, arguments)
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not bind function arguments"
                        ))
                    })?;
                (execution_start_state, current_state)
            };
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

/// Freeze a case selector at its checked frontier without retargeting explicit
/// snapshots or `old` expressions already carried by the selector.
pub(super) fn surface_frozen_at_snapshot<K: RecordedSnapshotKey + ?Sized>(
    surface: &ClickProposition,
    key: &K,
) -> Result<ClickProposition, ClickError> {
    annotate_surface_at_snapshot(surface, &key.to_selector(), SnapshotAnnotation::Freeze)
}

#[derive(Clone, Copy)]
enum SnapshotAnnotation {
    Freeze,
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
        ClickProposition::Initialized { .. }
            | ClickProposition::Loadable { .. }
            | ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
    ) {
        return Ok(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(surface.clone()),
        });
    }
    let expression_at_snapshot = |expression: &ContractExpression| match (annotation, expression) {
        (_, ContractExpression::Old(_))
        | (SnapshotAnnotation::Freeze, ContractExpression::At { .. }) => expression.clone(),
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
    // Construct one node outside the traversal frame. In debug builds these
    // by-value syntax temporaries are large; retaining them on every recursive
    // visit used tens of KiB per level inside an already nested proof planner.
    #[inline(never)]
    fn rebuild(
        proposition: &ClickProposition,
        expression_at_snapshot: &impl Fn(&ContractExpression) -> ContractExpression,
        selector: &SnapshotSelector,
        completed: &mut Vec<ClickProposition>,
    ) -> ClickProposition {
        let mut child = || Box::new(completed.pop().expect("visited snapshot child"));
        match proposition {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => ClickProposition::Comparison {
                left: expression_at_snapshot(left),
                operator: *operator,
                right: expression_at_snapshot(right),
            },
            ClickProposition::FloatClassification {
                expression,
                classification,
            } => ClickProposition::FloatClassification {
                expression: expression_at_snapshot(expression),
                classification: *classification,
            },
            ClickProposition::Defined { .. } => ClickProposition::At {
                selector: selector.clone(),
                proposition: Box::new(proposition.clone()),
            },
            ClickProposition::At { .. } => proposition.clone(),
            ClickProposition::And(_, _) => {
                let right = child();
                ClickProposition::And(child(), right)
            }
            ClickProposition::Or(_, _) => {
                let right = child();
                ClickProposition::Or(child(), right)
            }
            ClickProposition::Not(_) => ClickProposition::Not(child()),
            ClickProposition::Implies(_, _) => {
                let right = child();
                ClickProposition::Implies(child(), right)
            }
            ClickProposition::ForAll {
                click_type: c_type,
                name,
                ..
            } => ClickProposition::ForAll {
                click_type: c_type.clone(),
                name: name.clone(),
                written_name: proposition.written_quantifier_name().map(str::to_string),
                body: child(),
            },
            ClickProposition::Exists {
                click_type: c_type,
                name,
                ..
            } => ClickProposition::Exists {
                click_type: c_type.clone(),
                name: name.clone(),
                written_name: proposition.written_quantifier_name().map(str::to_string),
                body: child(),
            },
            ClickProposition::RangeAll {
                start, end, item, ..
            } => ClickProposition::RangeAll {
                start: expression_at_snapshot(start),
                end: expression_at_snapshot(end),
                item: item.clone(),
                written_item: proposition.written_quantifier_name().map(str::to_string),
                body: child(),
            },
            ClickProposition::RangeAny {
                start, end, item, ..
            } => ClickProposition::RangeAny {
                start: expression_at_snapshot(start),
                end: expression_at_snapshot(end),
                item: item.clone(),
                written_item: proposition.written_quantifier_name().map(str::to_string),
                body: child(),
            },
            ClickProposition::PredicateCall { name, arguments } => {
                ClickProposition::PredicateCall {
                    name: name.clone(),
                    arguments: arguments.iter().map(expression_at_snapshot).collect(),
                }
            }
            ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Initialized { .. }
            | ClickProposition::Loadable { .. } => proposition.clone(),
        }
    }
    // Postorder traversal stores references and completed output on the heap,
    // not large syntax values in one Rust call frame per logical connective.
    // Preserve left-to-right traversal, opaque `at` nodes, and the same bound.
    let mut pending = vec![(surface, 0, false)];
    let mut completed = Vec::new();
    while let Some((proposition, depth, visited)) = pending.pop() {
        if visited {
            let rebuilt = rebuild(
                proposition,
                &expression_at_snapshot,
                selector,
                &mut completed,
            );
            completed.push(rebuilt);
            continue;
        }
        crate::instrumentation::record_deterministic_work(1);
        if depth >= SNAPSHOT_ANNOTATION_DEPTH_LIMIT {
            return Err(ClickError::new(
                "Surface Click snapshot annotation exceeded its structural depth bound",
            ));
        }
        pending.push((proposition, depth, true));
        match proposition {
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                pending.push((right, depth + 1, false));
                pending.push((left, depth + 1, false));
            }
            ClickProposition::Not(body)
            | ClickProposition::ForAll { body, .. }
            | ClickProposition::Exists { body, .. }
            | ClickProposition::RangeAll { body, .. }
            | ClickProposition::RangeAny { body, .. } => {
                pending.push((body, depth + 1, false));
            }
            _ => {}
        }
    }
    debug_assert_eq!(completed.len(), 1);
    Ok(completed.pop().expect("visited snapshot root"))
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
        ClickProposition::FloatClassification { expression, .. } => expression_site(expression),
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
        | ClickProposition::Initialized { .. }
        | ClickProposition::Loadable { .. }
        | ClickProposition::Defined { .. } => None,
    }
}

/// Resume an entered `try`'s handler after a `Throw` outcome instead of
/// terminating the path. Pops continuations through the handler
/// continuation (abandoning the unwound region, as C++ unwinding does),
/// binds the payload, and positions the frontier at the handler entry.
/// Returns `Ok(true)` with the handler entered, or `Ok(false)` when no
/// handler continuation is present (existing termination behavior then
/// applies). Only entered `try` bodies push handler continuations, so C
/// execution always takes the `Ok(false)` path. The bundled binding
/// transitions are ordinary checked transitions recorded like any other;
/// they are not user-visible steps.
#[allow(clippy::too_many_arguments)]
pub(super) fn route_throw_to_handler(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut PureFactList,
    introduced_facts: &mut Vec<Proposition>,
    function: &CFunction,
    arguments: &[CExpression],
    parameters: &[syntax::C0Parameter],
    function_block: &FunctionBlock,
    function_environment: &CExecutionEnvironment,
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    fact_transport_policy: StatementFactTransportPolicy,
    context: Option<&PureFactContext>,
    throw_value: &CValue,
    thrown_state: &CState,
    throw_facts: &[Proposition],
) -> Result<bool, ClickError> {
    let handler = loop {
        match execution.core.frontier.continuations.pop() {
            Some(continuation) => {
                if let Some(exceptional) = continuation.exceptional {
                    break Some(exceptional);
                }
                // Non-handler continuations in the abandoned region are
                // discarded with it.
            }
            None => break None,
        }
    };
    let Some(handler) = handler else {
        return Ok(false);
    };
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    // Bind the payload exactly as the kernel's own `try` execution does:
    // declare the handler binding, then assign the thrown value. The
    // handler binding is always `int32` by `TryCatchInt32` semantics.
    let mut state = thrown_state.clone();
    let mut facts = PureFactList::from(throw_facts.to_vec());
    for statement in [
        c_declare(handler.binding.clone(), crate::kernel::CType::Int32),
        c_assign(
            handler.binding.clone(),
            CExpression::Value(throw_value.clone()),
        ),
    ] {
        let mut kernel_variable = execution.core.kernel_variable_mark();
        let (transitions, _) = certified_statement_transitions(
            &state,
            &facts,
            &statement,
            function_environment,
            Some(proof_context.spec_definitions.predicates),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &transition_label,
            &mut execution.core.next_opaque_call,
            &mut kernel_variable,
            prerequisite_policy,
            fact_transport_policy,
            context,
        )?;
        execution
            .core
            .advance_kernel_variable_mark(kernel_variable)
            .map_err(|message| ClickError::new(format!("{transition_label}: {message}")))?;
        let [transition] = transitions.try_into().map_err(|_| {
            ClickError::new(format!(
                "{transition_label}: handler binding transition did not complete"
            ))
        })?;
        let CStatementOutcome::Normal(next_state) = &transition.outcome else {
            return Err(ClickError::new(format!(
                "{transition_label}: handler binding transition did not complete normally"
            )));
        };
        let next_state = next_state.clone();
        execution.core.record_statement_transition(
            function,
            arguments,
            transition.theorem.clone(),
            transition.context.clone(),
            &transition.execution_facts,
            &transition.obligations,
        ).map_err(|refusal| {
            ClickError::new(format!(
                "{transition_label}: recorded handler binding evidence the proof object rejected: {}",
                describe_evidence_refusal(&refusal, parameters, arguments)
            ))
        })?;
        execution
            .presentation
            .record_generated_load_bindings(&transition.generated_load_bindings);
        append_execution_effect_facts(
            &mut execution.core.effect_facts,
            &transition.execution_facts,
        );
        facts = transition.pure_facts.clone();
        introduced_facts.extend(transition.introduced_facts.iter().cloned());
        state = *next_state;
    }
    *available_pure_facts = facts;
    execution.core.state = state.clone().into();
    let mut handler_source = handler.handler.clone();
    loop {
        let (head, tail) = split_next_source_operation(&handler_source).map_err(|message| {
            ClickError::new(format!(
                "{claim_label} tactic {tactic_index}: `{tactic_name}` failed to enter its exception handler: {message}"
            ))
        })?;
        if !matches!(head, CStatement::Skip) {
            break;
        }
        let Some(tail) = tail else {
            break;
        };
        handler_source = Arc::new(tail);
    }
    execution.core.frontier.position = FrontierPosition::StatementEntry {
        remaining: handler_source,
    };
    execution.core.frontier.next_statement_index = handler.handler_first_index;
    record_statement_program_snapshot_state(
        &mut execution.presentation.recorded_snapshots,
        function_block,
        handler.handler_first_index,
        ProgramPointKind::Entry,
        state,
    );
    Ok(true)
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
    available_pure_facts: &mut PureFactList,
    tactic_name: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    fact_transport_policy: StatementFactTransportPolicy,
    loop_step_policy: LoopStepPolicy,
) -> Result<Vec<Proposition>, ClickError> {
    execute_step_from_frontier_position_selecting_path(
        execution,
        proof_context,
        available_pure_facts,
        tactic_name,
        prerequisite_policy,
        fact_transport_policy,
        loop_step_policy,
        None,
        None,
        None,
    )
}

pub(super) struct ExecutionPointStepSuccessor {
    pub(super) execution: ExecutionProofState,
    pub(super) pure_facts: PureFactList,
    pub(super) introduced_facts: Vec<Proposition>,
}

/// The checked frontier and the two direct outcomes of a call whose throw
/// edge is caught by an active transparent `try` continuation.  This is a
/// preparation result only: the proof-object layer owns publishing the two
/// descendants and joining their certificates.
pub(super) struct PreparedCallOutcomeSplit {
    pub(super) execution: ExecutionProofState,
    pub(super) execution_start_state: CState,
    pub(super) current_state: CState,
    pub(super) statement_index: usize,
    pub(super) statement: CStatement,
    pub(super) source_frontier_position: FrontierPosition,
    pub(super) source_frontier_index: usize,
    pub(super) continuation_index: usize,
    pub(super) continuation_remaining: Option<CStatement>,
    pub(super) next_opaque_call: u64,
    pub(super) next_kernel_variable: u64,
    pub(super) transitions: Vec<crate::surface::CertifiedStatementTransition>,
}

/// Descend through transparent try/catch syntax when necessary, then certify
/// the direct call at its frontier without mutating the caller's proof state.
/// It also accepts a frontier that `step()` has already entered, provided the
/// active exceptional continuation is still present. Ordinary `step()` still
/// uses the one-successor path below; this helper exists only for the explicit
/// proof-object outcome split.
#[allow(clippy::too_many_arguments)]
pub(super) fn prepare_call_outcome_split(
    execution: &ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &PureFactList,
    tactic_name: &str,
) -> Result<Option<PreparedCallOutcomeSplit>, ClickError> {
    let mut prepared = execution.clone();
    let function = proof_context.function;
    let arguments = proof_context.arguments;
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;
    let mut statement_index = prepared.core.frontier.next_statement_index;
    let source_frontier_position = prepared.core.frontier.position.clone();
    let source_frontier_index = statement_index;
    let mut source_region = proof_context
        .constants
        .source_layout
        .statement(statement_index)
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve source statement({statement_index})"
            ))
        })?;
    let (execution_start_state, current_state, mut statement, mut remaining) =
        next_top_level_statement_from_frontier_position(
            prepared.view(proof_context),
            &prepared.core.state,
            function,
            arguments,
            claim_label,
            tactic_index,
            tactic_name,
        )?;

    while let CStatement::TryCatchInt32 {
        try_body,
        binding,
        handler,
        cleanup_unwind,
    } = &statement
    {
        let SourceStatementKind::Try {
            try_statement_index,
            handler_statement_index,
            after_try_statement_index,
            ..
        } = source_region.kind
        else {
            break;
        };
        prepared
            .core
            .frontier
            .continuations
            .push(ProofExecutionContinuation {
                remaining: remaining.map(Arc::new),
                next_statement_index: after_try_statement_index,
                loop_exit_statement_index: after_try_statement_index,
                exceptional: Some(ExceptionalContinuation {
                    binding: binding.clone(),
                    handler: Arc::new((**handler).clone()),
                    handler_first_index: handler_statement_index,
                    cleanup_unwind: *cleanup_unwind,
                }),
            });
        remaining = Some((**try_body).clone());
        statement_index = try_statement_index;
        source_region = proof_context
            .constants
            .source_layout
            .statement(statement_index)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve source statement({statement_index})"
                ))
            })?;
        (statement, remaining) = split_next_source_operation(
            remaining
                .as_ref()
                .expect("try descent installed a try-body source"),
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` failed: {message}"
            ))
        })?;
    }
    if !matches!(
        statement,
        CStatement::Call { .. } | CStatement::CallAssign { .. }
    ) {
        return Ok(None);
    }
    // Without an active handler the throw leaves the function: the threw arm
    // ends at function exit with that throw outcome, while the returned arm
    // continues with the rest of the function.
    // The preparation may have started at `FunctionEntry`. Re-present the
    // exact call source as a normal statement frontier for the arm's cursor;
    // the original container is retained separately for evidence matching.
    prepared.core.frontier.next_statement_index = statement_index;
    prepared.core.frontier.execution_start_state = Some(execution_start_state.clone());
    prepared.core.frontier.position = FrontierPosition::StatementEntry {
        remaining: match remaining.clone() {
            Some(tail) => Arc::new(CStatement::Seq(Arc::new(statement.clone()), Arc::new(tail))),
            None => Arc::new(statement.clone()),
        },
    };
    prepared.core.state = current_state.clone().into();
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    let mut next_opaque_call = prepared.core.next_opaque_call;
    let mut next_kernel_variable = prepared.core.kernel_variable_mark();
    let (transitions, _) = certified_statement_transitions(
        &current_state,
        available_pure_facts,
        &statement,
        proof_context.function_environment,
        Some(proof_context.spec_definitions.predicates),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &transition_label,
        &mut next_opaque_call,
        &mut next_kernel_variable,
        StatementPrerequisitePolicy::Retained,
        StatementFactTransportPolicy::None,
        None,
    )?;
    let normal = transitions
        .iter()
        .filter(|transition| matches!(transition.outcome, CStatementOutcome::Normal(_)))
        .count();
    let thrown = transitions
        .iter()
        .filter(|transition| matches!(transition.outcome, CStatementOutcome::Throw { .. }))
        .count();
    if normal != 1 || thrown != 1 || transitions.len() != 2 {
        return Ok(None);
    }
    Ok(Some(PreparedCallOutcomeSplit {
        execution: prepared,
        execution_start_state,
        current_state,
        statement_index,
        statement,
        source_frontier_position,
        source_frontier_index,
        continuation_index: source_region.continuation_node,
        continuation_remaining: remaining,
        next_opaque_call,
        next_kernel_variable,
        transitions,
    }))
}

/// Record one of the two transitions retained by
/// [`prepare_call_outcome_split`].  This is intentionally a recorder, not an
/// evaluator: the theorem, outcome, facts, and loan evidence all come from
/// the one checked transition list produced during preparation.
#[allow(clippy::too_many_arguments)]
pub(super) fn apply_prepared_call_outcome_transition(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available_pure_facts: &mut PureFactList,
    introduced_facts: &mut Vec<Proposition>,
    prepared: &PreparedCallOutcomeSplit,
    transition: &crate::surface::CertifiedStatementTransition,
) -> Result<(), ClickError> {
    let function_block = proof_context.function_block;
    let function = proof_context.function;
    let parameters = proof_context.parsed_function.parameters();
    let arguments = proof_context.arguments;
    let function_environment = proof_context.function_environment;
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `outcomes`");

    // Record the selected theorem against the original try wrapper. Matching
    // it against the synthetic call-only cursor would bypass the kernel's
    // validated try descent and leave the next source undefined.
    execution.core.frontier.position = prepared.source_frontier_position.clone();
    execution.core.frontier.next_statement_index = prepared.source_frontier_index;
    execution.core.next_opaque_call = prepared.next_opaque_call;
    execution
        .core
        .advance_kernel_variable_mark(prepared.next_kernel_variable)
        .map_err(|message| ClickError::new(format!("{transition_label}: {message}")))?;
    record_statement_program_snapshot_state(
        &mut execution.presentation.recorded_snapshots,
        function_block,
        prepared.statement_index,
        ProgramPointKind::Entry,
        prepared.current_state.clone(),
    );
    execution
        .presentation
        .record_generated_load_bindings(&transition.generated_load_bindings);
    execution
        .presentation
        .record_generated_load_source_events(&transition.generated_load_source_events);
    execution
        .core
        .record_statement_transition_with_loan_evidence(
            function,
            arguments,
            transition.theorem.clone(),
            transition.context.clone(),
            &transition.execution_facts,
            &transition.obligations,
            &transition.loan_evidence,
        )
        .map_err(|refusal| {
            ClickError::new(format!(
                "{transition_label}: recorded call outcome evidence the proof object rejected: {}",
                describe_evidence_refusal(&refusal, parameters, arguments)
            ))
        })?;
    append_execution_effect_facts(
        &mut execution.core.effect_facts,
        &transition.execution_facts,
    );
    introduced_facts.extend(transition.introduced_facts.iter().cloned());

    let (next_state, is_throw) = match &transition.outcome {
        CStatementOutcome::Normal(state) => (state.clone(), false),
        CStatementOutcome::Throw { state, .. } => (state.clone(), true),
        _ => {
            return Err(ClickError::new(
                "`outcomes` received a non-returned/non-thrown call transition",
            ));
        }
    };
    record_statement_program_snapshot_state(
        &mut execution.presentation.recorded_snapshots,
        function_block,
        prepared.statement_index,
        ProgramPointKind::Exit,
        *next_state.clone(),
    );

    if is_throw {
        let CStatementOutcome::Throw { value, state } = &transition.outcome else {
            unreachable!("the outcome was checked as a throw");
        };
        if !route_throw_to_handler(
            execution,
            proof_context,
            available_pure_facts,
            introduced_facts,
            function,
            arguments,
            parameters,
            function_block,
            function_environment,
            claim_label,
            tactic_index,
            "outcomes",
            StatementPrerequisitePolicy::Retained,
            StatementFactTransportPolicy::None,
            None,
            value,
            state,
            &transition.pure_facts,
        )? {
            // No handler: the throw is this path's function outcome.
            record_completed_continuation_exits(&mut execution.core.frontier);
            let return_assumptions = transition.pure_facts.context();
            let case_outcomes =
                crate::kernel::c_function_outcomes_from_statement_outcome_with_resource_cases(
                    &prepared.execution_start_state,
                    function,
                    arguments,
                    transition.outcome.clone(),
                    transition.obligations.clone(),
                    &return_assumptions,
                );
            let mut completed_outcomes = Vec::new();
            for (outcome, obligations, case_facts) in case_outcomes {
                let mut completed_execution_facts = execution
                    .core
                    .completed_path_facts(&transition.execution_facts);
                append_execution_effect_facts(
                    &mut completed_execution_facts,
                    &execution.core.effect_facts,
                );
                for fact in case_facts {
                    completed_execution_facts.push(ExecutionPureFact::new(fact));
                }
                completed_outcomes.push((
                    outcome,
                    completed_execution_facts,
                    obligations,
                    execution.core.loan_evidence().clone(),
                ));
            }
            append_pending_loop_returns(&mut execution.core, &mut completed_outcomes);
            *available_pure_facts = transition.pure_facts.clone();
            let completed =
                crate::kernel::c_function_execution_candidates_from_outcomes_with_loan_evidence(
                    prepared.execution_start_state.clone(),
                    function.clone(),
                    arguments.to_vec(),
                    completed_outcomes,
                );
            set_function_exit_execution(
                &mut execution.core.frontier,
                claim_label,
                tactic_index,
                "outcomes",
                prepared.execution_start_state.clone(),
                completed,
            )?;
            execution.core.frontier.next_statement_index = prepared.continuation_index;
            execution.core.state = prepared.execution_start_state.clone().into();
        }
        return Ok(());
    }

    *available_pure_facts = transition.pure_facts.clone();
    execution.core.frontier.execution_start_state = Some(prepared.execution_start_state.clone());
    execution.core.state = (*next_state.clone()).into();
    let remaining = if let Some(remaining) = prepared.continuation_remaining.clone() {
        execution.core.frontier.next_statement_index = prepared.continuation_index;
        Some(remaining)
    } else {
        resume_after_completed_region(&mut execution.core.frontier)
    };
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
                *next_state,
            );
        }
        None if finish_exhausted_region(&mut execution.core.frontier) => {}
        None => {
            return Err(ClickError::new(
                "`outcomes` returned from a call without a following source statement",
            ));
        }
    }
    Ok(())
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
    available_pure_facts: &PureFactList,
    tactic_name: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    fact_transport_policy: StatementFactTransportPolicy,
    loop_step_policy: LoopStepPolicy,
    context: Option<&PureFactContext>,
) -> Result<ExecutionPointStepSuccessor, ClickError> {
    let mut successor = execution.clone();
    let mut successor_facts = available_pure_facts.clone();
    let introduced_facts = execute_step_from_frontier_position_selecting_path(
        &mut successor,
        proof_context,
        &mut successor_facts,
        tactic_name,
        prerequisite_policy,
        fact_transport_policy,
        loop_step_policy,
        None,
        context,
        None,
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
    available_pure_facts: &mut PureFactList,
    tactic_name: &str,
    prerequisite_policy: StatementPrerequisitePolicy,
    fact_transport_policy: StatementFactTransportPolicy,
    loop_step_policy: LoopStepPolicy,
    selected_path_fact: Option<&Proposition>,
    context: Option<&PureFactContext>,
    path_cases: Option<&mut Vec<CertifiedStatementTransition>>,
) -> Result<Vec<Proposition>, ClickError> {
    let function_block = proof_context.function_block;
    let function = proof_context.function;
    let parameters = proof_context.parsed_function.parameters();
    let arguments = proof_context.arguments;
    let function_environment = proof_context.function_environment;
    let claim_label = proof_context.claim_label;
    let tactic_index = proof_context.tactic_index;

    let checked_call_events = execution.core.checked_call_events();
    let _checked_call_event_scope = CheckedCallEventScope::start(&checked_call_events);

    let state: &mut CState = &mut execution.core.state;

    let mut statement_index = execution.core.frontier.next_statement_index;
    let _site_scope = crate::surface::diagnostics::CStatementSiteScope::enter(
        &proof_context.constants.source_layout,
        statement_index,
        proof_context.parsed_function,
    );
    let mut source_region = proof_context.constants.source_layout.statement(statement_index).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve source statement({statement_index})"
        ))
    })?;
    if function_environment.selected_call_contract.is_some()
        && !matches!(source_region.kind, SourceStatementKind::Plain)
    {
        return Err(ClickError::new(
            "step(Contract) requires a call at the current frontier",
        ));
    }
    if let Some(transport) = &function_environment.selected_call_binders
        && !matches!(source_region.kind, SourceStatementKind::Plain)
    {
        return Err(ClickError::new(format!(
            "`step({}(...), {{ ... }})` requires a call to `{}` at the current frontier",
            transport.function, transport.function
        )));
    }
    if matches!(source_region.kind, SourceStatementKind::If { .. }) {
        let entered = execute_branch_step_from_frontier_position(
            execution,
            proof_context,
            available_pure_facts,
            "step",
            None,
            prerequisite_policy,
            false,
            context,
        )?;
        debug_assert!(entered);
        return Ok(Vec::new());
    }
    let loop_index = match source_region.kind {
        SourceStatementKind::Loop { loop_index } => Some(loop_index),
        SourceStatementKind::Plain
        | SourceStatementKind::If { .. }
        | SourceStatementKind::Try { .. } => None,
    };
    let (execution_start_state, current_state, mut source_statement, mut remaining) =
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
    if function_block.one_call_proof
        && matches!(
            execution.core.frontier.position,
            FrontierPosition::FunctionEntry
        )
    {
        source_statement = function.body().clone();
        remaining = None;
    }
    // Descend into `try` bodies transparently so an implicit cleanup call
    // inside one is its own steppable statement. Only the typed C++ frontend
    // produces `TryCatchInt32` (and only it gets the `Try` layout kind), so
    // C stepping never takes this branch. The handler continuation lets a
    // later `Throw` resume at the handler entry instead of terminating the
    // path; normal completion pops it with the tail like any other
    // continuation.
    let mut descended_try = false;
    while let CStatement::TryCatchInt32 {
        try_body,
        binding,
        handler,
        cleanup_unwind,
    } = &source_statement
    {
        let (try_first, handler_first, after_try) = match source_region.kind {
            SourceStatementKind::Try {
                try_statement_index,
                handler_statement_index,
                after_try_statement_index,
                ..
            } => (
                try_statement_index,
                handler_statement_index,
                after_try_statement_index,
            ),
            _ => break,
        };
        descended_try = true;
        execution
            .core
            .frontier
            .continuations
            .push(ProofExecutionContinuation {
                remaining: remaining.map(Arc::new),
                next_statement_index: after_try,
                loop_exit_statement_index: after_try,
                exceptional: Some(ExceptionalContinuation {
                    binding: binding.clone(),
                    handler: Arc::new((**handler).clone()),
                    handler_first_index: handler_first,
                    cleanup_unwind: *cleanup_unwind,
                }),
            });
        remaining = Some((**try_body).clone());
        statement_index = try_first;
        source_region = proof_context
            .constants
            .source_layout
            .statement(statement_index)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve source statement({statement_index})"
                ))
            })?;
        (source_statement, remaining) = split_next_source_operation(
            remaining
                .as_ref()
                .expect("try-body descent just set a remaining statement"),
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` failed: {message}"
            ))
        })?;
    }
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
            context,
        )?;
        return Ok(Vec::new());
    }
    let mut step_statement = source_statement;
    if function_environment.selected_call_contract.is_some()
        && !statement_contains_call(&step_statement)
    {
        return Err(ClickError::new(
            "step(Contract) requires a call at the current frontier",
        ));
    }
    // The step names the call it binds, so the statement the frontier is about
    // to run has to be that call: one comparison against the statement, not a
    // search for a matching call.
    if let Some(transport) = &function_environment.selected_call_binders {
        let called = match &step_statement {
            CStatement::Call {
                function_name,
                arguments,
            }
            | CStatement::CallAssign {
                function_name,
                arguments,
                ..
            } => Some((function_name.as_str(), arguments.len())),
            _ => None,
        };
        match called {
            Some((name, arity)) if transport.names_call_to(name) => {
                if arity != transport.arity {
                    return Err(ClickError::new(format!(
                        "`{name}` is called with {arity} argument(s) here, but the step writes {}",
                        transport.arity
                    )));
                }
            }
            _ => {
                return Err(ClickError::new(format!(
                    "`step({}(...), {{ ... }})` requires a call to `{}` at the current frontier; next operation: {}",
                    transport.function,
                    transport.function,
                    describe_statement_head(&step_statement)
                )));
            }
        }
    }

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
    let current_resources = current_state.resources().facts().to_vec();
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    let next_opaque_call_before_step = execution.core.next_opaque_call;
    let next_kernel_variable_before_step = execution.core.kernel_variable_mark();
    // The kernel owns the counter: the step reads a copy, the evaluation
    // advances it, and the checked setter installs the result.
    let mut stepped_kernel_variable = next_kernel_variable_before_step;
    let mut transitions = certified_statement_transitions(
        &current_state,
        available_pure_facts,
        &step_statement,
        function_environment,
        Some(proof_context.spec_definitions.predicates),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &transition_label,
        &mut execution.core.next_opaque_call,
        &mut stepped_kernel_variable,
        prerequisite_policy,
        fact_transport_policy,
        context,
    )?
    .0;
    execution
        .core
        .advance_kernel_variable_mark(stepped_kernel_variable)
        .map_err(|message| ClickError::new(format!("{transition_label}: {message}")))?;
    if let Some(selected_path_fact) = selected_path_fact {
        transitions.retain(|transition| transition.path_facts.contains(selected_path_fact));
    }
    let mut call_outcome_edges = None;
    // A direct call can have one continuing normal outcome and one terminal
    // throw. An int32 try/catch can similarly have one continuing normal
    // outcome and one terminal handler return. If the only continuation is a
    // return, prove that exact two-node source suffix as one checked statement
    // theorem family. Keep this constant-size: a step must not scan or
    // execute an unrelated remainder of the function to discover a join.
    if selected_path_fact.is_none()
        && matches!(
            step_statement,
            CStatement::Call { .. }
                | CStatement::CallAssign { .. }
                | CStatement::TryCatchInt32 { .. }
        )
        && matches!(
            execution.core.frontier.region,
            ExecutionRegionKind::Function
        )
        && execution.core.frontier.continuations.is_empty()
        && transitions.len() == 2
        && transitions
            .iter()
            .filter(|transition| matches!(transition.outcome, CStatementOutcome::Normal(_)))
            .count()
            == 1
        && transitions.iter().any(|transition| {
            matches!(
                (&step_statement, &transition.outcome),
                (
                    CStatement::Call { .. } | CStatement::CallAssign { .. },
                    CStatementOutcome::Throw { .. }
                ) | (
                    CStatement::TryCatchInt32 { .. },
                    CStatementOutcome::Return { .. }
                )
            )
        })
        && let Some(tail @ CStatement::Return(_)) = remaining.as_ref()
    {
        let whole_suffix = c_seq(step_statement.clone(), tail.clone());
        let mut next_opaque_call = next_opaque_call_before_step;
        let mut next_kernel_variable = next_kernel_variable_before_step;
        let (suffix_transitions, _) = certified_statement_transitions(
            &current_state,
            available_pure_facts,
            &whole_suffix,
            function_environment,
            Some(proof_context.spec_definitions.predicates),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &transition_label,
            &mut next_opaque_call,
            &mut next_kernel_variable,
            prerequisite_policy,
            fact_transport_policy,
            context,
        )?;
        if suffix_transitions.len() == 2
            && suffix_transitions.iter().all(|transition| {
                matches!(
                    (&step_statement, &transition.outcome),
                    (
                        CStatement::Call { .. } | CStatement::CallAssign { .. },
                        CStatementOutcome::Return { .. } | CStatementOutcome::Throw { .. }
                    ) | (
                        CStatement::TryCatchInt32 { .. },
                        CStatementOutcome::Return { .. }
                    )
                )
            })
            && (matches!(step_statement, CStatement::TryCatchInt32 { .. })
                || suffix_transitions
                    .iter()
                    .filter(|transition| {
                        matches!(transition.outcome, CStatementOutcome::Throw { .. })
                    })
                    .count()
                    == 1)
        {
            if let CStatement::TryCatchInt32 {
                try_body, handler, ..
            } = &step_statement
                && matches!(
                    try_body.as_ref(),
                    CStatement::Call { .. } | CStatement::CallAssign { .. }
                )
                && matches!(handler.as_ref(), CStatement::Return(_))
            {
                let edges = transitions
                    .iter()
                    .map(|transition| match transition.outcome {
                        CStatementOutcome::Normal(_) => Some(true),
                        CStatementOutcome::Return { .. } => Some(false),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>();
                // The kernel's Seq evaluator emits each first-statement path
                // in order, replacing only its continuing path with the tail's
                // descendants. With one descendant per edge, this order is
                // unchanged in `suffix_transitions`.
                call_outcome_edges = edges.filter(|edges| {
                    edges.len() == 2 && edges.iter().filter(|returned| **returned).count() == 1
                });
            } else if matches!(
                step_statement,
                CStatement::Call { .. } | CStatement::CallAssign { .. }
            ) {
                // A direct call's continuing normal edge is its returned
                // outcome and its terminal throw is the threw outcome, in the
                // kernel's first-statement path order, as for try/catch above.
                let edges = transitions
                    .iter()
                    .map(|transition| match transition.outcome {
                        CStatementOutcome::Normal(_) => Some(true),
                        CStatementOutcome::Throw { .. } => Some(false),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>();
                call_outcome_edges = edges.filter(|edges| {
                    edges.len() == 2 && edges.iter().filter(|returned| **returned).count() == 1
                });
            }
            step_statement = whole_suffix;
            transitions = suffix_transitions;
            execution.core.next_opaque_call = next_opaque_call;
            // The suffix evaluation re-ran the step from the counter it had
            // before, so this is not below what the step above installed only
            // when the suffix allocated at least as much. Take the higher of
            // the two: the counter never moves back.
            execution
                .core
                .advance_kernel_variable_mark(
                    next_kernel_variable.max(execution.core.kernel_variable_mark()),
                )
                .map_err(|message| ClickError::new(format!("{transition_label}: {message}")))?;
        }
    }
    // A summarized loop whose body may `return` has one continuing successor,
    // the join of its guard-false and `break` exits or its natural forward
    // jump, and one terminal
    // successor per returned path. The step follows the continuing one; each
    // returned path is retained as an already-completed path of this
    // execution and joins the function's exit paths at the boundary, where
    // its postcondition and resource obligations are checked on the value
    // and state it returned. A loop whose every successor returns completes
    // the frontier below like any other terminal operation.
    if matches!(loop_step_policy, LoopStepPolicy::ApplyVerifiedRule)
        && let Some(planned) =
            loop_index.and_then(|index| execution.presentation.loop_return_proofs.get(&index))
        && transitions
            .iter()
            .filter(|transition| matches!(transition.outcome, CStatementOutcome::Return { .. }))
            .count()
            != planned.paths.len()
    {
        return Err(ClickError::new(
            "checked loop return outcomes do not align with their preservation proofs",
        ));
    }
    let mut loop_return_transitions = Vec::new();
    if matches!(loop_step_policy, LoopStepPolicy::ApplyVerifiedRule)
        && transitions.len() > 1
        && transitions
            .iter()
            .filter(|transition| {
                matches!(
                    transition.outcome,
                    CStatementOutcome::Normal(_) | CStatementOutcome::Jump { .. }
                )
            })
            .count()
            == 1
        && transitions.iter().all(|transition| {
            matches!(
                transition.outcome,
                CStatementOutcome::Normal(_)
                    | CStatementOutcome::Jump { .. }
                    | CStatementOutcome::Return { .. }
            )
        })
    {
        let (returned, continuing): (Vec<_>, Vec<_>) = transitions
            .into_iter()
            .partition(|transition| matches!(transition.outcome, CStatementOutcome::Return { .. }));
        transitions = continuing;
        loop_return_transitions = returned;
    }
    if transitions.len() > 1
        && transitions.iter().all(|transition| {
            matches!(
                transition.outcome,
                CStatementOutcome::Return { .. } | CStatementOutcome::Throw { .. }
            )
        })
    {
        // One checked source operation can have several completed outcomes,
        // including a terminal direct call followed by a return.
        // Preserve every theorem and its own outcome for final certification.

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
                            &transition.execution_facts,
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
        let generated_load_source_events = transitions
            .iter()
            .flat_map(|transition| transition.generated_load_source_events.iter())
            .cloned()
            .collect::<Vec<_>>();
        for transition in &transitions {
            execution
                .presentation
                .record_generated_load_bindings(&transition.generated_load_bindings);
        }
        // A loop whose every successor returns leaves no continuing state
        // to record its exit at; one returned state binds the iteration
        // identities every returned path's facts are stated over.
        let loop_return_exit_state = loop_index.and_then(|_| {
            transitions
                .iter()
                .find_map(|transition| match &transition.outcome {
                    CStatementOutcome::Return { state, .. } => Some((**state).clone()),
                    _ => None,
                })
        });
        let mut completed_outcomes = Vec::new();
        for transition in transitions {
            let return_assumptions = transition.pure_facts.context();
            let case_outcomes =
                crate::kernel::c_function_outcomes_from_statement_outcome_with_resource_cases(
                    &execution_start_state,
                    function,
                    arguments,
                    transition.outcome.clone(),
                    transition.obligations.clone(),
                    &return_assumptions,
                );
            for (outcome, obligations, case_facts) in case_outcomes {
                let mut completed_execution_facts = execution
                    .core
                    .completed_path_facts(&transition.execution_facts);
                append_execution_effect_facts(
                    &mut completed_execution_facts,
                    &execution.core.effect_facts,
                );
                for fact in case_facts {
                    completed_execution_facts.push(ExecutionPureFact::new(fact));
                }
                completed_outcomes.push((
                    outcome,
                    completed_execution_facts,
                    obligations,
                    crate::kernel::concat_checked_loan_evidence(
                        execution.core.loan_evidence(),
                        &transition.loan_evidence,
                    ),
                ));
            }
        }
        append_pending_loop_returns(&mut execution.core, &mut completed_outcomes);
        let state: &mut CState = &mut execution.core.state;
        let completed =
            crate::kernel::c_function_execution_candidates_from_outcomes_with_loan_evidence(
                execution_start_state.clone(),
                function.clone(),
                arguments.to_vec(),
                completed_outcomes,
            );
        execution.presentation.call_outcome_edges = call_outcome_edges;
        if let (Some(loop_index), Some(exit_state)) = (loop_index, loop_return_exit_state) {
            record_loop_program_snapshot_state(
                &mut execution.presentation.recorded_snapshots,
                function_block,
                loop_index,
                ProgramPointKind::Exit,
                exit_state,
            );
            execution.presentation.surface_record.last_step_entry = Some(ProgramPointRef {
                region: CodeRegionRef::Loop(loop_index),
                kind: ProgramPointKind::Exit,
            });
        }
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
        execution
            .presentation
            .record_generated_load_source_events(&generated_load_source_events);
        return Ok(common_introduced_facts);
    }
    if selected_path_fact.is_none()
        && matches!(
            step_statement,
            CStatement::Call { .. } | CStatement::CallAssign { .. }
        )
        && matches!(
            execution.core.frontier.region,
            ExecutionRegionKind::Function
        )
        && execution.core.frontier.continuations.is_empty()
        && transitions.len() == 2
        && transitions
            .iter()
            .filter(|transition| matches!(transition.outcome, CStatementOutcome::Normal(_)))
            .count()
            == 1
        && transitions
            .iter()
            .filter(|transition| matches!(transition.outcome, CStatementOutcome::Throw { .. }))
            .count()
            == 1
    {
        // A maybe-throwing call has two successors, like an undecided C
        // `if`: each is its own proof arm, so one linear step cannot take
        // both.
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached `{}`, which may throw; its returned and threw successors are separate proof arms. Write `outcomes {{ returned => {{ step(); ... }} threw => {{ step(); ... }} }}` here, or let `execute()` split it",
            describe_statement_head(&step_statement)
        )));
    }
    // A statement whose checked successors differ only in their path facts
    // -- a load that may or may not read the cell an earlier store wrote --
    // is one C operation with several cases. A step never publishes those
    // cases as hidden siblings; a planner that asks for them receives them
    // unchanged and splits the proof on their conditions. Nothing has been
    // committed yet, so the caller runs the statement again from this
    // frontier on each side of that split.
    if transitions.len() > 1
        && !descended_try
        && let Some(path_cases) = path_cases
        && statement_successors_are_path_cases(&transitions)
    {
        execution.core.next_opaque_call = next_opaque_call_before_step;
        *path_cases = transitions;
        return Ok(Vec::new());
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
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` is missing exact prerequisite needed to select the safe statement transition: `{}`",
                    crate::surface::diagnostics::describe_stated_fact_over_locals(
                        required,
                        &current_state
                    )
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
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced {}{}\n{}",
                describe_function_outcome(&outcome, parameters, arguments),
                crate::surface::diagnostics::describe_c_statement_site(),
                describe_proof_context(
                    &listed_context_pure_facts(available_pure_facts, context),
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
            let kind = runtime_refusal_kind(error);
            let unsupported = kind == crate::surface::ClickErrorKind::Internal;
            let description = if unsupported {
                "reached an unsupported modeled operation"
            } else {
                "could not verify C operation"
            };
            let detail = format!(
                "{}{}",
                describe_runtime_error(error, parameters, arguments),
                describe_missing_range_end_note(error, &current_resources, parameters, arguments)
            );
            if matches!(
                error,
                crate::kernel::CRuntimeError::UninitializedMutex { .. }
                    | crate::kernel::CRuntimeError::UnsupportedConcurrentMutex
            ) {
                return Err(ClickError::new(detail).with_kind(kind));
            }
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` {description}: {}\n  C operation: {}{}{}\n{}",
                detail,
                describe_statement_head(&step_statement),
                describe_call_bindings(&step_statement, function_environment),
                crate::surface::diagnostics::describe_c_statement_site(),
                describe_proof_context(
                    &listed_context_pure_facts(available_pure_facts, context),
                    &current_resources,
                    parameters,
                    arguments,
                    &[]
                )
            ))
            .with_kind(kind));
        }
        let path_case_split = statement_successors_are_path_cases(&transitions);
        let split_condition = if path_case_split {
            let cases = transitions
                .iter()
                .map(PathCase::of_statement)
                .collect::<Vec<_>>();
            path_case_split_condition(
                &cases,
                &|fact| available_pure_facts.contains(fact),
                &current_state,
                proof_context,
            )
            .map(|(_, condition)| condition)
        } else {
            None
        };
        let case_split_guidance = if path_case_split {
            describe_path_case_split_guidance(split_condition.as_ref(), transitions.len())
        } else {
            String::new()
        };
        let error = ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires exactly one statement successor for `{}`, got {}{}\n{}{}{}{}",
            describe_c_statement_head(&step_statement),
            transitions.len(),
            crate::surface::diagnostics::describe_c_statement_site(),
            describe_undecided_statement_successors(&transitions, parameters, arguments),
            case_split_guidance,
            describe_multiple_statement_successors_guidance(
                &step_statement,
                transitions.len(),
                transitions
                    .iter()
                    .filter(|transition| {
                        matches!(transition.outcome, CStatementOutcome::Throw { .. })
                    })
                    .count()
                    == 1,
            ),
            describe_proof_context(
                &listed_context_pure_facts(available_pure_facts, context),
                &current_resources,
                parameters,
                arguments,
                &[]
            )
        ));
        return Err(match (path_case_split, split_condition) {
            (true, Some(condition)) => error.with_path_case_condition(condition),
            (true, None) => error.with_path_case_split(),
            (false, _) => error,
        });
    }
    let transition = transitions
        .into_iter()
        .next()
        .expect("one statement transition was required");
    execution
        .presentation
        .record_generated_load_bindings(&transition.generated_load_bindings);
    let generated_load_source_events = transition.generated_load_source_events.clone();
    let mut introduced_facts = transition.introduced_facts.clone();
    // The returned paths fork from the trace as it is before the loop's
    // continuing theorem is recorded on it.
    let loop_return_parent = (!loop_return_transitions.is_empty()).then(|| execution.core.clone());
    if matches!(loop_step_policy, LoopStepPolicy::ApplyVerifiedRule)
        && let Some(loop_index) = loop_index
        && matches!(transition.outcome, CStatementOutcome::Normal(_))
        && let Some(loop_clause) = function_block
            .structural_clauses()
            .iter()
            .find(|clause| clause.region() == &CodeRegion::Loop(loop_index))
    {
        record_loop_exit_invariants(
            &mut execution.presentation.surface_propositions,
            loop_clause,
            &transition.loop_invariant_correspondence,
            loop_index,
        )?;
    }

    execution
        .core
        .record_statement_transition_with_loan_evidence(
            function,
            arguments,
            transition.theorem.clone(),
            transition.context.clone(),
            &transition.execution_facts,
            &transition.obligations,
            &transition.loan_evidence,
        )
        .map_err(|refusal| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` recorded statement evidence the proof object rejected: {}",
                describe_evidence_refusal(&refusal, parameters, arguments)
            ))
        })?;
    if let Some(parent) = loop_return_parent {
        for (return_index, returned) in loop_return_transitions.into_iter().enumerate() {
            // The path's fact base: what was available at the loop, plus what
            // the returned path itself states. Nothing the continuing path
            // establishes after the loop is cited on it.
            let mut returned_facts = loop_index
                .and_then(|index| execution.presentation.loop_return_proofs.get(&index))
                .map(|planned| planned.entry_facts.clone())
                .unwrap_or_else(|| ProofFacts::from_source(&*available_pure_facts));
            for fact in returned.pure_facts.iter() {
                if !returned_facts.contains(fact) {
                    returned_facts = returned_facts.with_kernel_checked_fact(fact.clone());
                }
            }
            let (outcome, obligations) = crate::kernel::c_function_outcome_from_statement_outcome(
                &execution_start_state,
                function,
                returned.outcome.clone(),
                returned.obligations.clone(),
                returned_facts.assumptions(),
            );
            let mut completed_execution_facts =
                parent.completed_path_facts(&returned.execution_facts);
            append_execution_effect_facts(&mut completed_execution_facts, &parent.effect_facts);
            let loan_evidence = crate::kernel::concat_checked_loan_evidence(
                parent.loan_evidence(),
                &returned.loan_evidence,
            );
            execution
                .core
                .record_pending_loop_return(
                    &parent,
                    function,
                    arguments,
                    &returned.theorem,
                    &returned.context,
                    &returned.execution_facts,
                    &returned.obligations,
                    outcome,
                    completed_execution_facts,
                    obligations,
                    returned_facts,
                    loan_evidence,
                    loop_index,
                    return_index,
                )
                .map_err(|refusal| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` recorded a loop's returned path the proof object rejected: {}",
                        describe_evidence_refusal(&refusal, parameters, arguments)
                    ))
                })?;
        }
    }
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
    // Falling off a void function is a return in the kernel's C semantics.
    // A source-less one-call proof can reach this boundary without the
    // explicit return node normally inserted by C parsing.
    let outcome = match transition.outcome {
        CStatementOutcome::Normal(state)
            if function.return_type() == crate::kernel::CType::Void
                && remaining.is_none()
                && execution.core.frontier.region == ExecutionRegionKind::Function
                && execution.core.frontier.continuations.is_empty() =>
        {
            CStatementOutcome::Return {
                value: CValue::Void,
                state,
            }
        }
        outcome => outcome,
    };
    if let Some(loop_index) = loop_index
        && let CStatementOutcome::Normal(state) = &outcome
    {
        record_loop_program_snapshot_state(
            &mut execution.presentation.recorded_snapshots,
            function_block,
            loop_index,
            ProgramPointKind::Exit,
            *state.clone(),
        );
    }
    let mut outcome = outcome;
    let abrupt = !matches!(outcome, CStatementOutcome::Normal(_));
    let ended = proof_context
        .constants
        .source_layout
        .automatic_exits(statement_index, abrupt);
    match &mut outcome {
        CStatementOutcome::Normal(state)
        | CStatementOutcome::Break(state)
        | CStatementOutcome::Continue(state)
        | CStatementOutcome::Return { state, .. }
        | CStatementOutcome::Throw { state, .. }
        | CStatementOutcome::Jump { state, .. } => {
            **state = execution
                .core
                .record_automatic_lifetime_end(state, ended)
                .map_err(|error| {
                    ClickError::new(format!(
                        "{}{}",
                        crate::surface::diagnostics::describe_runtime_error_over_locals(
                            &error, state
                        ),
                        crate::surface::diagnostics::describe_c_statement_site(),
                    ))
                    .with_kind(runtime_refusal_kind(&error))
                })?;
        }
        _ => {}
    }
    if let Some(statement_exit_state) = match &outcome {
        CStatementOutcome::Normal(state)
        | CStatementOutcome::Break(state)
        | CStatementOutcome::Continue(state)
        | CStatementOutcome::Jump { state, .. }
        | CStatementOutcome::Return { state, .. }
        | CStatementOutcome::Throw { state, .. } => Some(state.clone()),
        CStatementOutcome::UndefinedBehavior(_) | CStatementOutcome::RuntimeError(_) => None,
        CStatementOutcome::VerificationDiverges => None,
    } {
        record_statement_program_snapshot_state(
            &mut execution.presentation.recorded_snapshots,
            function_block,
            statement_index,
            ProgramPointKind::Exit,
            *statement_exit_state,
        );
        if let Some(loop_index) = loop_index
            && !matches!(outcome, CStatementOutcome::Normal(_))
        {
            record_loop_program_snapshot_state(
                &mut execution.presentation.recorded_snapshots,
                function_block,
                loop_index,
                ProgramPointKind::Exit,
                match &outcome {
                    CStatementOutcome::Normal(state)
                    | CStatementOutcome::Break(state)
                    | CStatementOutcome::Continue(state)
                    | CStatementOutcome::Jump { state, .. }
                    | CStatementOutcome::Return { state, .. }
                    | CStatementOutcome::Throw { state, .. } => *state.clone(),
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
                    *next_state.clone(),
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
            execution.core.state = (*next_state.clone()).into();
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
                        *next_state,
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
                        *next_state,
                    );
                }
                None => {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached the end of the function without a return"
                    )));
                }
            }
        }
        CStatementOutcome::Return { .. } | CStatementOutcome::Throw { .. } => {
            // A `Throw` inside an entered `try` body resumes at the handler
            // entry instead of terminating the path. Only entered `try`
            // bodies push handler continuations, so C execution (and throws
            // outside any `try`) always takes the termination path below.
            // Routed paths fall through to the shared epilogue like normally
            // completed steps.
            let routed = if let CStatementOutcome::Throw { value, state } = &outcome {
                route_throw_to_handler(
                    execution,
                    proof_context,
                    available_pure_facts,
                    &mut introduced_facts,
                    function,
                    arguments,
                    parameters,
                    function_block,
                    function_environment,
                    claim_label,
                    tactic_index,
                    tactic_name,
                    prerequisite_policy,
                    fact_transport_policy,
                    context,
                    value,
                    state,
                    &successor_pure_facts,
                )?
            } else {
                false
            };
            if !routed {
                record_completed_continuation_exits(&mut execution.core.frontier);
                let return_assumptions = {
                    let _return_context = crate::instrumentation::OperationTiming::new(
                        function.name(),
                        claim_label,
                        "statement return context",
                    );
                    successor_pure_facts.context()
                };
                let case_outcomes =
                    crate::kernel::c_function_outcomes_from_statement_outcome_with_resource_cases(
                        &execution_start_state,
                        function,
                        arguments,
                        outcome.clone(),
                        transition_obligations.clone(),
                        &return_assumptions,
                    );
                let mut completed_outcomes = Vec::new();
                for (outcome, obligations, case_facts) in case_outcomes {
                    let mut completed_execution_facts =
                        execution.core.completed_path_facts(&execution_pure_facts);
                    append_execution_effect_facts(
                        &mut completed_execution_facts,
                        &execution.core.effect_facts,
                    );
                    for fact in case_facts {
                        completed_execution_facts.push(ExecutionPureFact::new(fact));
                    }
                    completed_outcomes.push((
                        outcome,
                        completed_execution_facts,
                        obligations,
                        execution.core.loan_evidence().clone(),
                    ));
                }
                append_pending_loop_returns(&mut execution.core, &mut completed_outcomes);
                let completed =
                    crate::kernel::c_function_execution_candidates_from_outcomes_with_loan_evidence(
                        execution_start_state.clone(),
                        function.clone(),
                        arguments.to_vec(),
                        completed_outcomes,
                    );
                // The returning statement's own successor facts are this
                // path's, exactly as a continuing statement's are: a loop
                // rule's `Return` path states the conditions the body took
                // on the way to its `return` (`flag == 0` for a body that
                // returns under `if (flag == 0)`), and the proof that closes
                // the postcondition on the returned value folds through them
                // only when they are its facts, not merely the candidate's.
                // A plain `return x;` adds nothing here and loses nothing.
                *available_pure_facts = successor_pure_facts;
                if let Some(loop_index) = loop_index
                    && matches!(outcome, CStatementOutcome::Return { .. })
                {
                    // Those facts are stated over the loop's iteration
                    // identities. The loop's exit snapshot, recorded above
                    // from this returned state, binds them; the statement's
                    // entry snapshot, where premises are otherwise read,
                    // predates the head's havoc and cannot spell them.
                    execution.presentation.surface_record.last_step_entry = Some(ProgramPointRef {
                        region: CodeRegionRef::Loop(loop_index),
                        kind: ProgramPointKind::Exit,
                    });
                }
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
                execution.core.state = execution_state.into();
            }
        }
        CStatementOutcome::Break(next_state) | CStatementOutcome::Continue(next_state) => {
            // The control statement's own successor facts are this path's:
            // `if (i == 3) break;` leaves the loop knowing `i == 3`, and a
            // `break` exit that lost its guard would state nothing at all.
            // The frontier itself was advanced when the evidence was
            // recorded: inside a loop-body region both controls reach its
            // typed boundary, and a concretely executed loop resumes at its
            // own continuation.
            *available_pure_facts = successor_pure_facts;
            execution.core.frontier.execution_start_state = Some(execution_start_state);
            execution.core.state = (*next_state).into();
        }
        CStatementOutcome::Jump {
            target,
            state: next_state,
        } => {
            if execution.core.frontier.natural_backedge_target == Some(target)
                && execution.core.frontier.in_loop_body
            {
                *available_pure_facts = successor_pure_facts;
                execution.core.frontier.position = FrontierPosition::RegionBoundary;
                execution.core.frontier.loop_control = Default::default();
                execution.core.frontier.execution_start_state = Some(execution_start_state);
                execution.core.state = (*next_state).into();
                return Ok(introduced_facts);
            }
            if execution.core.frontier.natural_exit_target == Some(target)
                && execution.core.frontier.in_loop_body
            {
                *available_pure_facts = successor_pure_facts;
                execution.core.frontier.position = FrontierPosition::RegionBoundary;
                execution.core.frontier.loop_control =
                    crate::kernel::proof::LoopControlExit::NaturalExit(target);
                execution.core.frontier.execution_start_state = Some(execution_start_state);
                execution.core.state = (*next_state).into();
                return Ok(introduced_facts);
            }
            let target_id = target;
            let target = function.control_target(target_id).ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced an unknown goto target"
                ))
            })?;
            *available_pure_facts = successor_pure_facts;
            execution.core.frontier.execution_start_state = Some(execution_start_state);
            let target_statement_index = loop_index
                .and_then(|loop_index| {
                    proof_context
                        .constants
                        .source_layout
                        .natural_exit_target(loop_index)
                        .filter(|natural_target| *natural_target == target_id)
                        .and_then(|_| {
                            proof_context
                                .constants
                                .source_layout
                                .natural_exit_statement_index(loop_index)
                        })
                })
                .unwrap_or(target.statement_index);
            record_statement_program_snapshot_state(
                &mut execution.presentation.recorded_snapshots,
                function_block,
                target_statement_index,
                ProgramPointKind::Entry,
                *next_state.clone(),
            );
            execution.core.state = (*next_state).into();
        }
        CStatementOutcome::VerificationDiverges => {
            let mut completed_execution_facts =
                execution.core.completed_path_facts(&execution_pure_facts);
            append_execution_effect_facts(
                &mut completed_execution_facts,
                &execution.core.effect_facts,
            );
            let mut completed_outcomes = vec![(
                CFunctionOutcome::VerificationDiverges,
                completed_execution_facts,
                transition_obligations,
                execution.core.loan_evidence().clone(),
            )];
            append_pending_loop_returns(&mut execution.core, &mut completed_outcomes);
            let completed =
                crate::kernel::c_function_execution_candidates_from_outcomes_with_loan_evidence(
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
            execution.core.state = execution_state.into();
        }
        CStatementOutcome::UndefinedBehavior(kind) => {
            let outcome = CFunctionOutcome::UndefinedBehavior(kind);
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced {}{}\n{}",
                describe_function_outcome(&outcome, parameters, arguments),
                crate::surface::diagnostics::describe_c_statement_site(),
                describe_proof_context(
                    &listed_context_pure_facts(available_pure_facts, context),
                    &current_resources,
                    parameters,
                    arguments,
                    &execution_pure_facts
                )
            )));
        }
        CStatementOutcome::RuntimeError(error) => {
            let kind = runtime_refusal_kind(&error);
            let unsupported = kind == crate::surface::ClickErrorKind::Internal;
            let description = if unsupported {
                "reached an unsupported modeled operation"
            } else {
                "could not verify C operation"
            };
            let detail = format!(
                "{}{}",
                describe_runtime_error(&error, parameters, arguments),
                describe_missing_range_end_note(&error, &current_resources, parameters, arguments)
            );
            if matches!(
                error,
                crate::kernel::CRuntimeError::UninitializedMutex { .. }
                    | crate::kernel::CRuntimeError::UnsupportedConcurrentMutex
            ) {
                return Err(ClickError::new(detail).with_kind(kind));
            }
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` {description}: {}\n  C operation: {}{}{}\n{}",
                detail,
                describe_statement_head(&step_statement),
                describe_call_bindings(&step_statement, function_environment),
                crate::surface::diagnostics::describe_c_statement_site(),
                describe_proof_context(
                    &listed_context_pure_facts(available_pure_facts, context),
                    &current_resources,
                    parameters,
                    arguments,
                    &execution_pure_facts
                )
            ))
            .with_kind(kind));
        }
    }
    execution
        .presentation
        .record_generated_load_source_events(&generated_load_source_events);
    // Standalone fact-transport steps are written against the post-statement
    // state, so their construction runs after the statement's exit snapshots
    // are in place. Each transport adds its target to the certificate-visible
    // certificate facts, and finishing the transports retires the stale
    // pre-statement sources, mirroring what the certificate's own check
    // carries across this statement.
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

/// Whether several checked successors of one statement are the cases of a
/// path split: each completes the statement normally or returns, and each
/// assumes a path fact some other successor does not, so the facts tell the
/// cases apart.
fn statement_successors_are_path_cases(transitions: &[CertifiedStatementTransition]) -> bool {
    let facts = transitions
        .iter()
        .map(|transition| transition.path_facts.as_slice())
        .collect::<Vec<_>>();
    transitions.iter().all(|transition| {
        matches!(
            transition.outcome,
            CStatementOutcome::Normal(_) | CStatementOutcome::Return { .. }
        ) && !distinguishing_path_facts(&transition.path_facts, &facts).is_empty()
    })
}

/// The facts in `facts` that not every case in `cases` assumes: the
/// conditions that select this case.
fn distinguishing_path_facts<'t>(
    facts: &'t [Proposition],
    cases: &[&[Proposition]],
) -> Vec<&'t Proposition> {
    facts
        .iter()
        .filter(|fact| !cases.iter().all(|other| other.contains(fact)))
        .collect()
}

/// One case of a path split: the checked path facts that select it.
struct PathCase<'t> {
    path_facts: &'t [Proposition],
}

impl<'t> PathCase<'t> {
    fn of_statement(transition: &'t CertifiedStatementTransition) -> Self {
        Self {
            path_facts: &transition.path_facts,
        }
    }
}

/// The Click condition a proof-level case split separates a C condition's
/// checked paths on first, when one has a spelling: the same choice the
/// planner makes before a `branch` whose condition has more paths than arms.
pub(super) fn condition_path_case_split_condition(
    path_facts: &[&[Proposition]],
    available: &dyn Fn(&Proposition) -> bool,
    state: &CState,
    proof_context: &ExecutionProofContext<'_>,
) -> Option<(ConditionTerm, ClickProposition)> {
    let cases = path_facts
        .iter()
        .map(|path_facts| PathCase { path_facts })
        .collect::<Vec<_>>();
    path_case_split_condition(&cases, available, state, proof_context)
}

/// The condition a case split of `cases` splits on first: a distinguishing
/// condition fact that some case assumes true and another false, that the
/// facts do not already decide, and that Click can spell in source terms.
/// A condition every case decides is preferred, in the cases' order: it is
/// the one the operation consults first on every path (`x > 0` in
/// `x > 0 && y > 0`, the address comparison before a load reads the cell it
/// selects), so the facts of each side are then the facts that side's paths
/// have. Splitting leaves fewer cases on each side, so repeating the split
/// separates every case.
fn path_case_split_condition(
    cases: &[PathCase<'_>],
    available: &dyn Fn(&Proposition) -> bool,
    state: &CState,
    proof_context: &ExecutionProofContext<'_>,
) -> Option<(ConditionTerm, ClickProposition)> {
    let facts = cases.iter().map(|case| case.path_facts).collect::<Vec<_>>();
    let decides = |case: &PathCase<'_>, condition: &ConditionTerm, value: bool| {
        case.path_facts
            .contains(&Proposition::ConditionIs(condition.clone(), value))
    };
    let candidates = cases
        .iter()
        .flat_map(|case| distinguishing_path_facts(case.path_facts, &facts))
        .filter_map(|fact| {
            let Proposition::ConditionIs(condition, _) = fact else {
                return None;
            };
            let splits = [true, false]
                .into_iter()
                .all(|value| cases.iter().any(|case| decides(case, condition, value)));
            let undecided = [true, false]
                .into_iter()
                .all(|value| !available(&Proposition::ConditionIs(condition.clone(), value)));
            (splits && undecided).then_some(condition)
        })
        .collect::<Vec<_>>();
    let decided_by_every_case = |condition: &ConditionTerm| {
        cases
            .iter()
            .all(|case| decides(case, condition, true) || decides(case, condition, false))
    };
    candidates
        .iter()
        .filter(|condition| decided_by_every_case(condition))
        .chain(
            candidates
                .iter()
                .filter(|condition| !decided_by_every_case(condition)),
        )
        .find_map(|condition| {
            let surface = synthesize_surface_proposition(
                &Proposition::ConditionIs((*condition).clone(), true),
                proof_context.parsed_function.parameters(),
                proof_context.arguments,
                state,
            )?;
            Some(((*condition).clone(), surface))
        })
}

/// What to write when a simple tactic meets a split it does not make: the
/// proof `if` on the condition a planner would split on first, which gives
/// each side its own frontier.
fn describe_path_case_split_guidance(
    split_condition: Option<&ClickProposition>,
    case_count: usize,
) -> String {
    let split = match split_condition {
        Some(condition) => format!(
            "Split the proof on the case condition first, then step each case:\n  if {} {{\n      step(); ...\n  }} else {{\n      step(); ...\n  }}\n",
            crate::surface::diagnostics::describe_click_proposition(condition)
        ),
        None => "No case condition has a Click spelling, so the cases cannot yet be split in source terms.\n".to_string(),
    };
    format!(
        "These successors are {} cases of one C operation, told apart only by the conditions above; a simple step never splits the proof. {split}`execute()` makes this split itself.\n",
        case_count,
    )
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

/// Appends the returned paths of summarized loops this execution retained to
/// the outcomes it completes with. Each was certified where its loop was
/// summarized; the function boundary is where it rejoins the path set, in
/// the order the proof object appends their traces.
fn append_pending_loop_returns(
    core: &mut crate::kernel::proof::ExecutionProofCore,
    completed_outcomes: &mut Vec<(
        CFunctionOutcome,
        ExecutionFacts,
        Vec<ProofObligation>,
        crate::kernel::CheckedLoanCallEvidenceSequence,
    )>,
) {
    for pending in core.complete_pending_loop_returns() {
        completed_outcomes.push((
            pending.outcome,
            pending.execution_facts,
            pending.obligations,
            pending.loan_evidence,
        ));
    }
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

/// Present the callee's parameter names alongside the written call arguments
/// when a call fails; no symbolic heap value is guessed for this diagnostic.
fn describe_call_bindings(statement: &CStatement, environment: &CExecutionEnvironment) -> String {
    let (name, arguments) = match statement {
        CStatement::Call {
            function_name,
            arguments,
        }
        | CStatement::CallAssign {
            function_name,
            arguments,
            ..
        } => (function_name.as_str(), arguments.as_slice()),
        _ => return String::new(),
    };
    let parameters = environment
        .get_function_contract(name)
        .map(|contract| contract.interface().parameters())
        .or_else(|| {
            environment
                .get_function(name)
                .map(|function| function.parameters())
        });
    let Some(parameters) = parameters else {
        return String::new();
    };
    let bindings = parameters
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| {
            format!("{} = {}", parameter.name(), describe_c_expression(argument))
        })
        .collect::<Vec<_>>();
    if bindings.is_empty() {
        String::new()
    } else {
        format!("\n  call bindings: {}", bindings.join(", "))
    }
}

/// A one-line C spelling of a statement's head, enough to recognize it in
/// a diagnostic: the first statement of a sequence, a loop or branch by its
/// condition, a body by its operation.
pub(super) fn describe_statement_head(statement: &CStatement) -> String {
    match statement {
        CStatement::Seq(first, _) => describe_statement_head(first),
        CStatement::Skip => "skip".to_string(),
        CStatement::Break => "break".to_string(),
        CStatement::Continue => "continue".to_string(),
        CStatement::Goto { target } => format!("goto target({})", target.0),
        CStatement::EndAutomaticLifetimes { .. } => "automatic lifetime end".to_string(),
        CStatement::ForStep {
            continue_after: true,
            ..
        } => "continue".to_string(),
        CStatement::ForStep { step, .. } => describe_statement_head(step),
        CStatement::Declare { name, .. } => format!("declare {name}"),
        CStatement::DeclareAggregate { name, .. } => format!("declare aggregate {name}"),
        CStatement::Assign { name, expression }
            if crate::surface::diagnostics::is_call_result_temporary(name) =>
        {
            describe_c_expression(expression)
        }
        CStatement::Assign { name, expression } => {
            format!("{name} = {}", describe_c_expression(expression))
        }
        CStatement::CallAssign {
            target,
            function_name,
            arguments,
        } => {
            let call = format!(
                "{}({})",
                crate::surface::diagnostics::describe_called_function(function_name),
                arguments
                    .iter()
                    .map(describe_c_expression)
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            if crate::surface::diagnostics::is_call_result_temporary(target) {
                call
            } else {
                format!("{target} = {call}")
            }
        }
        CStatement::Call {
            function_name,
            arguments,
        } => format!(
            "{}({})",
            crate::surface::diagnostics::describe_called_function(function_name),
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
            ..
        } => {
            let function = if *zeroed { "calloc" } else { "malloc" };
            format!("{target} = {function}({})", describe_c_expression(bytes))
        }
        CStatement::HeapFree { pointer } => format!("free({})", describe_c_expression(pointer)),
        CStatement::Assert { condition, .. } => {
            format!("assert({})", describe_c_expression(condition))
        }
        CStatement::Return(expression) => format!("return {}", describe_c_expression(expression)),
        CStatement::Throw(expression) => format!("throw {}", describe_c_expression(expression)),
        CStatement::TryCatchInt32 { binding, .. } => format!("try ... catch (int {binding})"),
        CStatement::Store { pointer, value } | CStatement::TypedStore { pointer, value, .. } => {
            format!(
                "*{} = {}",
                describe_c_expression(pointer),
                describe_c_expression(value)
            )
        }
        CStatement::InitializeScalarArray {
            target,
            count,
            copy,
            fresh,
            ..
        } => format!(
            "{} {} with {} scalar elements{}",
            if *fresh { "initialize" } else { "write" },
            describe_c_expression(target),
            count,
            if *copy {
                " by snapshot copy"
            } else {
                " by repetition"
            }
        ),
        CStatement::CopyAggregate { target, source, .. } => format!(
            "copy aggregate {} <- {}",
            describe_c_expression(target),
            describe_c_expression(source)
        ),
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

#[cfg(test)]
mod cursor_sequence_tests {
    use super::*;

    fn snapshot_test_leaf(name: String) -> ClickProposition {
        ClickProposition::Comparison {
            left: ContractExpression::CBinding(name),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::Old(Box::new(ContractExpression::CBinding("entry".into()))),
        }
    }

    fn annotate_on_small_stack(
        surface: ClickProposition,
    ) -> (Result<ClickProposition, ClickError>, usize) {
        std::thread::Builder::new()
            .name("snapshot-annotation-small-stack".into())
            .stack_size(256 * 1024)
            .spawn(move || {
                crate::instrumentation::measure_deterministic_work(|| {
                    annotate_surface_at_snapshot(
                        &surface,
                        &SnapshotSelector::Mark("chosen".into()),
                        SnapshotAnnotation::Reread,
                    )
                })
            })
            .unwrap()
            .join()
            .expect("snapshot annotation must not retain large recursive frames")
    }

    #[test]
    fn snapshot_annotation_depth_is_stack_safe_and_bounded() {
        for depth in [7, 15, 23, SNAPSHOT_ANNOTATION_DEPTH_LIMIT - 1] {
            let mut surface = snapshot_test_leaf("current".into());
            for _ in 0..depth {
                surface = ClickProposition::Not(Box::new(surface));
            }
            let (result, work) = annotate_on_small_stack(surface);
            let result = result.unwrap();
            assert_eq!(work, depth + 1);
            let mut leaf = &result;
            for _ in 0..depth {
                let ClickProposition::Not(body) = leaf else {
                    panic!("annotation must preserve every connective");
                };
                leaf = body;
            }
            let ClickProposition::Comparison { left, right, .. } = leaf else {
                panic!("annotation must preserve the leaf");
            };
            assert!(matches!(
                left,
                ContractExpression::At {
                    selector: SnapshotSelector::Mark(_),
                    ..
                }
            ));
            assert!(matches!(right, ContractExpression::Old(_)));
        }
        let mut too_deep = snapshot_test_leaf("current".into());
        for _ in 0..SNAPSHOT_ANNOTATION_DEPTH_LIMIT {
            too_deep = ClickProposition::Not(Box::new(too_deep));
        }
        let (result, work) = annotate_on_small_stack(too_deep);
        assert!(
            result
                .unwrap_err()
                .message()
                .contains("structural depth bound")
        );
        assert_eq!(work, SNAPSHOT_ANNOTATION_DEPTH_LIMIT + 1);
    }

    #[test]
    fn snapshot_annotation_work_is_linear_and_preserves_operand_order() {
        for leaves in [8, 16, 32, 64] {
            let mut level = (0..leaves)
                .map(|index| snapshot_test_leaf(index.to_string()))
                .collect::<Vec<_>>();
            while level.len() > 1 {
                let mut children = level.into_iter();
                level = Vec::new();
                while let Some(left) = children.next() {
                    let right = children.next().unwrap();
                    level.push(ClickProposition::Implies(Box::new(left), Box::new(right)));
                }
            }
            let (result, work) = annotate_on_small_stack(level.pop().unwrap());
            let result = result.unwrap();
            assert_eq!(work, 2 * leaves - 1);
            let mut pending = vec![&result];
            let mut index = 0;
            while let Some(node) = pending.pop() {
                match node {
                    ClickProposition::Implies(left, right) => {
                        pending.push(right);
                        pending.push(left);
                    }
                    ClickProposition::Comparison { left, .. } => {
                        let ContractExpression::At { expression, .. } = left else {
                            panic!("the comparison must read the selected snapshot");
                        };
                        assert_eq!(
                            expression.as_ref(),
                            &ContractExpression::CBinding(index.to_string())
                        );
                        index += 1;
                    }
                    _ => panic!("annotation changed a connective"),
                }
            }
            assert_eq!(index, leaves);
        }
    }

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
