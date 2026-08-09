use super::*;

pub(super) fn apply_branch_interface(
    target: &ProgramPointRef,
    assertions: &[ProofAssertion],
    tactic_index: usize,
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    claim_label: &str,
    stable_join_locals: &BTreeMap<String, CValue>,
    needs_abstraction: bool,
) -> Result<(), ClickError> {
    let mut concrete_facts = available_pure_facts.clone();
    let mut established_interface_resources = Vec::new();
    for assertion in assertions {
        match assertion {
            ProofAssertion::Fact(surface_fact) => {
                let fact = lower_point_proposition(
                        surface_fact,
                        &concrete_facts,
                        parameters,
                        arguments,
                        replay.old_reference_state(state),
                        state,
                        None,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `branch ensuring` fact: {message}"
                        ))
                })?;
                replay
                    .surface_propositions
                    .record_lowering(surface_fact, &fact)?;
                let assumptions = assumptions_from_propositions(&concrete_facts);
                if !concrete_facts.contains(&fact) && !assumptions.proves(&fact) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `branch ensuring` did not establish fact: {}",
                        describe_missing_pure_fact(
                            &fact,
                            &concrete_facts,
                            state.resources().facts(),
                            parameters,
                            arguments,
                            &[]
                        )
                    )));
                }
                if !concrete_facts.contains(&fact) {
                    concrete_facts.push(fact);
                }
            }
            ProofAssertion::Resource(resource) => {
                let expected =
                    lower_resource_clause_at_state(resource, parameters, arguments, state)?;
                let assumptions = assumptions_from_propositions(&concrete_facts);
                let is_observed_core = resource_is_direct_observed_core(
                    resource,
                    &established_interface_resources,
                    resource_environment,
                    claim_label,
                    tactic_index,
                )?;
                if !is_observed_core && !state.resources().satisfies_fact(&expected, &assumptions) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `branch ensuring` did not establish resource fact: {}",
                        describe_missing_resource_fact(
                            &expected,
                            &concrete_facts,
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
    let entry_state = replay.execution_start_state(state).clone();
    let mut abstract_state =
        abstract_c_state_for_join(state, stable_join_locals).map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not abstract `branch` target state: {message}"
            ))
        })?;

    // Branch abstraction discards incidental source-boundary snapshots, but
    // an explicit proof mark is a deliberate historical dependency. Preserve
    // marks that were common to every continuing arm.
    replay
        .program_point_states
        .retain(|point, _| matches!(point.region, CodeRegionRef::Mark(_)));
    replay
        .program_point_states
        .insert(target.clone(), abstract_state.clone());
    replay.unfolded_predicates.clear();
    replay.case_assumptions.clear();
    replay.execution_abstraction = true;

    let mut exported_resources = ResourceContext::new();
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
            // loadability in its entry-memory spelling. Export it exactly
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
                for fact in &replay.effect_facts {
                    if !pre_advance_facts.contains(fact.proposition()) {
                        pre_advance_facts.push(fact.proposition().clone());
                    }
                }
                let pre_advance = assumptions_from_propositions(&pre_advance_facts);
                for fact in entry_loadables {
                    if pre_advance.proves(&fact) && !exported_pure_facts.contains(&fact) {
                        exported_pure_facts.push(fact);
                    }
                }
            }
            if let ResourceClause::Declared {
                kind: ResourceKind::Composite,
                name,
                ..
            } = resource
            {
                let definition = resource_environment.get(name).ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unknown resource `{name}`"
                    ))
                })?;
                let CResource::Composite {
                    arguments: resource_arguments,
                    ..
                } = exported_resources
                    .facts()
                    .last()
                    .expect("exported composite resource was just appended")
                    .resource()
                else {
                    unreachable!("composite resource clause lowered to another resource family")
                };
                let (memory, _) = apply_composite_observation_law(
                    definition,
                    resource_arguments,
                    parameters,
                    arguments,
                    &entry_state,
                    &abstract_state,
                    &CValue::Int32(Bitvector32Term::Constant(0)),
                    &mut exported_pure_facts,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not project `branch ensuring` resource `{name}`: {message}"
                    ))
                })?;
                abstract_state = abstract_state.with_memory(memory);
            }
        }
    }
    abstract_state = abstract_state.with_resource_context(exported_resources.clone());
    replay
        .program_point_states
        .insert(target.clone(), abstract_state.clone());

    for assertion in assertions {
        if let ProofAssertion::Fact(surface_fact) = assertion {
            let fact = lower_point_proposition(
                    surface_fact,
                    &exported_pure_facts,
                    parameters,
                    arguments,
                    &entry_state,
                    &abstract_state,
                    None,
                    &replay.program_point_states,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not abstract `branch ensuring` fact: {message}"
                    ))
                })?;
            replay
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
    replay
        .program_point_states
        .insert(target.clone(), abstract_state.clone());
    *state = abstract_state;
    *available_pure_facts = exported_pure_facts;
    Ok(())
}

pub(super) fn append_execution_effect_facts(
    target: &mut Vec<ExecutionPureFact>,
    source: &[ExecutionPureFact],
) {
    for fact in source {
        // Verified-call rule results are kernel-certified transition facts,
        // just like memory-effect summaries. Keep them available to later
        // explicit replay without making the surface certificate restate
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
            | Proposition::CHeapLifetimeRetired { before, .. } => before,
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
            | Proposition::CHeapLifetimeRetired { .. }
    )
}

pub(super) fn is_implicit_fact_transport_context(proposition: &Proposition) -> bool {
    matches!(
        proposition,
        Proposition::CMemoryLoadable { .. }
            | Proposition::CMemoryCanStore { .. }
            | Proposition::CMemoryDisjoint { .. }
            | Proposition::CResourceSeparate { .. }
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
        // A guarded composite only exposes its children after the guard has
        // been selected. A joined interface does not carry enough state into
        // this syntactic shortcut, so keep guarded children explicit.
        if body.condition().is_some() {
            continue;
        }
        let substitutions =
            resource_argument_substitutions(definition, parent, claim_label, tactic_index)?;
        for child in body.contains() {
            let child = instantiate_resource_clause(child, &substitutions).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not instantiate observed child of `{name}`: {message}"
                ))
            })?;
            let core = match child {
                ResourceClause::Read(segment) | ResourceClause::Write(segment) => {
                    ResourceClause::Read(segment)
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
pub(super) fn execute_branch_step_from_execution_point(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
    requested_branch: Option<bool>,
    certified_prerequisites: &[PropositionDerivation],
    prerequisite_policy: StatementPrerequisitePolicy,
    branch_step_policy: BranchStepPolicy,
    complete_empty_branch: bool,
) -> Result<bool, ClickError> {
    replay.completed_branch_regions.clear();
    let statement_index = replay.frontier.next_statement_index;
    let source_region = replay.source_layout.statement(statement_index).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve source statement({statement_index})"
        ))
    })?;
    let (execution_start_state, mut current_state, statement, remaining) =
        next_top_level_statement_from_execution_point(
            replay,
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

    record_statement_program_point_state(
        replay,
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
        certified_prerequisites,
        true,
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
        let occurrence = replay.next_path_choice;
        replay.next_path_choice += 1;
        let statement_condition = surface_with_source_site(
            &surface_c_condition(&condition),
            &ProgramPointRef {
                region: CodeRegionRef::Statement(statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        // Prefer a spelling in terms of the shared function-entry snapshot.
        // It remains available after independently explored paths are merged,
        // whereas a later statement-entry state can legitimately differ
        // across those paths and is therefore not retained in the common
        // replay interface. Sorting networks are the representative case:
        // the second comparison's current operand is an entry value selected
        // by the first comparison.
        let condition = replay
            .function_entry_state
            .as_ref()
            .and_then(|entry_state| {
                condition_transition.path_facts.iter().find_map(|fact| {
                    let Proposition::ConditionIs(_, _) = fact else {
                        return None;
                    };
                    let surface =
                        synthesize_surface_proposition(fact, parameters, arguments, entry_state)?;
                    let surface = surface_with_source_site(
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
        replay
            .planned_tactics
            .push(ProofTactic::CertifiedPathAssumption {
                occurrence,
                condition,
                value: condition_transition.is_true,
                facts: condition_transition.path_facts.clone(),
                theorem: condition_transition.theorem.clone(),
            });
    }
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        append_condition_transition_certificate(
            replay,
            &condition_transition,
            condition_was_proven || matches!(branch_step_policy, BranchStepPolicy::RequireProven),
        );
    }
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
    replay
        .frontier
        .continuations
        .push(ProofExecutionContinuation {
            remaining,
            next_statement_index: source_region.continuation_node,
            kind: ProofExecutionContinuationKind::Branch { statement_index },
        });
    replay.frontier.next_statement_index = if selected_then {
        then_statement_index
    } else {
        else_statement_index
    };
    replay.frontier.execution_start_state = Some(execution_start_state);
    *state = current_state;
    if complete_empty_branch && matches!(selected_branch, CStatement::Skip) {
        let Some(remaining) = resume_after_completed_region(replay, function_block, state) else {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached the end of the function without a return"
            )));
        };
        replay.frontier.point = ProofExecutionPoint::StatementEntry { remaining };
    } else {
        replay.frontier.point = ProofExecutionPoint::StatementEntry {
            remaining: selected_branch,
        };
    }
    record_current_statement_entry(
        replay,
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
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
    certified_prerequisites: &[PropositionDerivation],
    prerequisite_policy: StatementPrerequisitePolicy,
    statement_index: usize,
    loop_index: usize,
    continuation_node: usize,
    execution_start_state: CState,
    current_state: CState,
    loop_statement: CStatement,
    remaining: Option<CStatement>,
) -> Result<(), ClickError> {
    replay.concrete_loop_execution = true;
    let CStatement::While {
        condition, body, ..
    } = loop_statement.clone()
    else {
        unreachable!("concrete loop stepping requires a while statement");
    };

    record_statement_program_point_state(
        replay,
        function_block,
        statement_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    record_loop_program_point_state(
        replay,
        function_block,
        loop_index,
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
        certified_prerequisites,
        true,
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
        append_condition_transition_certificate(replay, &condition_transition, true);
    }
    *available_pure_facts = condition_transition.pure_facts;
    replay.frontier.execution_start_state = Some(execution_start_state);
    *state = current_state.clone();

    if condition_transition.is_true {
        let loop_head = match remaining {
            Some(remaining) => c_seq(loop_statement, remaining),
            None => loop_statement,
        };
        replay
            .frontier
            .continuations
            .push(ProofExecutionContinuation {
                remaining: Some(loop_head),
                next_statement_index: statement_index,
                kind: ProofExecutionContinuationKind::LoopIteration,
            });
        replay.frontier.next_statement_index = replay
            .source_layout
            .loop_body_entry(loop_index)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve the source body of loop({loop_index})"
                ))
            })?;
        replay.frontier.point = ProofExecutionPoint::StatementEntry { remaining: *body };
        record_statement_program_point_state(
            replay,
            function_block,
            replay.frontier.next_statement_index,
            ProgramPointKind::Entry,
            current_state,
        );
        return Ok(());
    }

    record_statement_program_point_state(
        replay,
        function_block,
        statement_index,
        ProgramPointKind::Exit,
        current_state.clone(),
    );
    record_loop_program_point_state(
        replay,
        function_block,
        loop_index,
        ProgramPointKind::Exit,
        current_state.clone(),
    );
    let next = if let Some(remaining) = remaining {
        replay.frontier.next_statement_index = continuation_node;
        Some(remaining)
    } else {
        resume_after_completed_region(replay, function_block, &current_state)
    };
    let Some(remaining) = next else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached the end of the function without a return"
        )));
    };
    replay.frontier.point = ProofExecutionPoint::StatementEntry { remaining };
    record_statement_program_point_state(
        replay,
        function_block,
        replay.frontier.next_statement_index,
        ProgramPointKind::Entry,
        current_state,
    );
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn next_top_level_statement_from_execution_point(
    replay: &TacticReplayState,
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
) -> Result<NextTopLevelStatement, ClickError> {
    match &replay.frontier.point {
        ProofExecutionPoint::FunctionEntry => {
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
        ProofExecutionPoint::StatementEntry { remaining } => {
            let execution_start_state = replay
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
        ProofExecutionPoint::FunctionExit { .. } => Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` cannot run after execution already reached function exit"
        ))),
    }
}

pub(super) fn record_loop_program_point_state(
    replay: &mut TacticReplayState,
    function_block: &FunctionBlock,
    loop_index: usize,
    kind: ProgramPointKind,
    state: CState,
) {
    record_code_region_program_point_state(
        &mut replay.program_point_states,
        function_block,
        CodeRegion::Loop(loop_index),
        kind,
        state,
    );
}

pub(super) fn record_statement_program_point_state(
    replay: &mut TacticReplayState,
    function_block: &FunctionBlock,
    statement_index: usize,
    kind: ProgramPointKind,
    state: CState,
) {
    record_code_region_program_point_state(
        &mut replay.program_point_states,
        function_block,
        CodeRegion::Statement(statement_index),
        kind,
        state,
    );
}

pub(super) fn record_code_region_program_point_state(
    program_point_states: &mut ProgramPointStates,
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
    program_point_states.insert(
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
        program_point_states.insert(
            ProgramPointRef {
                region: CodeRegionRef::Label(label.to_string()),
                kind,
            },
            state.clone(),
        );
    }
}

fn replay_certified_statement_transition(
    evidence: &CertifiedStatementReplay,
    current_state: &CState,
    statement: &CStatement,
    available_pure_facts: &[Proposition],
    context_label: &str,
) -> Result<CertifiedStatementTransition, ClickError> {
    let mut replay_facts = available_pure_facts.to_vec();
    for fact in evidence
        .transition
        .execution_facts
        .iter()
        .filter(|fact| fact.is_certified())
    {
        if !replay_facts.contains(fact.proposition()) {
            replay_facts.push(fact.proposition().clone());
        }
    }
    let mut proposition = evidence.transition.theorem.proposition();
    while let Proposition::Implies(premise, body) = proposition {
        let mut certified_by_derivation = false;
        for derivation in &evidence.transition.prerequisite_derivations {
            if derivation.conclusion() == premise.as_ref()
                && derivation_replays_with_materialized_context(derivation, &replay_facts)?
            {
                certified_by_derivation = true;
                break;
            }
        }
        let certified = exact_fact_is_available(premise, available_pure_facts)
            || materialization_equivalent_available_fact(premise, available_pure_facts).is_some()
            || matches!(normalize_proposition(premise), SimpProposition::True)
            || evidence
                .transition
                .execution_facts
                .iter()
                .any(|fact| fact.is_certified() && fact.proposition() == premise.as_ref())
            || certified_by_derivation;
        if !certified {
            return Err(ClickError::new(format!(
                "{context_label} certificate is missing prerequisite {premise:?}"
            )));
        }
        proposition = body;
    }
    let Proposition::CStatementVerifies {
        state: theorem_state,
        statement: theorem_statement,
        outcome,
    } = proposition
    else {
        return Err(ClickError::new(format!(
            "{context_label} certificate has an unexpected theorem body: {proposition:?}"
        )));
    };
    if theorem_state != current_state || theorem_statement != statement {
        return Err(ClickError::new(format!(
            "{context_label} certificate does not match the current statement execution"
        )));
    }
    if outcome != &evidence.transition.outcome {
        return Err(ClickError::new(format!(
            "{context_label} certificate outcome does not match its execution theorem"
        )));
    }

    let mut transition = evidence.transition.clone();
    transition.pure_facts = available_pure_facts.to_vec();
    for fact in &transition.path_facts {
        if !transition.pure_facts.contains(fact) {
            transition.pure_facts.push(fact.clone());
        }
    }
    let internal_transports = transition
        .fact_transports
        .iter()
        .filter(|transport| transport.statement_local)
        .collect::<Vec<_>>();
    for transport in &internal_transports {
        if !exact_fact_is_available(&transport.source, &transition.pure_facts) {
            return Err(ClickError::new(format!(
                "{context_label} internal fact transport is missing exact statement-produced source {:?}",
                transport.source
            )));
        }
        let Proposition::Implies(theorem_source, theorem_target) = transport.theorem.proposition()
        else {
            return Err(ClickError::new(format!(
                "{context_label} internal fact transport theorem is not an implication"
            )));
        };
        if theorem_source.as_ref() != &transport.source
            || theorem_target.as_ref() != &transport.target
        {
            return Err(ClickError::new(format!(
                "{context_label} internal fact transport theorem does not match its source and target"
            )));
        }
    }
    let internal_sources = internal_transports
        .iter()
        .map(|transport| &transport.source)
        .collect::<Vec<_>>();
    transition
        .pure_facts
        .retain(|fact| !internal_sources.contains(&fact));
    for transport in internal_transports {
        if !transition.pure_facts.contains(&transport.target) {
            transition.pure_facts.push(transport.target.clone());
        }
    }
    transition.fact_transports.clear();
    Ok(transition)
}

pub(super) const SOURCE_SITE_ANNOTATION_DEPTH_LIMIT: usize = 32;

pub(super) fn surface_with_source_site(
    surface: &ClickProposition,
    point: &ProgramPointRef,
) -> Result<ClickProposition, ClickError> {
    if matches!(
        surface,
        ClickProposition::Loadable { .. }
            | ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
    ) {
        return Ok(ClickProposition::At {
            selector: VisitSelector::ProgramPoint(point.clone()),
            proposition: Box::new(surface.clone()),
        });
    }
    let expression_at_source = |expression: &ContractExpression| {
        if matches!(expression, ContractExpression::Old(_)) {
            expression.clone()
        } else {
            ContractExpression::At {
                selector: VisitSelector::ProgramPoint(point.clone()),
                expression: Box::new(match expression {
                    ContractExpression::At { expression, .. } => expression.as_ref().clone(),
                    expression => expression.clone(),
                }),
            }
        }
    };
    fn annotate(
        proposition: &ClickProposition,
        expression_at_source: &impl Fn(&ContractExpression) -> ContractExpression,
        depth: usize,
    ) -> Result<ClickProposition, ClickError> {
        if depth >= SOURCE_SITE_ANNOTATION_DEPTH_LIMIT {
            return Err(ClickError::new(
                "Surface Click source-site annotation exceeded its structural depth bound",
            ));
        }
        Ok(match proposition {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => ClickProposition::Comparison {
                left: expression_at_source(left),
                operator: *operator,
                right: expression_at_source(right),
            },
            ClickProposition::Defined { expression } => ClickProposition::Defined {
                expression: expression_at_source(expression),
            },
            ClickProposition::At { .. } => proposition.clone(),
            ClickProposition::And(left, right) => ClickProposition::And(
                Box::new(annotate(left, expression_at_source, depth + 1)?),
                Box::new(annotate(right, expression_at_source, depth + 1)?),
            ),
            ClickProposition::Or(left, right) => ClickProposition::Or(
                Box::new(annotate(left, expression_at_source, depth + 1)?),
                Box::new(annotate(right, expression_at_source, depth + 1)?),
            ),
            ClickProposition::Not(body) => {
                ClickProposition::Not(Box::new(annotate(body, expression_at_source, depth + 1)?))
            }
            ClickProposition::Implies(left, right) => ClickProposition::Implies(
                Box::new(annotate(left, expression_at_source, depth + 1)?),
                Box::new(annotate(right, expression_at_source, depth + 1)?),
            ),
            ClickProposition::ForAll { c_type, name, body } => ClickProposition::ForAll {
                c_type: *c_type,
                name: name.clone(),
                body: Box::new(annotate(body, expression_at_source, depth + 1)?),
            },
            ClickProposition::Exists { c_type, name, body } => ClickProposition::Exists {
                c_type: *c_type,
                name: name.clone(),
                body: Box::new(annotate(body, expression_at_source, depth + 1)?),
            },
            ClickProposition::RangeAll {
                start,
                end,
                item,
                body,
            } => ClickProposition::RangeAll {
                start: expression_at_source(start),
                end: expression_at_source(end),
                item: item.clone(),
                body: Box::new(annotate(body, expression_at_source, depth + 1)?),
            },
            ClickProposition::RangeAny {
                start,
                end,
                item,
                body,
            } => ClickProposition::RangeAny {
                start: expression_at_source(start),
                end: expression_at_source(end),
                item: item.clone(),
                body: Box::new(annotate(body, expression_at_source, depth + 1)?),
            },
            ClickProposition::PredicateCall { name, arguments } => {
                ClickProposition::PredicateCall {
                    name: name.clone(),
                    arguments: arguments.iter().map(expression_at_source).collect(),
                }
            }
            ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. } => proposition.clone(),
        })
    }
    annotate(surface, &expression_at_source, 0)
}

pub(super) fn predicate_call_source_site(surface: &ClickProposition) -> Option<ProgramPointRef> {
    let ClickProposition::PredicateCall { arguments, .. } = surface else {
        return None;
    };
    arguments.iter().find_map(|argument| {
        let ContractExpression::At {
            selector: VisitSelector::ProgramPoint(point),
            ..
        } = argument
        else {
            return None;
        };
        Some(point.clone())
    })
}

#[allow(clippy::too_many_arguments)]
pub(super) fn execute_step_from_execution_point(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    _assumptions: &Assumptions,
    function_environment: &CExecutionEnvironment,
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
    certified_prerequisites: &[PropositionDerivation],
    certified_replay: Option<&CertifiedStatementReplay>,
    prerequisite_policy: StatementPrerequisitePolicy,
    fact_transport_policy: StatementFactTransportPolicy,
    loop_step_policy: LoopStepPolicy,
) -> Result<(), ClickError> {
    replay.completed_branch_regions.clear();
    let statement_index = replay.frontier.next_statement_index;
    let source_region = replay.source_layout.statement(statement_index).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve source statement({statement_index})"
        ))
    })?;
    if matches!(source_region.kind, SourceStatementKind::If { .. }) {
        let entered = execute_branch_step_from_execution_point(
            replay,
            state,
            available_pure_facts,
            function_block,
            function,
            parameters,
            arguments,
            claim_label,
            tactic_index,
            "step",
            None,
            certified_prerequisites,
            prerequisite_policy,
            BranchStepPolicy::RequireProven,
            false,
        )?;
        debug_assert!(entered);
        return Ok(());
    }
    let loop_index = match source_region.kind {
        SourceStatementKind::Loop { loop_index } => Some(loop_index),
        SourceStatementKind::Plain | SourceStatementKind::If { .. } => None,
    };
    let (execution_start_state, current_state, source_statement, remaining) =
        next_top_level_statement_from_execution_point(
            replay,
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
        return execute_concrete_loop_head_step(
            replay,
            state,
            available_pure_facts,
            function_block,
            parameters,
            arguments,
            claim_label,
            tactic_index,
            tactic_name,
            certified_prerequisites,
            prerequisite_policy,
            statement_index,
            loop_index,
            source_region.continuation_node,
            execution_start_state,
            current_state,
            source_statement,
            remaining,
        );
    }
    let step_statement = source_statement;

    record_statement_program_point_state(
        replay,
        function_block,
        statement_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    if let Some(loop_index) = loop_index {
        record_loop_program_point_state(
            replay,
            function_block,
            loop_index,
            ProgramPointKind::Entry,
            current_state.clone(),
        );
    }
    let current_resources = current_state.resources().facts().to_vec();
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    let direct_transition = certified_replay
        .map(|evidence| {
            replay_certified_statement_transition(
                evidence,
                &current_state,
                &step_statement,
                available_pure_facts,
                &transition_label,
            )
        })
        .transpose()?;
    let transitions = if let Some(transition) = direct_transition {
        replay.next_opaque_call = certified_replay
            .expect("a direct transition requires replay evidence")
            .next_opaque_call;
        replay.next_verification_variable = certified_replay
            .expect("a direct transition requires replay evidence")
            .next_verification_variable;
        vec![transition]
    } else {
        certified_statement_transitions(
            &current_state,
            available_pure_facts,
            &step_statement,
            function_environment,
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &transition_label,
            &mut replay.next_opaque_call,
            &mut replay.next_verification_variable,
            prerequisite_policy,
            fact_transport_policy,
            certified_prerequisites,
        )?
        .0
    };
    if transitions.len() > 1
        && transitions
            .iter()
            .all(|transition| matches!(transition.outcome, CStatementOutcome::Return { .. }))
    {
        // A single source return can have several valid operational outcomes,
        // notably when it returns an unresolved malloc result. This is not C
        // control flow and needs no proof-level case split: all successors
        // complete the function at the same statement boundary.
        if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
            let mut prerequisite_derivations = Vec::new();
            let mut exact_premises = Vec::new();
            for transition in &transitions {
                for derivation in &transition.prerequisite_derivations {
                    if !prerequisite_derivations.contains(derivation) {
                        prerequisite_derivations.push(derivation.clone());
                    }
                }
                for fact in &transition.planning_premises {
                    if !exact_premises.contains(fact) {
                        exact_premises.push(fact.clone());
                    }
                }
                for transport in &transition.fact_transports {
                    if !transport.statement_local
                        && exact_fact_is_available(&transport.source, available_pure_facts)
                        && !exact_premises.contains(&transport.source)
                    {
                        exact_premises.push(transport.source.clone());
                    }
                }
                for obligation in &transition.obligations {
                    if exact_fact_is_available(obligation.proposition(), available_pure_facts)
                        && !exact_premises.contains(obligation.proposition())
                    {
                        exact_premises.push(obligation.proposition().clone());
                    }
                }
            }
            replay
                .planned_tactics
                .push(ProofTactic::CertifiedStatementStep {
                    prerequisite_derivations,
                    exact_premises,
                });
        }

        let mut common_pure_facts = transitions[0].pure_facts.clone();
        common_pure_facts.retain(|fact| {
            transitions
                .iter()
                .skip(1)
                .all(|transition| transition.pure_facts.contains(fact))
        });
        let mut completed_outcomes = Vec::new();
        for transition in transitions {
            let mut completed_execution_facts = transition.execution_facts;
            append_execution_effect_facts(&mut completed_execution_facts, &replay.effect_facts);
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
        let completed = c_function_execution_candidates_from_outcomes(
            execution_start_state.clone(),
            function.clone(),
            arguments.to_vec(),
            completed_outcomes,
        );
        let replay_state = execution_start_state.clone();
        set_replay_execution(
            replay,
            claim_label,
            tactic_index,
            tactic_name,
            execution_start_state,
            completed,
        )?;
        replay.frontier.next_statement_index = source_region.continuation_node;
        *available_pure_facts = common_pure_facts;
        *state = replay_state;
        return Ok(());
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
        let mut invariant_targets = transition.pure_facts.iter().filter(|fact| {
            !available_pure_facts.contains(fact)
                && !matches!(
                    fact,
                    Proposition::CMemoryEffectSummary { .. }
                        | Proposition::CMemoryMutatesOnly { .. }
                        | Proposition::CHeapLifetimeRetired { .. }
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
            let exit_surface = surface_with_source_site(surface, &exit_point)?;
            replay
                .surface_propositions
                .record_lowering(&exit_surface, target)?;
        }
    }
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        append_statement_transition_certificate(
            replay,
            &transition,
            if loop_index.is_some() {
                loop_step_policy
            } else {
                LoopStepPolicy::EnterBody
            },
        );
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
                    selector: VisitSelector::ProgramPoint(point.clone()),
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
            replay
                .surface_propositions
                .record_lowering(&surface, &equation)?;
        }
    }
    let execution_pure_facts = transition.execution_facts;
    append_execution_effect_facts(&mut replay.effect_facts, &execution_pure_facts);
    let transition_obligations = transition.obligations;
    let successor_pure_facts = transition.pure_facts;
    let outcome = transition.outcome;
    if let Some(statement_exit_state) = match &outcome {
        CStatementOutcome::Normal(state) | CStatementOutcome::Return { state, .. } => {
            Some(state.clone())
        }
        CStatementOutcome::UndefinedBehavior(_) | CStatementOutcome::RuntimeError(_) => None,
        CStatementOutcome::VerificationDiverges => None,
    } {
        record_statement_program_point_state(
            replay,
            function_block,
            statement_index,
            ProgramPointKind::Exit,
            statement_exit_state,
        );
        if let Some(loop_index) = loop_index {
            record_loop_program_point_state(
                replay,
                function_block,
                loop_index,
                ProgramPointKind::Exit,
                match &outcome {
                    CStatementOutcome::Normal(state) | CStatementOutcome::Return { state, .. } => {
                        state.clone()
                    }
                    CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_)
                    | CStatementOutcome::VerificationDiverges => unreachable!(),
                },
            );
        }
    }

    match outcome {
        CStatementOutcome::Normal(next_state) => {
            let remaining = if let Some(remaining) = remaining {
                replay.frontier.next_statement_index = source_region.continuation_node;
                remaining
            } else if let Some(remaining) =
                resume_after_completed_region(replay, function_block, &next_state)
            {
                remaining
            } else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached the end of the function without a return"
                )));
            };
            *available_pure_facts = successor_pure_facts;
            replay.frontier.execution_start_state = Some(execution_start_state);
            replay.frontier.point = ProofExecutionPoint::StatementEntry { remaining };
            *state = next_state.clone();
            record_statement_program_point_state(
                replay,
                function_block,
                replay.frontier.next_statement_index,
                ProgramPointKind::Entry,
                next_state,
            );
        }
        CStatementOutcome::Return { .. } => {
            if let CStatementOutcome::Return {
                state: return_state,
                ..
            } = &outcome
            {
                record_completed_continuation_exits(replay, function_block, return_state);
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
            append_execution_effect_facts(&mut completed_execution_facts, &replay.effect_facts);
            let completed = c_function_execution_candidates_from_outcomes(
                execution_start_state.clone(),
                function.clone(),
                arguments.to_vec(),
                vec![(outcome, completed_execution_facts, obligations)],
            );
            let replay_state = execution_start_state.clone();
            set_replay_execution(
                replay,
                claim_label,
                tactic_index,
                tactic_name,
                execution_start_state,
                completed,
            )?;
            replay.frontier.next_statement_index = source_region.continuation_node;
            *state = replay_state;
        }
        CStatementOutcome::VerificationDiverges => {
            let mut completed_execution_facts = execution_pure_facts;
            append_execution_effect_facts(&mut completed_execution_facts, &replay.effect_facts);
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
            let replay_state = execution_start_state.clone();
            set_replay_execution(
                replay,
                claim_label,
                tactic_index,
                tactic_name,
                execution_start_state,
                completed,
            )?;
            replay.frontier.next_statement_index = source_region.continuation_node;
            *state = replay_state;
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
    Ok(())
}

fn resume_after_completed_region(
    replay: &mut TacticReplayState,
    function_block: &FunctionBlock,
    state: &CState,
) -> Option<CStatement> {
    while let Some(continuation) = replay.frontier.continuations.pop() {
        if let ProofExecutionContinuationKind::Branch { statement_index } = continuation.kind {
            replay.completed_branch_regions.push(statement_index);
            record_statement_program_point_state(
                replay,
                function_block,
                statement_index,
                ProgramPointKind::Exit,
                state.clone(),
            );
        }
        replay.frontier.next_statement_index = continuation.next_statement_index;
        if let Some(remaining) = continuation.remaining {
            return Some(remaining);
        }
    }
    None
}

fn record_completed_continuation_exits(
    replay: &mut TacticReplayState,
    function_block: &FunctionBlock,
    state: &CState,
) {
    while let Some(continuation) = replay.frontier.continuations.pop() {
        if let ProofExecutionContinuationKind::Branch { statement_index } = continuation.kind {
            replay.completed_branch_regions.push(statement_index);
            record_statement_program_point_state(
                replay,
                function_block,
                statement_index,
                ProgramPointKind::Exit,
                state.clone(),
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn record_current_statement_entry(
    replay: &mut TacticReplayState,
    state: &CState,
    function_block: &FunctionBlock,
    function: &CFunction,
    arguments: &[CExpression],
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
) -> Result<(), ClickError> {
    let current_state = match &replay.frontier.point {
        ProofExecutionPoint::FunctionEntry => c_function_entry_state(state, function, arguments)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not bind function arguments"
                ))
            })?,
        ProofExecutionPoint::StatementEntry { .. } => state.clone(),
        ProofExecutionPoint::FunctionExit { .. } => return Ok(()),
    };
    record_statement_program_point_state(
        replay,
        function_block,
        replay.frontier.next_statement_index,
        ProgramPointKind::Entry,
        current_state,
    );
    Ok(())
}

pub(super) const BOUNDED_EXECUTE_STEP_LIMIT: usize = 10_000;

#[derive(Clone)]
pub(super) struct BoundedProofFrontier {
    pub(super) replay: TacticReplayState,
    pub(super) state: CState,
    pub(super) pure_facts: Vec<Proposition>,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn bounded_execute_from_execution_point(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    function_environment: &CExecutionEnvironment,
    claim_label: &str,
    tactic_index: usize,
    prerequisite_policy: StatementPrerequisitePolicy,
) -> Result<(), ClickError> {
    let mut pending = vec![BoundedProofFrontier {
        replay: replay.clone(),
        state: state.clone(),
        pure_facts: available_pure_facts.clone(),
    }];
    let mut completed = Vec::new();
    let mut executed_steps = 0;

    while let Some(mut frontier) = pending.pop() {
        if frontier.replay.is_at_function_exit() {
            completed.push(frontier);
            continue;
        }
        if executed_steps == BOUNDED_EXECUTE_STEP_LIMIT {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute` exhausted its {BOUNDED_EXECUTE_STEP_LIMIT}-step budget at statement({})",
                frontier.replay.frontier.next_statement_index
            )));
        }
        executed_steps += 1;

        let source_region = frontier
            .replay
            .source_layout
            .statement(frontier.replay.frontier.next_statement_index)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `execute` could not resolve source statement({})",
                    frontier.replay.frontier.next_statement_index
                ))
            })?;
        if matches!(source_region.kind, SourceStatementKind::If { .. }) {
            for take_then in [false, true] {
                let mut branch = frontier.clone();
                let entered = execute_branch_step_from_execution_point(
                    &mut branch.replay,
                    &mut branch.state,
                    &mut branch.pure_facts,
                    function_block,
                    function,
                    parameters,
                    arguments,
                    claim_label,
                    tactic_index,
                    "execute",
                    Some(take_then),
                    &[],
                    prerequisite_policy,
                    BranchStepPolicy::Explore,
                    false,
                )?;
                if entered {
                    pending.push(branch);
                }
            }
            continue;
        }

        let assumptions = assumptions_from_propositions(&frontier.pure_facts);
        execute_step_from_execution_point(
            &mut frontier.replay,
            &mut frontier.state,
            &mut frontier.pure_facts,
            function_block,
            function,
            parameters,
            arguments,
            &assumptions,
            function_environment,
            claim_label,
            tactic_index,
            "execute",
            &[],
            None,
            prerequisite_policy,
            StatementFactTransportPolicy::Automatic,
            LoopStepPolicy::EnterBody,
        )
        .map_err(|error| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute` failed after {executed_steps} small execution steps: {}",
                error.message()
            ))
        })?;
        pending.push(frontier);
    }

    let alternatives = if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        Some(
            completed
                .iter()
                .map(|frontier| {
                    InternalProofPlan::from_planned_tactics(&frontier.replay.planned_tactics)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `execute` path planned a non-certificate tactic {:?}",
                                error.smart_tactic()
                            ))
                        })
                })
                .collect::<Result<Vec<_>, _>>()?,
        )
    } else {
        None
    };
    merge_bounded_execution_frontiers(
        replay,
        state,
        available_pure_facts,
        function,
        arguments,
        completed,
        claim_label,
        tactic_index,
    )?;
    if let Some(alternatives) = alternatives {
        replay.planned_tactics = vec![ProofTactic::CertifiedAlternatives(alternatives)];
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn merge_bounded_execution_frontiers(
    replay: &mut TacticReplayState,
    state: &mut CState,
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
        .replay
        .frontier
        .execution_start_state
        .clone()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute` has no execution start state"
            ))
        })?;
    let mut common_pure_facts = completed[0].pure_facts.clone();
    common_pure_facts.retain(|fact| {
        completed
            .iter()
            .skip(1)
            .all(|frontier| frontier.pure_facts.contains(fact))
    });
    let mut common_program_points = completed[0].replay.program_point_states.clone();
    common_program_points.retain(|point, point_state| {
        completed
            .iter()
            .skip(1)
            .all(|frontier| frontier.replay.program_point_states.get(point) == Some(point_state))
    });

    let mut paths = Vec::new();
    for frontier in &completed {
        let execution = frontier
            .replay
            .execution()
            .expect("completed bounded frontier should have an execution");
        for path in execution.paths() {
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
    let execution = c_function_execution_candidates_from_outcomes(
        execution_start_state.clone(),
        function.clone(),
        arguments.to_vec(),
        paths,
    );

    let mut merged = completed.remove(0);
    merged.replay.program_point_states = common_program_points;
    merged.replay.frontier.point = ProofExecutionPoint::FunctionExit { execution };
    merged.state = execution_start_state;
    merged.pure_facts = common_pure_facts;
    *replay = merged.replay;
    *state = merged.state;
    *available_pure_facts = merged.pure_facts;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn execute_rest_from_execution_point(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    function_environment: &CExecutionEnvironment,
    claim_label: &str,
    tactic_index: usize,
) -> Result<(), ClickError> {
    loop {
        let can_execute_one_step = match &replay.frontier.point {
            ProofExecutionPoint::FunctionEntry => {
                split_next_execution_step(function.body()).is_ok()
            }
            ProofExecutionPoint::StatementEntry { remaining } => {
                split_next_execution_step(remaining).is_ok()
            }
            ProofExecutionPoint::FunctionExit { .. } => return Ok(()),
        };
        if !can_execute_one_step {
            break;
        }

        let assumptions = assumptions_from_propositions(available_pure_facts);
        execute_step_from_execution_point(
            replay,
            state,
            available_pure_facts,
            function_block,
            function,
            parameters,
            arguments,
            &assumptions,
            function_environment,
            claim_label,
            tactic_index,
            "execute",
            &[],
            None,
            StatementPrerequisitePolicy::Planning,
            StatementFactTransportPolicy::Automatic,
            LoopStepPolicy::ApplyVerifiedRule,
        )?;
    }

    if !replay.is_at_function_exit() {
        bounded_execute_from_execution_point(
            replay,
            state,
            available_pure_facts,
            function_block,
            function,
            parameters,
            arguments,
            function_environment,
            claim_label,
            tactic_index,
            StatementPrerequisitePolicy::Planning,
        )?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn execute_until_statement(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    function_environment: &CExecutionEnvironment,
    statement_index: usize,
    claim_label: &str,
    tactic_index: usize,
    prerequisite_policy: StatementPrerequisitePolicy,
) -> Result<(), ClickError> {
    if replay.source_layout.statement(statement_index).is_none() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: function has no source statement({statement_index}); it contains {} statement regions",
            replay.source_layout.statement_count()
        )));
    }

    if replay.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `execute_until(statement({statement_index}))` cannot run after execution already reached function exit"
        )));
    }
    if statement_index < replay.frontier.next_statement_index {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `execute_until(statement({statement_index}))` cannot move backward from statement({})",
            replay.frontier.next_statement_index
        )));
    }

    while replay.frontier.next_statement_index != statement_index {
        let region_start = replay.frontier.next_statement_index;
        let assumptions = assumptions_from_propositions(available_pure_facts);
        execute_step_from_execution_point(
            replay,
            state,
            available_pure_facts,
            function_block,
            function,
            parameters,
            arguments,
            &assumptions,
            function_environment,
            claim_label,
            tactic_index,
            "execute_until",
            &[],
            None,
            prerequisite_policy,
            StatementFactTransportPolicy::Automatic,
            LoopStepPolicy::ApplyVerifiedRule,
        )?;
        if replay.is_at_function_exit() {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute_until(statement({statement_index}))` reached function exit before its target"
            )));
        }
        if replay.frontier.next_statement_index > statement_index {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute_until(statement({statement_index}))` target is not reachable from the current execution path; advancing statement({region_start}) moved the frontier to statement({})",
                replay.frontier.next_statement_index
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
    let mut statements = Vec::new();
    flatten_top_level_sequence(statement, &mut statements).map_err(|message| {
        format!("could not flatten the lowered statement sequence: {message}")
    })?;
    let Some(source_statement) = statements.first() else {
        return Err("lowered statement is missing its source operation".to_string());
    };
    let remaining = sequence_from_statements(&statements[1..]);
    Ok((source_statement.clone(), remaining))
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
    let (first, rest) = statements.split_first()?;
    Some(rest.iter().cloned().fold(first.clone(), c_seq))
}

fn set_replay_execution(
    replay: &mut TacticReplayState,
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
    execution_start_state: CState,
    execution: CFunctionExecutionCandidates,
) -> Result<(), ClickError> {
    if replay.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` cannot run after execution already reached function exit"
        )));
    }
    replay.frontier.execution_start_state = Some(execution_start_state);
    replay.frontier.point = ProofExecutionPoint::FunctionExit { execution };
    Ok(())
}

pub(super) fn require_function_exit(
    replay: &TacticReplayState,
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
) -> Result<(), ClickError> {
    if !replay.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires execution to reach function exit first"
        )));
    }
    Ok(())
}
