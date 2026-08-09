use super::*;

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn execute_internal_proof(
    node: &InternalProofNode,
    context: ProofReplayContext,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
) -> Result<Vec<ProofReplayContext>, ClickError> {
    match node {
        InternalProofNode::Done => Ok(vec![context]),
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => {
            let branch_path = context.branch_path.clone();
            let context = replay_linear_tactics(
                context,
                function_block,
                parsed_function,
                claims,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                function,
                arguments,
                tactics,
            )
            .map_err(|error| add_proof_branch_path(error, &branch_path))?;
            execute_internal_proof(
                continuation,
                context,
                function_block,
                parsed_function,
                claims,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                function,
                arguments,
            )
        }
        InternalProofNode::Open {
            index,
            source_index,
            resource,
            body,
            continuation,
        } => {
            let mut opened = context;
            if opened.replay.is_at_function_exit() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {index}: `open` must begin before execution reaches function exit"
                )));
            }
            let surface_start = opened.replay.surface_replay.tactics.len();
            let unfolded = unfold_composite_resource(
                resource_environment,
                resource,
                parsed_function.parameters(),
                arguments,
                opened.state,
                &mut opened.pure_facts,
                &mut opened.replay.surface_propositions,
                predicate_environment,
                click_function_environment,
                claim_label,
                *index,
                ResourceBodyAccess::Open,
            )?;
            opened.state = unfolded.state;
            let preserve_exposed_body = unfolded.body_was_already_exposed;
            let opened_contexts = execute_internal_proof(
                body,
                opened,
                function_block,
                parsed_function,
                claims,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                function,
                arguments,
            )?;
            let mut contexts = Vec::new();
            for mut closed in opened_contexts {
                if closed.replay.is_at_function_exit() {
                    closed.replay.defer_post_execution(
                        *index,
                        *source_index,
                        PostExecutionTactic::CloseOpen {
                            resource: resource.clone(),
                            preserve_exposed_body,
                        },
                    );
                } else {
                    let pre_state = closed.replay.old_reference_state(&closed.state).clone();
                    closed.state = close_open_resource_at_current_point(
                        resource_environment,
                        resource,
                        claim_label,
                        *index,
                        &closed.pure_facts,
                        parsed_function.parameters(),
                        arguments,
                        &pre_state,
                        closed.state,
                        predicate_environment,
                        click_function_environment,
                        &closed.replay.unfolded_predicates,
                        preserve_exposed_body,
                    )?;
                }
                let nested = closed
                    .replay
                    .surface_replay
                    .tactics
                    .split_off(surface_start);
                closed
                    .replay
                    .surface_replay
                    .tactics
                    .push(ProofTactic::Open(ProofOpen {
                        resource: resource.clone(),
                        tactics: nested,
                    }));
                let mut continued = execute_internal_proof(
                    continuation,
                    closed,
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                )?;
                contexts.append(&mut continued);
            }
            Ok(contexts)
        }
        InternalProofNode::If {
            index,
            condition,
            then_branch,
            else_branch,
            continuation,
        } => {
            let condition_text = describe_click_proposition(condition);
            let mut contexts = Vec::new();
            for (branch_name, value, branch) in [
                ("then", true, then_branch.as_ref()),
                ("else", false, else_branch.as_ref()),
            ] {
                let mut branch_context = context.clone();
                let branch_description =
                    format!("{branch_name} branch of proof `if {condition_text}`");
                branch_context.branch_path.push(branch_description);
                let feasible = introduce_proof_case_assumption(
                    &mut branch_context,
                    condition,
                    value,
                    *index,
                    parsed_function.parameters(),
                    arguments,
                    predicate_environment,
                    click_function_environment,
                    claim_label,
                )
                .map_err(|error| add_proof_branch_path(error, &branch_context.branch_path))?;
                if !feasible {
                    continue;
                }
                let branch_contexts = execute_internal_proof(
                    branch,
                    branch_context,
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                )?;
                for branch_context in branch_contexts {
                    let mut continued = execute_internal_proof(
                        continuation,
                        branch_context,
                        function_block,
                        parsed_function,
                        claims,
                        claim_label,
                        function_environment,
                        predicate_environment,
                        click_function_environment,
                        resource_environment,
                        theorem_environment,
                        function,
                        arguments,
                    )?;
                    contexts.append(&mut continued);
                }
            }
            Ok(contexts)
        }
        InternalProofNode::Branch {
            index,
            ensuring,
            then_branch,
            else_branch,
            continuation,
        } => {
            let statement_index = context.replay.frontier.next_statement_index;
            let source_region = context
                .replay
                .source_layout
                .statement(statement_index)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {index}: `branch` could not resolve source statement({statement_index})"
                    ))
                })?;
            if !matches!(source_region.kind, SourceStatementKind::If { .. }) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {index}: `branch` requires a C `if` at the execution frontier, but statement({statement_index}) is not an `if`"
                )));
            }
            let continuation_index = source_region.continuation_node;
            let initial_continuation_depth = context.replay.frontier.continuations.len();
            let selected_source_index = context
                .replay
                .proof_site
                .as_ref()
                .and_then(selected_tactic_index_for_site);
            let capture_in_continuation = selected_source_index
                .is_some_and(|wanted| internal_proof_contains_source_index(continuation, wanted));
            let capture_condition = if selected_source_index.is_some() && !capture_in_continuation {
                let (_, _, statement, _) = next_top_level_statement_from_execution_point(
                    &context.replay,
                    &context.state,
                    function,
                    arguments,
                    claim_label,
                    *index,
                    "branch",
                )?;
                let CStatement::If { condition, .. } = statement else {
                    unreachable!("source branch was checked as an if above")
                };
                Some(surface_with_source_site(
                    &surface_c_condition(&condition),
                    &ProgramPointRef {
                        region: CodeRegionRef::Statement(statement_index),
                        kind: ProgramPointKind::Entry,
                    },
                )?)
            } else {
                None
            };
            let mut completed_contexts = Vec::new();
            let mut continuing_contexts = Vec::new();
            for (branch_name, take_then, branch) in [
                ("then", true, then_branch.as_ref()),
                ("else", false, else_branch.as_ref()),
            ] {
                let mut branch_context = context.clone();
                branch_context.branch_path.push(format!(
                    "{branch_name} arm of C `if` at statement({statement_index})"
                ));
                let entered = execute_branch_step_from_execution_point(
                    &mut branch_context.replay,
                    &mut branch_context.state,
                    &mut branch_context.pure_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    claim_label,
                    *index,
                    "branch",
                    Some(take_then),
                    &[],
                    StatementPrerequisitePolicy::Contextual,
                    BranchStepPolicy::Explore,
                    true,
                )
                .map_err(|error| add_proof_branch_path(error, &branch_context.branch_path))?;
                if !entered {
                    continue;
                }
                branch_context.replay.has_structured_branch_history = true;
                if let Some(condition) = &capture_condition {
                    branch_context
                        .replay
                        .deferred_expansion_path_choices
                        .push(SurfacePathChoice {
                            occurrence: statement_index,
                            condition: condition.clone(),
                            value: take_then,
                            // The path is attached to the selected tactic's
                            // standalone certificate, whose prefix starts at
                            // offset zero after capture resets surface replay.
                            tactic_offset: 0,
                        });
                }
                let branch_contexts = execute_internal_proof(
                    branch,
                    branch_context,
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                )?;
                for branch_context in branch_contexts {
                    let returned = branch_context.replay.is_at_function_exit();
                    let reached_continuation = branch_context
                        .replay
                        .completed_branch_regions
                        .contains(&statement_index)
                        && branch_context.replay.frontier.continuations.len()
                            <= initial_continuation_depth;
                    if !reached_continuation {
                        return Err(add_proof_branch_path(
                            ClickError::new(format!(
                                "`{claim_label}` tactic {index}: `{branch_name}` arm of `branch` must stop at the shared continuation statement({continuation_index}); its frontier is statement({})",
                                branch_context.replay.frontier.next_statement_index
                            )),
                            &branch_context.branch_path,
                        ));
                    }
                    if returned {
                        completed_contexts.push(branch_context);
                        continue;
                    }
                    continuing_contexts.push(branch_context);
                }
            }
            if completed_contexts.is_empty() && continuing_contexts.is_empty() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {index}: `branch` found no feasible C `if` arm"
                )));
            }
            if continuing_contexts.is_empty() {
                return Ok(completed_contexts);
            }

            let mut joined_context = if let Some(assertions) = ensuring {
                let mut common_pure_facts = continuing_contexts[0].pure_facts.clone();
                common_pure_facts.retain(|fact| {
                    continuing_contexts
                        .iter()
                        .skip(1)
                        .all(|context| context.pure_facts.contains(fact))
                });
                let mut common_resource_facts =
                    continuing_contexts[0].state.resources().facts().to_vec();
                common_resource_facts.retain(|fact| {
                    continuing_contexts
                        .iter()
                        .skip(1)
                        .all(|context| context.state.resources().facts().contains(fact))
                });
                let mut stable_join_locals = continuing_contexts[0]
                    .state
                    .locals()
                    .object_values()
                    .map(|(name, value)| (name.to_string(), value.clone()))
                    .collect::<BTreeMap<_, _>>();
                stable_join_locals.retain(|name, value| {
                    continuing_contexts
                        .iter()
                        .skip(1)
                        .all(|context| context.state.locals().get(name) == Some(value))
                });
                let joined_frontier = continuing_contexts[0].replay.frontier.next_statement_index;
                if continuing_contexts
                    .iter()
                    .skip(1)
                    .any(|context| context.replay.frontier.next_statement_index != joined_frontier)
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {index}: `branch` arms did not reach one common execution frontier"
                    )));
                }
                let target = ProgramPointRef {
                    region: CodeRegionRef::Statement(joined_frontier),
                    kind: ProgramPointKind::Entry,
                };
                let needs_abstraction = continuing_contexts.len() > 1;
                let mut joined: Option<ProofReplayContext> = None;
                for mut branch_context in continuing_contexts {
                    apply_branch_interface(
                        &target,
                        assertions,
                        *index,
                        &mut branch_context.replay,
                        &mut branch_context.state,
                        &mut branch_context.pure_facts,
                        parsed_function.parameters(),
                        arguments,
                        predicate_environment,
                        click_function_environment,
                        resource_environment,
                        claim_label,
                        &stable_join_locals,
                        needs_abstraction,
                    )
                    .map_err(|error| add_proof_branch_path(error, &branch_context.branch_path))?;
                    for fact in &common_pure_facts {
                        if !branch_context.pure_facts.contains(fact) {
                            branch_context.pure_facts.push(fact.clone());
                        }
                    }
                    let assumptions = assumptions_from_propositions(&branch_context.pure_facts);
                    let additional_common_resources = common_resource_facts
                        .iter()
                        .filter(|fact| !branch_context.state.resources().facts().contains(fact))
                        .cloned()
                        .collect::<Vec<_>>();
                    let resources = branch_context
                        .state
                        .resources()
                        .clone()
                        .try_compose_with_facts(additional_common_resources, &assumptions)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {index}: invalid automatic common `branch` resource interface: {error:?}"
                            ))
                        })?;
                    branch_context.state = branch_context.state.with_resource_context(resources);
                    if let Some(joined_context) = &mut joined {
                        append_execution_effect_facts(
                            &mut joined_context.replay.effect_facts,
                            &branch_context.replay.effect_facts,
                        );
                    } else {
                        joined = Some(branch_context);
                    }
                }
                joined.expect("at least one continuing branch context")
            } else if continuing_contexts.len() == 1 {
                continuing_contexts.remove(0)
            } else {
                let common_state = continuing_contexts[0].state.clone();
                if continuing_contexts
                    .iter()
                    .skip(1)
                    .any(|context| context.state != common_state)
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {index}: `branch` arms reach the common frontier with different states; add an `ensuring` block describing the facts and resources needed afterward"
                    )));
                }
                let mut joined = continuing_contexts.remove(0);
                joined.pure_facts.retain(|fact| {
                    continuing_contexts
                        .iter()
                        .all(|context| context.pure_facts.contains(fact))
                });
                joined.replay.program_point_states.retain(|point, state| {
                    continuing_contexts.iter().all(|context| {
                        context.replay.program_point_states.get(point) == Some(state)
                    })
                });
                for context in &continuing_contexts {
                    append_execution_effect_facts(
                        &mut joined.replay.effect_facts,
                        &context.replay.effect_facts,
                    );
                }
                joined
            };
            joined_context.branch_path.clear();
            joined_context.replay.case_assumptions.clear();
            let mut continued = execute_internal_proof(
                continuation,
                joined_context,
                function_block,
                parsed_function,
                claims,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                function,
                arguments,
            )?;
            completed_contexts.append(&mut continued);
            Ok(completed_contexts)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn introduce_proof_case_assumption(
    context: &mut ProofReplayContext,
    condition: &ClickProposition,
    value: bool,
    tactic_index: usize,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
) -> Result<bool, ClickError> {
    if context.replay.is_at_function_exit()
        && context.replay.has_structured_branch_history
        && proof_case_is_stable_program_point_condition(condition)
    {
        // A source-qualified condition can still be lowered without choosing
        // one return outcome. Use it immediately when possible so a logical
        // certificate nested under an already selected C path does not
        // manufacture its contradictory sibling at function exit. Conditions
        // involving `result` or the post-state retain the deferred per-outcome
        // handling below.
        if let Ok(proposition) = lower_point_proposition(
            condition,
            &context.pure_facts,
            parameters,
            arguments,
            context.replay.old_reference_state(&context.state),
            &context.state,
            None,
            &context.replay.program_point_states,
            predicate_environment,
            click_function_environment,
        ) {
            let surface_fact = if value {
                condition.clone()
            } else {
                negate_click_proposition(condition)
            };
            let kernel_fact = if value {
                proposition
            } else {
                match proposition {
                    Proposition::ConditionIs(condition, value) => {
                        Proposition::ConditionIs(condition, !value)
                    }
                    Proposition::Not(body) => *body,
                    proposition => Proposition::Not(Box::new(proposition)),
                }
            };
            if context
                .pure_facts
                .iter()
                .any(|available| propositions_are_exact_negations(available, &kernel_fact))
            {
                return Ok(false);
            }
            context
                .replay
                .surface_propositions
                .record_lowering(&surface_fact, &kernel_fact)?;
            context.pure_facts.push(kernel_fact.clone());
            context.replay.case_assumptions.push(ReplayCaseAssumption {
                tactic_index,
                condition: condition.clone(),
                value,
                fact: Some(kernel_fact),
                at_function_entry: false,
            });
            return Ok(true);
        }
    }
    if context.replay.is_at_function_exit() {
        context.replay.case_assumptions.push(ReplayCaseAssumption {
            tactic_index,
            condition: condition.clone(),
            value,
            fact: None,
            at_function_entry: false,
        });
        return Ok(true);
    }
    let at_function_entry = context.replay.is_at_function_entry();
    let proposition = lower_point_proposition(
        condition,
        &context.pure_facts,
        parameters,
        arguments,
        context.replay.old_reference_state(&context.state),
        &context.state,
        None,
        &context.replay.program_point_states,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not lower `if` condition: {message}"
        ))
    })?;
    let surface_fact = if value {
        condition.clone()
    } else {
        negate_click_proposition(condition)
    };
    let kernel_fact = if value {
        proposition
    } else {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                Proposition::ConditionIs(condition, !value)
            }
            Proposition::Not(body) => *body,
            proposition => Proposition::Not(Box::new(proposition)),
        }
    };
    if context
        .pure_facts
        .iter()
        .any(|available| propositions_are_exact_negations(available, &kernel_fact))
    {
        return Ok(false);
    }
    context
        .replay
        .surface_propositions
        .record_lowering(&surface_fact, &kernel_fact)?;
    context.pure_facts.push(kernel_fact.clone());
    context.replay.case_assumptions.push(ReplayCaseAssumption {
        tactic_index,
        condition: condition.clone(),
        value,
        fact: Some(kernel_fact),
        at_function_entry,
    });
    Ok(true)
}

fn proof_case_is_stable_program_point_condition(proposition: &ClickProposition) -> bool {
    let expression_is_stable = |expression: &ContractExpression| {
        matches!(
            expression,
            ContractExpression::At {
                selector: VisitSelector::ProgramPoint(_),
                ..
            } | ContractExpression::Old(_)
        )
    };
    fn stable(
        proposition: &ClickProposition,
        expression_is_stable: &impl Fn(&ContractExpression) -> bool,
    ) -> bool {
        match proposition {
            ClickProposition::Comparison { left, right, .. } => {
                expression_is_stable(left) && expression_is_stable(right)
            }
            ClickProposition::Defined { expression } => expression_is_stable(expression),
            ClickProposition::At {
                selector: VisitSelector::ProgramPoint(_),
                ..
            } => true,
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                stable(left, expression_is_stable) && stable(right, expression_is_stable)
            }
            ClickProposition::Not(body) => stable(body, expression_is_stable),
            ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. }
            | ClickProposition::ForAll { .. }
            | ClickProposition::Exists { .. }
            | ClickProposition::RangeAll { .. }
            | ClickProposition::RangeAny { .. }
            | ClickProposition::PredicateCall { .. } => false,
        }
    }
    stable(proposition, &expression_is_stable)
}

fn add_proof_branch_context(error: ClickError, branch: &str) -> ClickError {
    if error.is_expansion_complete() {
        return error;
    }
    ClickError::new(format!("in {branch}:\n{}", error.message()))
}

pub(in crate::lang::click::proof) fn add_proof_branch_path(
    mut error: ClickError,
    branch_path: &[String],
) -> ClickError {
    for branch in branch_path.iter().rev() {
        error = add_proof_branch_context(error, branch);
    }
    error
}
