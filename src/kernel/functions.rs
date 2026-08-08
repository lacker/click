use super::prelude::*;
use std::collections::VecDeque;
#[derive(Clone, Debug, Eq, PartialEq)]
struct CFunctionResourceTransfer {
    callee_resources: ResourceContext,
    caller_resources_after_requirements: ResourceContext,
}

fn function_needs_outcome_resource_transfer(function: &CFunction) -> bool {
    function
        .composite_resource_definitions()
        .iter()
        .any(CCompositeResourceDefinition::needs_outcome_resource_transfer)
}

fn function_changes_declared_resource_quantities(function: &CFunction) -> bool {
    function.resource_requires() != function.resource_ensures()
}

fn complete_void_fallthrough(
    function: &CFunction,
    outcome: CStatementOutcome,
) -> CStatementOutcome {
    match (function.return_type(), outcome) {
        (CType::Void, CStatementOutcome::Normal(state)) => CStatementOutcome::Return {
            value: CValue::Void,
            state,
        },
        (_, outcome) => outcome,
    }
}

pub(super) fn execute_c_function_paths(
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &Assumptions,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    execute_c_function_paths_with_contract_resources(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
        false,
    )
}

pub(super) fn execute_c_function_paths_with_contract_resources(
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &Assumptions,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
    prepare_contract_resources: bool,
) -> ExecutionResult<Vec<CFunctionPath>> {
    budget.consume_function_call()?;
    if arguments.len() != function.parameters.len() {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::WrongArity {
                expected: function.parameters.len(),
                actual: arguments.len(),
            }),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    }

    let mut paths = Vec::new();
    for arguments_path in evaluate_c_arguments_paths(state, arguments, assumptions, budget)? {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(CFunctionPath {
                outcome,
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        }

        let Some(callee_state) = bind_c_function_arguments(state, function, &arguments_path.values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "could not bind arguments for {}",
                    function.name()
                ))),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        };

        let body_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        let (callee_state, resource_transfer) = if prepare_contract_resources {
            let resource_transfer = match prepare_function_resource_transfer(
                state,
                &callee_state,
                function,
                &body_assumptions,
                budget,
                true,
            )? {
                Ok(resource_transfer) => resource_transfer,
                Err(error) => {
                    paths.push(CFunctionPath {
                        outcome: CFunctionOutcome::RuntimeError(error),
                        facts: arguments_path.facts,
                        obligations: arguments_path.obligations,
                    });
                    continue;
                }
            };
            (
                callee_state.with_resource_context(resource_transfer.callee_resources.clone()),
                Some(resource_transfer),
            )
        } else {
            (callee_state, None)
        };
        for body_path in execute_c_statement_paths(
            &callee_state,
            function.body(),
            &body_assumptions,
            environment,
            execution_semantics,
            budget,
        )? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &arguments_path.facts,
                &arguments_path.obligations,
                &body_path.facts,
                &body_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            let return_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            let (outcome, obligations) = if let Some(resource_transfer) = &resource_transfer {
                if function_needs_outcome_resource_transfer(function) {
                    function_outcome_from_body_with_resource_transfer(
                        state,
                        function,
                        complete_void_fallthrough(function, body_path.outcome),
                        obligations,
                        &return_assumptions,
                        resource_transfer,
                        &arguments_path.values,
                        true,
                        budget,
                    )?
                } else if function_changes_declared_resource_quantities(function) {
                    function_outcome_from_body_with_population_transition(
                        state,
                        function,
                        complete_void_fallthrough(function, body_path.outcome),
                        obligations,
                        &return_assumptions,
                        &arguments_path.values,
                        budget,
                    )?
                } else {
                    function_outcome_from_body(
                        state,
                        function,
                        complete_void_fallthrough(function, body_path.outcome),
                        obligations,
                        &return_assumptions,
                        None,
                    )
                }
            } else {
                function_outcome_from_body(
                    state,
                    function,
                    complete_void_fallthrough(function, body_path.outcome),
                    obligations,
                    &return_assumptions,
                    None,
                )
            };

            paths.push(CFunctionPath {
                outcome,
                facts,
                obligations,
            });
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_function_verification_paths(
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &Assumptions,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
    variables: &mut VerificationVariableGenerator,
    prepare_contract_resources: bool,
) -> ExecutionResult<Vec<CFunctionPath>> {
    budget.consume_function_call()?;
    if arguments.len() != function.parameters.len() {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::WrongArity {
                expected: function.parameters.len(),
                actual: arguments.len(),
            }),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    }

    let mut paths = Vec::new();
    for arguments_path in evaluate_c_arguments_paths(state, arguments, assumptions, budget)? {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(CFunctionPath {
                outcome,
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        }

        let Some(callee_state) = bind_c_function_arguments(state, function, &arguments_path.values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "could not bind arguments for {}",
                    function.name()
                ))),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        };

        let body_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        let (callee_state, resource_transfer) = if prepare_contract_resources {
            let resource_transfer = match prepare_function_resource_transfer(
                state,
                &callee_state,
                function,
                &body_assumptions,
                budget,
                true,
            )? {
                Ok(resource_transfer) => resource_transfer,
                Err(error) => {
                    paths.push(CFunctionPath {
                        outcome: CFunctionOutcome::RuntimeError(error),
                        facts: arguments_path.facts,
                        obligations: arguments_path.obligations,
                    });
                    continue;
                }
            };
            (
                callee_state.with_resource_context(resource_transfer.callee_resources.clone()),
                Some(resource_transfer),
            )
        } else {
            (callee_state, None)
        };
        for body_path in execute_c_statement_verification_paths(
            &callee_state,
            function.body(),
            &body_assumptions,
            environment,
            execution_semantics,
            budget,
            variables,
        )? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &arguments_path.facts,
                &arguments_path.obligations,
                &body_path.facts,
                &body_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            let return_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            let (outcome, obligations) = if let Some(resource_transfer) = &resource_transfer {
                if function_needs_outcome_resource_transfer(function) {
                    function_outcome_from_body_with_resource_transfer(
                        state,
                        function,
                        complete_void_fallthrough(function, body_path.outcome),
                        obligations,
                        &return_assumptions,
                        resource_transfer,
                        &arguments_path.values,
                        true,
                        budget,
                    )?
                } else if function_changes_declared_resource_quantities(function) {
                    function_outcome_from_body_with_population_transition(
                        state,
                        function,
                        complete_void_fallthrough(function, body_path.outcome),
                        obligations,
                        &return_assumptions,
                        &arguments_path.values,
                        budget,
                    )?
                } else {
                    function_outcome_from_body(
                        state,
                        function,
                        complete_void_fallthrough(function, body_path.outcome),
                        obligations,
                        &return_assumptions,
                        None,
                    )
                }
            } else {
                function_outcome_from_body(
                    state,
                    function,
                    complete_void_fallthrough(function, body_path.outcome),
                    obligations,
                    &return_assumptions,
                    None,
                )
            };

            paths.push(CFunctionPath {
                outcome,
                facts,
                obligations,
            });
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_function_call_paths(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &Assumptions,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    match execution_semantics.calls {
        CCallSemantics::ExecuteBodies => {}
        CCallSemantics::ApplyVerifiedRules => {
            let Some(rule) = environment.get_verified_function_rule(function.name()) else {
                let error = if function.opaque_contract_supported() {
                    CRuntimeError::MissingVerifiedFunctionRule(function.name().to_string())
                } else {
                    CRuntimeError::UnsupportedOpaqueFunctionContract(function.name().to_string())
                };
                return Ok(vec![CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts: Vec::new(),
                    obligations: Vec::new(),
                }]);
            };
            return execute_verified_function_rule(
                caller_state,
                rule,
                arguments,
                assumptions,
                budget,
            );
        }
    }
    budget.consume_function_call()?;
    if arguments.len() != function.parameters.len() {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::WrongArity {
                expected: function.parameters.len(),
                actual: arguments.len(),
            }),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    }

    let mut paths = Vec::new();
    for arguments_path in evaluate_c_arguments_paths(caller_state, arguments, assumptions, budget)?
    {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(CFunctionPath {
                outcome,
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        }

        let Some(callee_state) =
            bind_c_function_arguments(caller_state, function, &arguments_path.values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "could not bind arguments for {}",
                    function.name()
                ))),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        };

        let body_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        let resource_transfer = match prepare_function_resource_transfer(
            caller_state,
            &callee_state,
            function,
            &body_assumptions,
            budget,
            false,
        )? {
            Ok(resource_transfer) => resource_transfer,
            Err(error) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts: arguments_path.facts,
                    obligations: arguments_path.obligations,
                });
                continue;
            }
        };
        let callee_state =
            callee_state.with_resource_context(resource_transfer.callee_resources.clone());
        for body_path in execute_c_statement_paths(
            &callee_state,
            function.body(),
            &body_assumptions,
            environment,
            execution_semantics,
            budget,
        )? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &arguments_path.facts,
                &arguments_path.obligations,
                &body_path.facts,
                &body_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            let return_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            let (outcome, obligations) = function_outcome_from_body_with_resource_transfer(
                caller_state,
                function,
                body_path.outcome,
                obligations,
                &return_assumptions,
                &resource_transfer,
                &arguments_path.values,
                true,
                budget,
            )?;

            paths.push(CFunctionPath {
                outcome,
                facts,
                obligations,
            });
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn execute_verified_function_rule(
    caller_state: &CState,
    rule: &CVerifiedFunctionRule,
    arguments: &[CExpression],
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    let function = &rule.function;
    budget.consume_function_call()?;
    let mut existing_variables = BTreeSet::new();
    collect_c_state_bitvector_variables(caller_state, &mut existing_variables);
    collect_c_function_bitvector_variables(function, &mut existing_variables);
    for argument in arguments {
        collect_c_expression_bitvector_variables(argument, &mut existing_variables);
    }
    collect_assumption_variables(assumptions, &mut existing_variables);
    let mut variables = VerificationVariableGenerator::fresh_for(
        budget.next_verification_variable,
        existing_variables,
    );
    let memory_identity = variables.next();
    let result_identity = variables.next();
    budget.next_verification_variable = variables.next;
    let mut paths = Vec::new();
    for arguments_path in evaluate_c_arguments_paths(caller_state, arguments, assumptions, budget)?
    {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(CFunctionPath {
                outcome,
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        }
        let Some(mut entry_state) =
            bind_c_function_arguments(caller_state, function, &arguments_path.values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "could not bind arguments for {}",
                    function.name()
                ))),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        };
        let path_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        let transfer = match prepare_function_resource_transfer(
            caller_state,
            &entry_state,
            function,
            &path_assumptions,
            budget,
            false,
        )? {
            Ok(transfer) => transfer,
            Err(error) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts: arguments_path.facts,
                    obligations: arguments_path.obligations,
                });
                continue;
            }
        };
        entry_state.resources = transfer.callee_resources.clone();
        let entry_contract_state =
            with_contract_argument_views(&entry_state, function, &arguments_path.values);

        let mut obligations = arguments_path.obligations;
        let mut facts = arguments_path.facts;
        let mut established_requirements = Vec::new();
        for requirement in function.contract_requires() {
            let requirement_assumptions =
                assumptions_with_path_context(&path_assumptions, &facts, &obligations);
            let requirement_assumptions =
                assumptions_with_propositions(&requirement_assumptions, &established_requirements);
            let lowering_assumptions = requirement_assumptions
                .clone()
                .allow_symbolic_contract_loads();
            let requirement_paths = lower_spec_proposition_at_state_with_loop_entry(
                &entry_contract_state,
                requirement,
                Some(&entry_contract_state),
                &lowering_assumptions,
                budget,
            )?;
            if requirement_paths.is_empty() {
                obligations.push(
                    ProofObligation::verification_condition(false_equals_true_proposition())
                        .with_context(format!("{} precondition", function.name())),
                );
                continue;
            }
            for requirement_path in requirement_paths {
                let path_assumptions = assumptions_with_path_context(
                    &requirement_assumptions,
                    &requirement_path.facts,
                    &requirement_path.obligations,
                );
                for path_obligation in &requirement_path.obligations {
                    let guarded = wrap_path_context(
                        path_obligation.proposition().clone(),
                        &requirement_path.facts,
                        &[],
                    );
                    if !requirement_assumptions.proves(&guarded) {
                        obligations.push(
                            ProofObligation::verification_condition(guarded.clone())
                                .with_context(format!("{} precondition", function.name())),
                        );
                    }
                    established_requirements.push(guarded);
                }
                let requirement_is_proven = match &requirement_path.proposition {
                    Proposition::ConditionIs(condition, value) => {
                        path_assumptions.proves_exact(&requirement_path.proposition)
                            || path_assumptions
                                .has_matching_condition_fact_for_memory_resolution(
                                    condition, *value,
                                )
                    }
                    Proposition::CResourceSeparate {
                        left: CResource::Memory(left),
                        right: CResource::Memory(right),
                    } => path_assumptions.proves_exact(&requirement_path.proposition)
                        || path_assumptions
                            .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                                left, right,
                            ),
                    proposition => path_assumptions.proves_exact(proposition),
                };
                let guarded_requirement = wrap_path_context(
                    requirement_path.proposition,
                    &requirement_path.facts,
                    &requirement_path.obligations,
                );
                if !requirement_is_proven && !requirement_assumptions.proves(&guarded_requirement) {
                    obligations.push(
                        ProofObligation::verification_condition(guarded_requirement.clone())
                            .with_context(format!("{} precondition", function.name())),
                    );
                }
                established_requirements.push(guarded_requirement);
            }
        }

        let effective_assumptions =
            assumptions_with_path_context(assumptions, &facts, &obligations);
        let effective_assumptions =
            assumptions_with_propositions(&effective_assumptions, &established_requirements);
        let footprint_state = entry_contract_state.clone();
        let mut mutable_ranges = Vec::new();
        let mut footprint_error = None;
        for segment in function.contract_mutable() {
            if segment.guard().is_some_and(|guard| {
                evaluate_guarded_contract_condition(
                    guard,
                    &entry_contract_state,
                    &effective_assumptions,
                    budget,
                ) == Some(false)
            }) {
                continue;
            }
            match evaluate_loop_effect_segment(
                &footprint_state,
                segment,
                &effective_assumptions,
                budget,
            )? {
                Ok(segment) => {
                    mutable_ranges.push(CMemoryRange::new(segment.base, segment.start, segment.end))
                }
                Err(message) => {
                    footprint_error = Some(message);
                    break;
                }
            }
        }
        if let Some(message) = footprint_error {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "could not evaluate mutable footprint: {message}"
                ))),
                facts,
                obligations,
            });
            continue;
        }

        let memory = if mutable_ranges.is_empty() {
            entry_state.memory.clone()
        } else {
            entry_state.memory.clone().with_call_memory_havoc(
                memory_identity,
                &mutable_ranges,
                &effective_assumptions,
            )
        };
        if !mutable_ranges.is_empty() {
            facts.push(ExecutionPureFact::internal(
                Proposition::CMemoryEffectSummary {
                    before: entry_state.memory.clone(),
                    after: memory.clone(),
                    mutable_ranges: mutable_ranges.clone(),
                },
            ));
        }
        let result = symbolic_call_result(function.return_type(), result_identity);
        let mut post_state = entry_state.clone().with_memory(memory);
        if function.return_type() != CType::Void {
            post_state.locals.set_typed(
                "result".to_string(),
                result.clone(),
                function.return_type(),
            );
        }
        let mut transition_state = post_state
            .clone()
            .with_resource_context(transfer.callee_resources.clone());
        let mut population_obligations = Vec::new();
        let population_transition = match apply_counted_population_transitions(
            caller_state,
            &mut transition_state,
            function,
            &arguments_path.values,
            &effective_assumptions,
            &mut population_obligations,
            true,
            budget,
        )? {
            Ok(transition) => transition,
            Err(error) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                });
                continue;
            }
        };
        post_state.counted_populations = transition_state.counted_populations;
        for obligation in population_obligations {
            facts.push(ExecutionPureFact::certified(
                obligation.proposition().clone(),
            ));
        }
        for proposition in &population_transition.population_facts {
            facts.push(ExecutionPureFact::certified(proposition.clone()));
        }
        let caller_resources_after_requirements =
            match apply_counted_population_transition_resources(
                transfer.caller_resources_after_requirements.clone(),
                &population_transition,
                &effective_assumptions,
            ) {
                Ok(resources) => resources,
                Err(error) => {
                    paths.push(CFunctionPath {
                        outcome: CFunctionOutcome::RuntimeError(error),
                        facts,
                        obligations,
                    });
                    continue;
                }
            };
        post_state.resources = caller_resources_after_requirements.clone();
        let output_resource_state =
            with_contract_argument_views(&post_state, function, &arguments_path.values);

        let return_resources = match evaluate_function_return_resources(
            &caller_resources_after_requirements,
            &output_resource_state,
            function,
            &effective_assumptions,
            budget,
        )? {
            Ok(resources) => resources,
            Err(error) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                });
                continue;
            }
        };
        let (memory, lifetime_effects) = match apply_verified_allocation_lifetime_effects(
            post_state.memory.clone(),
            &transfer.callee_resources,
            &return_resources,
            function,
            &effective_assumptions,
        ) {
            Ok(memory) => memory,
            Err(error) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                });
                continue;
            }
        };
        facts.extend(lifetime_effects);
        post_state.memory = memory;
        post_state.resources = return_resources.clone();
        let post_contract_state =
            with_contract_argument_views(&post_state, function, &arguments_path.values);

        for ensure in function.contract_ensures() {
            let ensure_assumptions =
                assumptions_with_path_context(&effective_assumptions, &facts, &obligations);
            let lowering_assumptions = ensure_assumptions.clone().allow_symbolic_contract_loads();
            let ensure_paths = lower_spec_proposition_at_state_with_loop_entry(
                &post_contract_state,
                ensure,
                Some(&entry_contract_state),
                &lowering_assumptions,
                budget,
            )?;
            for ensure_path in ensure_paths {
                for path_obligation in &ensure_path.obligations {
                    facts.push(ExecutionPureFact::certified(wrap_path_context(
                        path_obligation.proposition().clone(),
                        &ensure_path.facts,
                        &[],
                    )));
                }
                facts.push(ExecutionPureFact::certified(wrap_path_context(
                    ensure_path.proposition,
                    &ensure_path.facts,
                    &[],
                )));
            }
        }

        let mut return_state = caller_state.clone();
        return_state.memory = post_state.memory;
        return_state.resources = return_resources;
        return_state.counted_populations = post_state.counted_populations;
        paths.push(CFunctionPath {
            outcome: CFunctionOutcome::Return {
                value: result,
                state: return_state,
            },
            facts,
            obligations,
        });
    }
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn apply_verified_allocation_lifetime_effects(
    mut memory: CMemory,
    input_resources: &ResourceContext,
    output_resources: &ResourceContext,
    function: &CFunction,
    assumptions: &Assumptions,
) -> Result<(CMemory, Vec<ExecutionPureFact>), CRuntimeError> {
    let mut effects = Vec::new();
    let input = expand_all_composite_resource_facts(
        input_resources,
        function.composite_resource_definitions(),
        &memory,
        assumptions,
    )
    .ok_or_else(|| {
        CRuntimeError::FunctionContract(
            "could not inspect input allocation effects at call".to_string(),
        )
    })?;
    let output = expand_all_composite_resource_facts(
        output_resources,
        function.composite_resource_definitions(),
        &memory,
        assumptions,
    )
    .ok_or_else(|| {
        CRuntimeError::FunctionContract(
            "could not inspect output allocation effects at call".to_string(),
        )
    })?;
    let lifetime_assumptions = input
        .observable_facts_assuming_valid(assumptions)
        .into_iter()
        .fold(assumptions.clone(), |assumptions, fact| {
            assumptions.assume_proposition(fact)
        });

    for allocation in input.facts().iter().filter_map(|fact| {
        fact.allocation()
            .map(|(base, bytes)| (fact, base.clone(), bytes.clone()))
    }) {
        let (fact, base, bytes) = allocation;
        if expose_composite_resource_fact(
            &output,
            fact,
            function.composite_resource_definitions(),
            &memory,
            &lifetime_assumptions,
        )
        .is_some()
        {
            continue;
        }
        if let Some(stale) = output.facts().iter().find(|resource| {
            resource.may_refer_to_memory_block(&base.block)
                && !resource.is_proven_separate_from_allocation(
                    &base,
                    &bytes,
                    &lifetime_assumptions,
                )
        }) {
            return Err(CRuntimeError::StaleResourceAfterFree {
                resource: stale.clone(),
            });
        }
        let lifetime_before = memory.clone();
        if memory.live_heap_block_size(&base).is_none() {
            memory = memory
                .with_heap_allocation_claim(base.clone(), bytes.clone())
                .ok_or(CRuntimeError::InvalidFree(CInvalidFree::NonHeapPointer))?;
        }
        memory = memory
            .free_heap_block(&base)
            .map_err(CRuntimeError::InvalidFree)?;
        effects.push(ExecutionPureFact::internal(
            Proposition::CHeapLifetimeRetired {
                before: lifetime_before,
                after: memory.clone(),
                allocation_base: base,
                bytes,
            },
        ));
    }

    for (base, bytes) in output.facts().iter().filter_map(CResourceFact::allocation) {
        if input.facts().iter().any(|fact| {
            fact.allocation()
                .is_some_and(|(input_base, input_bytes)| input_base == base && input_bytes == bytes)
        }) || memory.live_heap_block_size(base).is_some()
        {
            continue;
        }
        memory = memory
            .with_heap_allocation_claim(base.clone(), bytes.clone())
            .ok_or_else(|| {
                CRuntimeError::FunctionContract(
                    "returned allocation conflicts with an existing or retired lifetime"
                        .to_string(),
                )
            })?;
    }
    Ok((memory, effects))
}

fn with_contract_argument_views(state: &CState, function: &CFunction, values: &[CValue]) -> CState {
    let mut state = state.clone();
    for (parameter, value) in function.parameters().iter().zip(values) {
        // Keep the contract view identical to the typed parameter binding.
        // In particular, a C null-pointer constant arrives here as the
        // caller's int32 `0`, but the callee parameter is a pointer.  Using
        // the raw caller value would overwrite the correctly coerced binding
        // and make pointer preconditions impossible to lower.
        let value = coerce_c_null_pointer_constant(value.clone(), parameter.c_type())
            .expect("function arguments were type-checked before building contract views");
        state.locals.set_typed(
            parameter.name().to_string(),
            value.clone(),
            parameter.c_type(),
        );
        if let CValue::Pointer(pointer) = &value {
            state.resources = state
                .resources
                .unchecked_with_fact(CResourceFact::view_memory(CMemoryRange::new(
                    pointer.clone(),
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Constant(i32::MAX as u32),
                )));
        }
    }
    state
}

fn symbolic_call_result(c_type: CType, variable: Variable) -> CValue {
    match c_type {
        CType::Void => CValue::Void,
        CType::Int32 => CValue::Int32(Bitvector32Term::Variable(variable)),
        CType::UInt8 => CValue::UInt8(Bitvector32Term::Variable(variable)),
        CType::Int32Pointer | CType::UInt8Pointer => CValue::Pointer(Pointer::symbolic(variable)),
        CType::Int32Array(_) | CType::UInt8Array(_) => {
            unreachable!("C functions cannot return array values")
        }
    }
}

pub(super) fn add_memory_store_obligation(
    memory: &CMemory,
    pointer: &Pointer,
    value: &CValue,
    mut obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Option<Vec<ProofObligation>> {
    if memory.can_store_concretely(pointer, value) {
        return Some(obligations);
    }

    add_proof_obligation(
        &mut obligations,
        assumptions,
        Proposition::CMemoryCanStore {
            memory: memory.clone(),
            pointer: pointer.clone(),
            byte_width: value.byte_width(),
        },
    )?;
    Some(obligations)
}

pub(super) fn evaluate_c_arguments_paths(
    state: &CState,
    arguments: &[CExpression],
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CArgumentsPath>> {
    let mut paths = vec![CArgumentsPath {
        values: Vec::new(),
        outcome: None,
        facts: Vec::new(),
        obligations: Vec::new(),
    }];

    for argument in arguments {
        let mut next_paths = Vec::new();
        for path in paths {
            if path.outcome.is_some() {
                next_paths.push(path);
                continue;
            }

            let argument_assumptions =
                assumptions_with_path_context(assumptions, &path.facts, &path.obligations);
            for argument_path in
                evaluate_c_expression_paths(state, argument, &argument_assumptions, budget)?
            {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &path.facts,
                    &path.obligations,
                    &argument_path.facts,
                    &argument_path.obligations,
                    assumptions,
                ) else {
                    continue;
                };

                match argument_path.outcome {
                    CExpressionOutcome::Value(value) => {
                        let mut values = path.values.clone();
                        values.push(value);
                        next_paths.push(CArgumentsPath {
                            values,
                            outcome: None,
                            facts,
                            obligations,
                        });
                    }
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                        next_paths.push(CArgumentsPath {
                            values: path.values.clone(),
                            outcome: Some(CFunctionOutcome::UndefinedBehavior(undefined_behavior)),
                            facts,
                            obligations,
                        })
                    }
                    CExpressionOutcome::RuntimeError(error) => next_paths.push(CArgumentsPath {
                        values: path.values.clone(),
                        outcome: Some(CFunctionOutcome::RuntimeError(error)),
                        facts,
                        obligations,
                    }),
                }
            }
        }
        budget.consume_paths(next_paths.len())?;
        paths = next_paths;
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn bind_c_function_arguments(
    caller_state: &CState,
    function: &CFunction,
    values: &[CValue],
) -> Option<CState> {
    let mut callee_state = CState::new()
        .with_memory(caller_state.memory.clone())
        .with_resource_context(caller_state.resources.clone());
    callee_state.counted_populations = caller_state.counted_populations.clone();
    for (parameter, value) in function.parameters().iter().zip(values) {
        let value = coerce_c_null_pointer_constant(value.clone(), parameter.c_type())?;
        callee_state
            .locals
            .set_typed(parameter.name().to_string(), value, parameter.c_type());
    }
    Some(callee_state)
}

fn evaluate_counted_population_body_resources(
    required_resources: &ResourceContext,
    callee_state: &CState,
    definitions: &[CCompositeResourceDefinition],
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceContext, CRuntimeError>> {
    let mut body_resources = ResourceContext::new();
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    for required in required_resources.facts() {
        let (name, arguments) = match required.resource() {
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                (name, arguments)
            }
            CResource::Memory(_) => continue,
        };
        let Some(definition) = definitions
            .iter()
            .find(|definition| definition.name() == name)
        else {
            continue;
        };
        if !definition.is_counted_population() {
            continue;
        }
        if definition.parameters().len() != arguments.len() {
            return Ok(Err(CRuntimeError::FunctionContract(format!(
                "counted population `{name}` received the wrong number of arguments"
            ))));
        }
        let mut population_state = callee_state.clone();
        for (parameter, argument) in definition.parameters().iter().zip(arguments) {
            if parameter.c_type() != argument.c_type() {
                return Ok(Err(CRuntimeError::TypeMismatch));
            }
            population_state.locals.set_typed(
                parameter.name().to_string(),
                argument.clone(),
                parameter.c_type(),
            );
        }
        let Some(body_active) = evaluate_composite_resource_body_condition(
            definition,
            &population_state,
            &evaluation_assumptions,
            budget,
        ) else {
            return Ok(Err(CRuntimeError::FunctionContract(format!(
                "counted population `{name}` body condition is not decidable"
            ))));
        };
        if !body_active {
            continue;
        }
        for contained in definition.contains() {
            let fact = match evaluate_function_resource_spec(
                &population_state,
                contained,
                &evaluation_assumptions,
                budget,
            )? {
                Ok(fact) => fact,
                Err(error) => return Ok(Err(error)),
            };
            if !body_resources.satisfies_fact(&fact, assumptions) {
                body_resources = match body_resources
                    .try_compose_with_facts_delaying_normalization([fact], assumptions)
                {
                    Ok(resources) => resources,
                    Err(error) => return Ok(Err(resource_context_runtime_error(error))),
                };
            }
        }
    }
    Ok(Ok(body_resources))
}

fn prepare_function_resource_transfer(
    caller_state: &CState,
    callee_state: &CState,
    function: &CFunction,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
    preserve_explicit_representation: bool,
) -> ExecutionResult<Result<CFunctionResourceTransfer, CRuntimeError>> {
    let preserve_explicit_representation = preserve_explicit_representation
        && function
            .composite_resource_definitions()
            .iter()
            .any(CCompositeResourceDefinition::is_recursive);
    let required_resources = match evaluate_function_resource_context(
        callee_state,
        function.resource_requires(),
        assumptions,
        budget,
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    let Some(canonical_resources) = expand_all_composite_resource_facts(
        &required_resources,
        function.composite_resource_definitions(),
        callee_state.memory(),
        assumptions,
    ) else {
        return Ok(Err(CRuntimeError::FunctionContract(format!(
            "could not expand required composite resources before call: {required_resources:?}"
        ))));
    };
    let canonical_resources = expand_decidable_composite_resource_frontier(
        &canonical_resources,
        function.composite_resource_definitions(),
        callee_state.memory(),
        assumptions,
    );
    let population_body_resources = match evaluate_counted_population_body_resources(
        &required_resources,
        callee_state,
        function.composite_resource_definitions(),
        assumptions,
        budget,
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    let required_composite_heads = required_resources
        .facts()
        .iter()
        .filter_map(resource_fact_composite_head)
        .collect::<Vec<_>>();
    let caller_composite_heads = caller_state
        .resources()
        .facts()
        .iter()
        .filter_map(resource_fact_composite_head)
        .collect::<Vec<_>>();
    let has_explicit_representation = caller_state.resources().facts().len()
        != required_resources.facts().len()
        || caller_composite_heads != required_composite_heads;
    let mut callee_resources = if preserve_explicit_representation && has_explicit_representation {
        // Proof replay may have opened exactly the recursive branches needed
        // by the body with `observe` or `unfold`. Independent certification
        // must execute from that same definitionally equivalent spelling.
        // The transfer checks below still consume every declared requirement,
        // so this cannot weaken the function contract or affect ordinary
        // calls, which always use the canonical boundary.
        caller_state.resources().clone()
    } else {
        canonical_resources
    };
    for body_resource in population_body_resources.facts() {
        // The population owns its body even while that body is absent from
        // the caller's explicit proof context. Contract execution opens the
        // body internally after the required population unit has established
        // authority; surface proofs still need scoped `open` to use it.
        if !callee_resources.satisfies_fact(body_resource, assumptions) {
            callee_resources = match callee_resources
                .try_compose_with_facts_delaying_normalization([body_resource.clone()], assumptions)
            {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(resource_context_runtime_error(error))),
            };
        }
    }
    if preserve_explicit_representation && has_explicit_representation {
        let viewed_composites = caller_state
            .resources()
            .facts()
            .iter()
            .filter(|fact| matches!(fact, CResourceFact::View(CResource::Composite { .. })))
            .cloned()
            .collect::<Vec<_>>();
        for composite in viewed_composites {
            let singleton = ResourceContext::new().unchecked_with_fact(composite.clone());
            if let Some(expanded) = expand_composite_resource_fact(
                &singleton,
                &composite,
                function.composite_resource_definitions(),
                callee_state.memory(),
                assumptions,
            ) {
                callee_resources =
                    callee_resources.unchecked_with_facts(expanded.facts().iter().cloned());
            }
        }
    }
    let mut required_resource_list = required_resources.facts().to_vec();
    required_resource_list.sort_by_key(resource_fact_transfer_priority);

    let mut return_resources = caller_state.resources().clone();
    for resource in &required_resource_list {
        if matches!(
            resource,
            CResourceFact::View(CResource::Memory(range))
                if range.base().block.starts_with("local:")
                    && caller_state.memory().has_block(&range.base().block)
        ) {
            continue;
        }
        if let CResource::Composite { name, arguments } | CResource::Token { name, arguments } =
            resource.resource()
            && function
                .composite_resource_definitions()
                .iter()
                .any(|definition| definition.is_counted_population() && definition.name() == name)
            && !return_resources.satisfies_fact(resource, assumptions)
            && callee_state
                .counted_population(name, arguments)
                .is_some_and(|count| {
                    assumptions.proves(&Proposition::ConditionIs(
                        ConditionTerm::Bitvector32Equal(
                            Box::new(count.clone()),
                            Box::new(Bitvector32Term::Constant(1)),
                        ),
                        true,
                    ))
                })
        {
            let singleton = ResourceContext::new().unchecked_with_fact(resource.clone());
            let body = match evaluate_counted_population_body_resources(
                &singleton,
                callee_state,
                function.composite_resource_definitions(),
                assumptions,
                budget,
            )? {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(error)),
            };
            let unfolded = body
                .facts()
                .iter()
                .try_fold(return_resources.clone(), |resources, body_resource| {
                    resources.without_fact(body_resource, assumptions)
                });
            if let Some(unfolded) = unfolded {
                return_resources = unfolded;
                continue;
            }
        }
        let Some(resources) = consume_resource_fact_definitionally(
            &return_resources,
            resource,
            function.composite_resource_definitions(),
            caller_state.memory(),
            assumptions,
        ) else {
            return Ok(Err(CRuntimeError::MissingResource {
                resource: resource.clone(),
            }));
        };
        return_resources = resources;
    }
    Ok(Ok(CFunctionResourceTransfer {
        callee_resources,
        caller_resources_after_requirements: return_resources,
    }))
}

fn evaluate_function_return_resources(
    caller_resources_after_requirements: &ResourceContext,
    post_state: &CState,
    function: &CFunction,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceContext, CRuntimeError>> {
    let ensured_resources = match evaluate_function_resource_context(
        post_state,
        function.resource_ensures(),
        assumptions,
        budget,
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    // A view returned to a caller that already owns the same resource does
    // not create another persistent capability. Keeping both spellings would
    // make a later valid mutation or free look as though a stale borrow were
    // still live.
    let newly_ensured_resources = ensured_resources.facts().iter().filter(|fact| {
        !fact.is_view() || !caller_resources_after_requirements.satisfies_fact(fact, assumptions)
    });
    let return_resources = match caller_resources_after_requirements
        .clone()
        .try_compose_with_facts_delaying_normalization(
            newly_ensured_resources.cloned(),
            assumptions,
        ) {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(resource_context_runtime_error(error))),
    };
    let Some(expanded_ensured_resources) = expand_all_composite_resource_facts(
        &ensured_resources,
        function.composite_resource_definitions(),
        post_state.memory(),
        assumptions,
    ) else {
        return Ok(Err(CRuntimeError::FunctionContract(format!(
            "could not expand ensured composite resources after call: {ensured_resources:?}"
        ))));
    };
    let projected_cores = expanded_ensured_resources
        .facts()
        .iter()
        .filter_map(CResourceFact::core)
        .filter(|core| !return_resources.satisfies_fact(core, assumptions))
        .collect::<Vec<_>>();
    // The callee has already certified every ensured composite and its
    // instantiated body. Its duplicable cores are therefore observations of
    // certified ownership, not newly composed ownership that needs another
    // global validity/normalization pass.
    Ok(Ok(return_resources.unchecked_with_facts(projected_cores)))
}

fn counted_population_quantities(
    resources: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    tracked_state: &CState,
    assumptions: &Assumptions,
) -> BTreeMap<(String, Vec<CValue>), u32> {
    let mut quantities = BTreeMap::new();
    for fact in resources.facts() {
        let (name, arguments) = match fact.resource() {
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                (name, arguments)
            }
            CResource::Memory(_) => continue,
        };
        if name == CResourceFact::ALLOCATION_RESOURCE_NAME {
            continue;
        }
        // Ordinary resource counts are derived directly from the held
        // resource context. Only definitions whose bodies mention their
        // population count need a persistent cross-call ledger and a
        // contract transition here.
        let has_declared_population_invariant = definitions
            .iter()
            .any(|definition| definition.is_counted_population() && definition.name() == name);
        let population_is_observed = tracked_state
            .counted_population_proven_equal(name, arguments, assumptions)
            .is_some();
        if !has_declared_population_invariant && !population_is_observed {
            continue;
        }
        let quantity = fact.owned_quantity().unwrap_or(0);
        if quantity == 0 {
            continue;
        }
        let total = quantities
            .entry((name.clone(), arguments.clone()))
            .or_insert(0u32);
        *total = total.saturating_add(quantity);
    }
    quantities
}

#[derive(Default)]
struct CCountedPopulationTransition {
    finalized_body_resources: Vec<CResourceFact>,
    population_facts: Vec<Proposition>,
}

fn apply_counted_population_transition_resources(
    mut resources: ResourceContext,
    transition: &CCountedPopulationTransition,
    _assumptions: &Assumptions,
) -> Result<ResourceContext, CRuntimeError> {
    for resource in &transition.finalized_body_resources {
        for representation in [Some(resource.clone()), resource.core()]
            .into_iter()
            .flatten()
        {
            while resources.facts().contains(&representation) {
                resources = resources
                    .without_exact_representation(&representation)
                    .expect(
                        "an exact finalized population-body representation should be removable",
                    );
            }
        }
    }
    Ok(resources)
}

fn apply_counted_population_transitions(
    caller_state: &CState,
    post_state: &mut CState,
    function: &CFunction,
    argument_values: &[CValue],
    assumptions: &Assumptions,
    obligations: &mut Vec<ProofObligation>,
    reestablish_invariants: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CCountedPopulationTransition, CRuntimeError>> {
    let Some(entry_state) = bind_c_function_arguments(caller_state, function, argument_values)
    else {
        return Ok(Err(CRuntimeError::TypeMismatch));
    };
    let required = match evaluate_function_resource_context(
        &entry_state,
        function.resource_requires(),
        assumptions,
        budget,
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    let post_contract_state = with_contract_argument_views(post_state, function, argument_values);
    let ensured = match evaluate_function_resource_context(
        &post_contract_state,
        function.resource_ensures(),
        assumptions,
        budget,
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    let required_quantities = counted_population_quantities(
        &required,
        function.composite_resource_definitions(),
        caller_state,
        assumptions,
    );
    let ensured_quantities = counted_population_quantities(
        &ensured,
        function.composite_resource_definitions(),
        caller_state,
        assumptions,
    );
    let caller_quantities = counted_population_quantities(
        caller_state.resources(),
        function.composite_resource_definitions(),
        caller_state,
        assumptions,
    );
    let keys = required_quantities
        .keys()
        .chain(ensured_quantities.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut transition = CCountedPopulationTransition::default();
    let mut transition_guaranteed_facts = Vec::new();
    for (name, arguments) in keys {
        let required_quantity = required_quantities
            .get(&(name.clone(), arguments.clone()))
            .copied()
            .unwrap_or(0);
        let ensured_quantity = ensured_quantities
            .get(&(name.clone(), arguments.clone()))
            .copied()
            .unwrap_or(0);
        if required_quantity == ensured_quantity {
            // A resource-neutral contract preserves this exact population.
            // Do not ask general arithmetic reasoning to rediscover
            // `old_count + 0 != 0`; on large proof contexts that turns a
            // constant-time ledger update into an expensive search.
            if caller_state.counted_population(&name, &arguments).is_none() {
                let visible_count = caller_quantities
                    .get(&(name.clone(), arguments.clone()))
                    .copied()
                    .unwrap_or(required_quantity);
                if visible_count > 0 {
                    *post_state = post_state.clone().with_counted_population(
                        name,
                        arguments,
                        Bitvector32Term::Constant(visible_count),
                    );
                }
            }
            continue;
        }
        let consumes_entire_population = ensured_quantity == 0
            && caller_state
                .counted_population(&name, &arguments)
                .is_some_and(|old_count| {
                    assumptions.proves(&Proposition::ConditionIs(
                        ConditionTerm::Bitvector32Equal(
                            Box::new(old_count.clone()),
                            Box::new(Bitvector32Term::Constant(required_quantity)),
                        ),
                        true,
                    ))
                });
        let new_count =
            if let Some(old_count) = caller_state.counted_population(&name, &arguments).cloned() {
                if ensured_quantity >= required_quantity {
                    Bitvector32Term::add(
                        old_count,
                        Bitvector32Term::Constant(ensured_quantity - required_quantity),
                    )
                } else {
                    Bitvector32Term::subtract(
                        old_count,
                        Bitvector32Term::Constant(required_quantity - ensured_quantity),
                    )
                }
            } else if let Some(visible_count) = caller_quantities
                .get(&(name.clone(), arguments.clone()))
                .copied()
            {
                if ensured_quantity >= required_quantity {
                    Bitvector32Term::add(
                        Bitvector32Term::Constant(visible_count),
                        Bitvector32Term::Constant(ensured_quantity - required_quantity),
                    )
                } else {
                    Bitvector32Term::subtract(
                        Bitvector32Term::Constant(visible_count),
                        Bitvector32Term::Constant(required_quantity - ensured_quantity),
                    )
                }
            } else if required_quantity > 0 {
                Bitvector32Term::Constant(ensured_quantity)
            } else if ensured_quantity > 0 {
                Bitvector32Term::Constant(ensured_quantity)
            } else {
                return Ok(Err(CRuntimeError::FunctionContract(format!(
                    "counted population `{name}` is not initialized"
                ))));
            };
        let population_was_initialized =
            caller_state.counted_population(&name, &arguments).is_some()
                || caller_quantities
                    .get(&(name.clone(), arguments.clone()))
                    .is_some_and(|quantity| *quantity > 0)
                || required_quantity > 0;
        let zero = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(new_count.clone()),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );
        let population_ends = consumes_entire_population
            || bitvector_terms_proven_equal_for_memory_resolution(
                &new_count,
                &Bitvector32Term::Constant(0),
                assumptions,
            )
            || assumptions.proves(&zero);
        if population_was_initialized && population_ends {
            *post_state = post_state
                .clone()
                .without_counted_population(&name, &arguments);
            let singleton = ResourceContext::new().unchecked_with_fact(CResourceFact::own(
                CResource::Composite {
                    name: name.clone(),
                    arguments: arguments.clone(),
                },
            ));
            let finalized = match evaluate_counted_population_body_resources(
                &singleton,
                &entry_state,
                function.composite_resource_definitions(),
                assumptions,
                budget,
            )? {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(error)),
            };
            transition
                .finalized_body_resources
                .extend(finalized.facts().iter().cloned());
        } else {
            *post_state = post_state.clone().with_counted_population(
                name.clone(),
                arguments.clone(),
                new_count.clone(),
            );
            // A visible ensured unit witnesses nonemptiness. The transition
            // preserves the population cardinality invariant algebraically:
            // entry count >= required units, then both sides change by the
            // same net contract quantity. Only a population with no locally
            // returned unit needs an explicit proof that unseen units remain.
            if ensured_quantity == 0 {
                obligations.push(
                    ProofObligation::verification_condition(Proposition::ConditionIs(
                        ConditionTerm::Bitvector32SignedGreaterThan(
                            Box::new(new_count),
                            Box::new(Bitvector32Term::Constant(0)),
                        ),
                        true,
                    ))
                    .with_context("resource population remains nonempty"),
                );
            } else {
                // Entry count covers every required unit, and the logical
                // count and returned quantity change by the same contract
                // delta. A returned unit therefore witnesses nonemptiness
                // without another arithmetic proof obligation.
                transition_guaranteed_facts.push(Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedGreaterEqual(
                        Box::new(new_count.clone()),
                        Box::new(Bitvector32Term::Constant(1)),
                    ),
                    true,
                ));
            }
        }
    }

    if !reestablish_invariants {
        return Ok(Ok(transition));
    }

    // Re-establish every active counted population's declared invariant at
    // the post-contract snapshot. The transition changes the logical count;
    // a body fact relating that count to C memory is therefore a genuine
    // verification condition, not an automatically assumed consequence.
    let post_contract_state = with_contract_argument_views(post_state, function, argument_values);
    let active_populations = post_contract_state
        .counted_populations()
        .iter()
        .filter_map(|population| {
            function
                .composite_resource_definitions()
                .iter()
                .any(|definition| {
                    definition.is_counted_population() && definition.name() == population.name
                })
                .then(|| {
                    CResourceFact::own(CResource::Composite {
                        name: population.name.clone(),
                        arguments: population.arguments.clone(),
                    })
                })
        })
        .collect::<Vec<_>>();
    let active_populations = ResourceContext::new().unchecked_with_facts(active_populations);
    let Some(population_facts) = evaluate_counted_population_fact_propositions(
        &active_populations,
        function.composite_resource_definitions(),
        &post_contract_state,
        &Assumptions::new(),
    ) else {
        return Ok(Err(CRuntimeError::FunctionContract(
            "could not evaluate resource population postcondition".to_string(),
        )));
    };
    for proposition in population_facts {
        transition.population_facts.push(proposition.clone());
        if !assumptions.proves(&proposition) && !transition_guaranteed_facts.contains(&proposition)
        {
            obligations.push(
                ProofObligation::verification_condition(proposition)
                    .with_context("resource population invariant"),
            );
        }
    }
    Ok(Ok(transition))
}

fn resource_fact_composite_head(fact: &CResourceFact) -> Option<(bool, &str)> {
    let CResource::Composite { name, .. } = fact.resource() else {
        return None;
    };
    Some((fact.is_own(), name))
}

pub(super) fn prepare_function_contract_entry_state_with_values(
    caller_state: &CState,
    function: &CFunction,
    argument_values: &[CValue],
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CState, CRuntimeError>> {
    let Some(callee_state) = bind_c_function_arguments(caller_state, function, argument_values)
    else {
        return Ok(Err(CRuntimeError::FunctionContract(format!(
            "could not bind contract-entry arguments for {}",
            function.name()
        ))));
    };
    let transfer = match prepare_function_resource_transfer(
        caller_state,
        &callee_state,
        function,
        assumptions,
        budget,
        true,
    )? {
        Ok(transfer) => transfer,
        Err(error) => return Ok(Err(error)),
    };
    Ok(Ok(
        callee_state.with_resource_context(transfer.callee_resources)
    ))
}

pub(super) fn expand_composite_resource_fact(
    context: &ResourceContext,
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &Assumptions,
) -> Option<ResourceContext> {
    expand_composite_resource_fact_with_children(
        context,
        composite,
        definitions,
        memory,
        assumptions,
    )
    .map(|(expanded, _)| expanded)
}

fn expand_composite_resource_fact_with_children(
    context: &ResourceContext,
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &Assumptions,
) -> Option<(ResourceContext, Vec<CResourceFact>)> {
    let CResource::Composite { name, arguments } = composite.resource() else {
        return None;
    };
    let definition = definitions
        .iter()
        .find(|definition| definition.name() == name)?;
    if definition.parameters().len() != arguments.len() {
        return None;
    }
    let expansion_base = context.clone().without_exact_representation(composite)?;
    let mut state = CState::new()
        .with_memory(memory.clone())
        .with_resource_context(expansion_base.clone());
    for (parameter, argument) in definition.parameters().iter().zip(arguments) {
        if parameter.c_type() != argument.c_type() {
            return None;
        }
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.c_type(),
        );
    }
    let mut budget = ExecutionBudget::default();
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    let mut child_facts = Vec::new();
    let Some(body_active) = evaluate_composite_resource_body_condition(
        definition,
        &state,
        &evaluation_assumptions,
        &mut budget,
    ) else {
        // A guarded folded resource remains opaque until the current path
        // decides its condition.
        return Some((context.clone(), Vec::new()));
    };
    for contained in if body_active {
        definition.contains()
    } else {
        &[]
    } {
        let child_result = evaluate_function_resource_spec(
            &state,
            contained,
            &evaluation_assumptions,
            &mut budget,
        );
        let Ok(Ok(child)) = child_result else {
            return None;
        };
        state.resources = state.resources.clone().unchecked_with_fact(child.clone());
        child_facts.push(child);
    }
    let children = ResourceContext::new()
        .try_compose_with_facts(child_facts, assumptions)
        .ok()?;
    let children = if composite.is_own() {
        children.facts().to_vec()
    } else {
        children
            .facts()
            .iter()
            .map(|fact| CResourceFact::View(fact.resource().clone()))
            .collect()
    };
    let mut expanded = expansion_base;
    let missing = children
        .iter()
        .filter(|child| !expanded.facts().contains(child))
        .cloned()
        .collect::<Vec<_>>();
    expanded = expanded
        .try_compose_into_valid_context_delaying_normalization(missing, assumptions)
        .ok()?;
    Some((expanded, children))
}

pub(super) fn evaluate_guarded_contract_condition(
    condition: &SpecProposition,
    state: &CState,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> Option<bool> {
    let paths = lower_spec_proposition_at_state_with_loop_entry(
        state,
        condition,
        None,
        assumptions,
        budget,
    )
    .ok()?;
    let [path] = paths.as_slice() else {
        return None;
    };
    if !path
        .obligations
        .iter()
        .all(|obligation| assumptions.proves(obligation.proposition()))
    {
        return None;
    }
    let proves_body_condition = |proposition: &Proposition| match proposition {
        Proposition::ConditionIs(condition, value) => {
            assumptions.proves_condition_exact_or_snapshot(condition, *value)
                || assumptions.decide(condition) == Some(*value)
        }
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => {
                assumptions.proves_condition_exact_or_snapshot(condition, !*value)
                    || assumptions.decide(condition) == Some(!*value)
            }
            _ => false,
        },
        _ => assumptions.proves_exact(proposition) || assumptions.proves(proposition),
    };
    if proves_body_condition(&path.proposition) {
        return Some(true);
    }
    let false_proposition = match &path.proposition {
        Proposition::ConditionIs(condition, value) => {
            Proposition::ConditionIs(condition.clone(), !value)
        }
        Proposition::Not(body) => body.as_ref().clone(),
        proposition => Proposition::Not(Box::new(proposition.clone())),
    };
    proves_body_condition(&false_proposition).then_some(false)
}

fn evaluate_composite_resource_body_condition(
    definition: &CCompositeResourceDefinition,
    state: &CState,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> Option<bool> {
    definition.condition().map_or(Some(true), |condition| {
        evaluate_guarded_contract_condition(condition, state, assumptions, budget)
    })
}

pub(super) fn expand_all_composite_resource_facts(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &Assumptions,
) -> Option<ResourceContext> {
    expand_composite_resource_context(context, definitions, memory, assumptions)
        .map(|(resources, _)| resources)
}

/// Continues through recursive composites only while their guards are
/// decidable in the current contract path. Unknown branches remain folded.
fn expand_decidable_composite_resource_frontier(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &Assumptions,
) -> ResourceContext {
    let mut expanded = context.clone();
    let mut seen = BTreeSet::new();
    let mut pending = VecDeque::from(
        context
            .facts()
            .iter()
            .filter(|fact| matches!(fact.resource(), CResource::Composite { .. }))
            .cloned()
            .collect::<Vec<_>>(),
    );
    while let Some(composite) = pending.pop_front() {
        if !seen.insert(composite.clone()) || !expanded.facts().contains(&composite) {
            continue;
        }
        let Some(next) =
            expand_composite_resource_fact(&expanded, &composite, definitions, memory, assumptions)
        else {
            continue;
        };
        if next == expanded {
            continue;
        }
        for child in next.facts().iter().filter(|fact| {
            matches!(fact.resource(), CResource::Composite { .. }) && !seen.contains(*fact)
        }) {
            pending.push_back(child.clone());
        }
        expanded = next;
    }
    expanded
}

/// Expands only the folded branches needed to expose `target`, leaving
/// unrelated and deeper recursive resources folded.
pub(super) fn expose_composite_resource_fact(
    context: &ResourceContext,
    target: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &Assumptions,
) -> Option<ResourceContext> {
    let target_is_available = |context: &ResourceContext| {
        context.facts().iter().any(|available| {
            let access_compatible = match (available, target) {
                (
                    CResourceFact::Own(_, available_quantity),
                    CResourceFact::Own(_, target_quantity),
                ) => available_quantity >= target_quantity,
                (CResourceFact::Own(..), CResourceFact::View(_))
                | (CResourceFact::View(_), CResourceFact::View(_)) => true,
                _ => false,
            };
            access_compatible
                && super::assumptions::resources_equal_ignoring_memories(
                    available.resource(),
                    target.resource(),
                )
        })
    };
    if target_is_available(context) {
        return Some(context.clone());
    }

    let mut seen = BTreeSet::new();
    let mut pending = VecDeque::from([context.clone()]);
    while let Some(context) = pending.pop_front() {
        if !seen.insert(context.clone()) {
            continue;
        }
        let composites = context
            .facts()
            .iter()
            .filter(|fact| matches!(fact.resource(), CResource::Composite { .. }))
            .cloned()
            .collect::<Vec<_>>();
        for composite in composites {
            let expanded = expand_composite_resource_fact(
                &context,
                &composite,
                definitions,
                memory,
                assumptions,
            )?;
            if expanded == context {
                continue;
            }
            if target_is_available(&expanded) {
                return Some(expanded);
            }
            pending.push_back(expanded);
        }
    }
    None
}

fn expand_composite_resource_context(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &Assumptions,
) -> Option<(ResourceContext, Vec<CResourceFact>)> {
    let mut expanded = context.clone();
    let mut composites = Vec::new();
    let roots = context
        .facts()
        .iter()
        .filter(|fact| matches!(fact.resource(), CResource::Composite { .. }))
        .cloned()
        .collect::<Vec<_>>();
    for root in roots {
        expanded = expand_composite_resource_tree(
            &expanded,
            &root,
            definitions,
            memory,
            assumptions,
            &[],
            &mut composites,
        )?;
    }
    Some((expanded, composites))
}

fn expand_composite_resource_tree(
    context: &ResourceContext,
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &Assumptions,
    ancestors: &[String],
    composites: &mut Vec<CResourceFact>,
) -> Option<ResourceContext> {
    if !context.facts().contains(composite) {
        return Some(context.clone());
    }
    let CResource::Composite { name, .. } = composite.resource() else {
        return Some(context.clone());
    };
    let definition = definitions
        .iter()
        .find(|definition| definition.name() == name)?;
    if definition.is_recursive() && ancestors.iter().any(|ancestor| ancestor == name) {
        return Some(context.clone());
    }
    let (mut expanded, children) = expand_composite_resource_fact_with_children(
        context,
        composite,
        definitions,
        memory,
        assumptions,
    )?;
    if expanded.facts().contains(composite) {
        return Some(expanded);
    }
    composites.push(composite.clone());
    let mut child_ancestors = ancestors.to_vec();
    child_ancestors.push(name.clone());
    for child in children {
        if matches!(child.resource(), CResource::Composite { .. }) {
            expanded = expand_composite_resource_tree(
                &expanded,
                &child,
                definitions,
                memory,
                assumptions,
                &child_ancestors,
                composites,
            )?;
        }
    }
    Some(expanded)
}

pub(super) fn expand_all_composite_resource_facts_and_propositions(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &Assumptions,
) -> Option<(ResourceContext, Vec<Proposition>)> {
    let (expanded, composites) =
        expand_composite_resource_context(context, definitions, memory, assumptions)?;
    let mut propositions = Vec::new();
    for composite in composites {
        propositions.extend(evaluate_composite_resource_relation_propositions(
            &composite,
            definitions,
            memory,
            assumptions,
        )?);
        let fact_assumptions = assumptions_with_propositions(assumptions, &propositions);
        propositions.extend(evaluate_composite_resource_fact_propositions(
            &composite,
            definitions,
            memory,
            &expanded,
            &fact_assumptions,
        )?);
    }
    Some((expanded, propositions))
}

pub(super) fn evaluate_counted_population_fact_propositions(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    state: &CState,
    assumptions: &Assumptions,
) -> Option<Vec<Proposition>> {
    let mut populations = BTreeMap::<(String, Vec<CValue>), u32>::new();
    for fact in context.facts() {
        let (name, arguments) = match fact.resource() {
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                (name, arguments)
            }
            CResource::Memory(_) => continue,
        };
        let quantity = fact.owned_quantity().unwrap_or(0);
        let entry = populations
            .entry((name.clone(), arguments.clone()))
            .or_default();
        *entry = entry.saturating_add(quantity);
    }
    let mut propositions = Vec::new();
    for ((name, arguments), visible_quantity) in populations {
        let Some(definition) = definitions
            .iter()
            .find(|definition| definition.name() == name)
        else {
            continue;
        };
        if definition.parameters().len() != arguments.len() {
            return None;
        }
        let population_count = state.counted_population(&name, &arguments);
        if visible_quantity > 0
            && let Some(population_count) = population_count
        {
            propositions.push(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedGreaterEqual(
                    Box::new(population_count.clone()),
                    Box::new(Bitvector32Term::Constant(visible_quantity)),
                ),
                true,
            ));
        }
        // Every declared resource has a population count, but ordinary body
        // facts are handled by composite expansion above. Only a definition
        // whose body invariant observes its population count needs this
        // additional invariant evaluation. In particular, do not force an
        // undecided conditional body before certification enumerates its
        // guard cases.
        if !definition.is_counted_population() {
            continue;
        }
        if population_count.is_none() {
            return None;
        }
        let mut population_state = state.clone();
        for (parameter, argument) in definition.parameters().iter().zip(&arguments) {
            if parameter.c_type() != argument.c_type() {
                return None;
            }
            population_state.locals.set_typed(
                parameter.name().to_string(),
                argument.clone(),
                parameter.c_type(),
            );
        }
        let mut budget = ExecutionBudget::default();
        let evaluation_assumptions = assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .prefer_symbolic_external_loads();
        if !evaluate_composite_resource_body_condition(
            definition,
            &population_state,
            &evaluation_assumptions,
            &mut budget,
        )? {
            continue;
        }
        // Definition facts are justified by the population body, even while
        // that body is opaque in the surface proof context. Expose the body
        // only in this kernel-local state so heap-dependent invariants can
        // discharge their own loadability obligations.
        for contained in definition.contains() {
            let body_resource = evaluate_function_resource_spec(
                &population_state,
                contained,
                &evaluation_assumptions,
                &mut budget,
            )
            .ok()?
            .ok()?;
            if !population_state
                .resources
                .satisfies_fact(&body_resource, &evaluation_assumptions)
            {
                population_state.resources = population_state
                    .resources
                    .try_compose_with_facts_delaying_normalization(
                        [body_resource],
                        &evaluation_assumptions,
                    )
                    .ok()?;
            }
        }
        let mut fact_assumptions = assumptions.clone();
        let mut pending = definition.facts().iter().collect::<Vec<_>>();
        while !pending.is_empty() {
            let mut next_pending = Vec::new();
            let mut made_progress = false;
            for population_fact in pending {
                let evaluation_assumptions = fact_assumptions
                    .clone()
                    .allow_symbolic_contract_loads()
                    .prefer_symbolic_external_loads();
                let Ok(paths) = lower_spec_proposition_at_state_with_loop_entry(
                    &population_state,
                    population_fact,
                    None,
                    &evaluation_assumptions,
                    &mut budget,
                ) else {
                    return None;
                };
                let [path] = paths.as_slice() else {
                    next_pending.push(population_fact);
                    continue;
                };
                if !path.obligations.iter().all(|obligation| {
                    if fact_assumptions.proves(obligation.proposition()) {
                        return true;
                    }
                    let Proposition::CMemoryLoadable {
                        memory: obligation_memory,
                        base,
                        bytes,
                    } = obligation.proposition()
                    else {
                        return false;
                    };
                    memory_snapshots_proven_equal_at_pointer(
                        obligation_memory,
                        population_state.memory(),
                        base,
                        &fact_assumptions,
                    ) && bytes.as_const().is_some_and(|bytes| {
                        resource_context_has_read(
                            population_state.resources(),
                            base,
                            bytes,
                            &fact_assumptions,
                        )
                    })
                }) {
                    next_pending.push(population_fact);
                    continue;
                }
                for obligation in &path.obligations {
                    fact_assumptions =
                        fact_assumptions.assume_proposition(obligation.proposition().clone());
                }
                for path_fact in &path.facts {
                    let proposition = path_fact.proposition().clone();
                    if !propositions.contains(&proposition) {
                        propositions.push(proposition.clone());
                    }
                    fact_assumptions = fact_assumptions.assume_proposition(proposition);
                }
                if !propositions.contains(&path.proposition) {
                    propositions.push(path.proposition.clone());
                }
                fact_assumptions = fact_assumptions.assume_proposition(path.proposition.clone());
                made_progress = true;
            }
            if !made_progress {
                return None;
            }
            pending = next_pending;
        }
    }
    Some(propositions)
}

pub(super) fn evaluate_composite_resource_relation_propositions(
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &Assumptions,
) -> Option<Vec<Proposition>> {
    let CResource::Composite { name, arguments } = composite.resource() else {
        return None;
    };
    let definition = definitions
        .iter()
        .find(|definition| definition.name() == name)?;
    if definition.parameters().len() != arguments.len() {
        return None;
    }
    let mut state = CState::new().with_memory(memory.clone());
    for (parameter, argument) in definition.parameters().iter().zip(arguments) {
        if parameter.c_type() != argument.c_type() {
            return None;
        }
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.c_type(),
        );
    }
    let mut budget = ExecutionBudget::default();
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    let mut children = Vec::new();
    let body_active = evaluate_composite_resource_body_condition(
        definition,
        &state,
        &evaluation_assumptions,
        &mut budget,
    )?;
    for contained in if body_active {
        definition.contains()
    } else {
        &[]
    } {
        let child_result = evaluate_function_resource_spec(
            &state,
            contained,
            &evaluation_assumptions,
            &mut budget,
        );
        let Ok(Ok(child)) = child_result else {
            return None;
        };
        state.resources = state.resources.clone().unchecked_with_fact(child.clone());
        if composite.is_own()
            && let Some(child) = child.owned_resource()
        {
            children.push(child.clone());
        }
    }
    let mut propositions = Vec::new();
    for child in &children {
        propositions.push(Proposition::CResourceContains {
            parent: composite.resource().clone(),
            child: child.clone(),
        });
    }
    for index in 0..children.len() {
        for right in &children[index + 1..] {
            propositions.push(Proposition::CResourceSeparate {
                left: children[index].clone(),
                right: right.clone(),
            });
        }
    }
    Some(propositions)
}

fn evaluate_composite_resource_fact_propositions(
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    resources: &ResourceContext,
    assumptions: &Assumptions,
) -> Option<Vec<Proposition>> {
    let CResource::Composite { name, arguments } = composite.resource() else {
        return None;
    };
    let definition = definitions
        .iter()
        .find(|definition| definition.name() == name)?;
    if definition.parameters().len() != arguments.len() {
        return None;
    }
    let mut state = CState::new()
        .with_memory(memory.clone())
        .with_resource_context(resources.clone());
    for (parameter, argument) in definition.parameters().iter().zip(arguments) {
        if parameter.c_type() != argument.c_type() {
            return None;
        }
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.c_type(),
        );
    }
    let mut result = Vec::new();
    let mut budget = ExecutionBudget::default();
    let mut fact_assumptions = assumptions.clone();
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    if !evaluate_composite_resource_body_condition(
        definition,
        &state,
        &evaluation_assumptions,
        &mut budget,
    )? {
        return Some(result);
    }
    let mut pending = definition.facts().iter().collect::<Vec<_>>();
    while !pending.is_empty() {
        let mut next_pending = Vec::new();
        let mut made_progress = false;
        for fact in pending {
            let evaluation_assumptions = fact_assumptions
                .clone()
                .allow_symbolic_contract_loads()
                .prefer_symbolic_external_loads();
            let Ok(paths) = lower_spec_proposition_at_state_with_loop_entry(
                &state,
                fact,
                None,
                &evaluation_assumptions,
                &mut budget,
            ) else {
                return None;
            };
            let [path] = paths.as_slice() else {
                next_pending.push(fact);
                continue;
            };
            if !path.obligations.iter().all(|obligation| {
                if fact_assumptions.proves(obligation.proposition()) {
                    return true;
                }
                let Proposition::CMemoryLoadable {
                    memory: obligation_memory,
                    base,
                    bytes,
                } = obligation.proposition()
                else {
                    return false;
                };
                memory_snapshots_proven_equal_at_pointer(
                    obligation_memory,
                    memory,
                    base,
                    &fact_assumptions,
                ) && bytes.as_const().is_some_and(|bytes| {
                    resource_context_has_read(resources, base, bytes, &fact_assumptions)
                })
            }) {
                next_pending.push(fact);
                continue;
            }
            for obligation in &path.obligations {
                fact_assumptions =
                    fact_assumptions.assume_proposition(obligation.proposition().clone());
            }
            for path_fact in &path.facts {
                let proposition = path_fact.proposition().clone();
                if !result.contains(&proposition) {
                    result.push(proposition.clone());
                }
                fact_assumptions = fact_assumptions.assume_proposition(proposition);
            }
            if !result.contains(&path.proposition) {
                result.push(path.proposition.clone());
            }
            fact_assumptions = fact_assumptions.assume_proposition(path.proposition.clone());
            made_progress = true;
        }
        if !made_progress {
            return None;
        }
        pending = next_pending;
    }
    Some(result)
}

pub(super) fn resource_context_satisfies_definitional_fact(
    available: &ResourceContext,
    required: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &Assumptions,
) -> bool {
    if available.satisfies_fact(required, assumptions) {
        return true;
    }
    let Some(available) =
        expand_all_composite_resource_facts(available, definitions, memory, assumptions)
    else {
        return false;
    };
    let required_context = ResourceContext::new().unchecked_with_fact(required.clone());
    let Some(required) =
        expand_all_composite_resource_facts(&required_context, definitions, memory, assumptions)
    else {
        return false;
    };
    required
        .facts()
        .iter()
        .all(|fact| available.satisfies_fact(fact, assumptions))
}

/// True when every element of a constant-bounded memory range is concretely
/// loadable, so a view of it is represented by the materialized cells rather
/// than a resource fact.
fn view_range_concretely_loadable(memory: &CMemory, range: &CMemoryRange) -> bool {
    let (Some(start), Some(end)) = (range.start().as_const(), range.end().as_const()) else {
        return false;
    };
    if end <= start || end - start > 64 {
        return false;
    }
    let width = match &range.base().offset {
        PointerOffsetTerm::Int32Scaled { byte_width, .. } => {
            u32::try_from(*byte_width).unwrap_or(4)
        }
        _ => 4,
    };
    (start..end).all(|index| {
        let pointer = Pointer {
            block: range.base().block.clone(),
            offset: PointerOffsetTerm::add(
                range.base().offset.clone(),
                PointerOffsetTerm::scale_int32(Bitvector32Term::Constant(index), i64::from(width)),
            ),
        };
        memory.is_loadable_concretely(&pointer, width)
    })
}

fn consume_resource_fact_definitionally(
    available: &ResourceContext,
    required: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &Assumptions,
) -> Option<ResourceContext> {
    fn consume(
        available: &ResourceContext,
        required: &CResourceFact,
        definitions: &[CCompositeResourceDefinition],
        memory: &CMemory,
        assumptions: &Assumptions,
        seen: &mut BTreeSet<(ResourceContext, CResourceFact)>,
    ) -> Option<ResourceContext> {
        if !seen.insert((available.clone(), required.clone())) {
            return None;
        }
        // A view of memory the caller has concretely materialized is freely
        // satisfiable: read access is represented by the materialized cells,
        // mirroring the local-block view rule at call transfer.
        if let CResourceFact::View(CResource::Memory(range)) = required
            && view_range_concretely_loadable(memory, range)
        {
            return Some(available.clone());
        }
        if let Some(remaining) = available
            .clone()
            .without_fact_delaying_normalization(required, assumptions)
        {
            return Some(remaining);
        }
        let normalized = available.clone().normalized(assumptions);
        if &normalized != available
            && let Some(remaining) =
                normalized.without_fact_delaying_normalization(required, assumptions)
        {
            return Some(remaining);
        }

        let required_context = ResourceContext::new().unchecked_with_fact(required.clone());
        if let Some(expanded_required) = expand_composite_resource_fact(
            &required_context,
            required,
            definitions,
            memory,
            assumptions,
        ) {
            let mut remaining = available.clone();
            for child in expanded_required.facts() {
                remaining = consume(&remaining, child, definitions, memory, assumptions, seen)?;
            }
            return Some(remaining);
        }

        for composite in available
            .facts()
            .iter()
            .filter(|fact| matches!(fact.resource(), CResource::Composite { .. }))
        {
            let Some(expanded_available) = expand_composite_resource_fact(
                available,
                composite,
                definitions,
                memory,
                assumptions,
            ) else {
                continue;
            };
            if let Some(remaining) = consume(
                &expanded_available,
                required,
                definitions,
                memory,
                assumptions,
                seen,
            ) {
                return Some(remaining);
            }
        }
        None
    }

    consume(
        available,
        required,
        definitions,
        memory,
        assumptions,
        &mut BTreeSet::new(),
    )
}

pub(super) fn resource_context_definitionally_contains(
    available: &ResourceContext,
    required: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &Assumptions,
) -> bool {
    let mut remaining = available.clone();
    let mut required = required.facts().to_vec();
    required.sort_by_key(resource_fact_transfer_priority);
    for fact in &required {
        let Some(next) = consume_resource_fact_definitionally(
            &remaining,
            fact,
            definitions,
            memory,
            assumptions,
        ) else {
            return false;
        };
        remaining = next;
    }
    true
}

pub(super) fn resource_contexts_definitionally_equivalent_by_consumption(
    left: &ResourceContext,
    right: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &Assumptions,
) -> bool {
    resource_context_definitionally_contains(left, right, definitions, memory, assumptions)
        && resource_context_definitionally_contains(right, left, definitions, memory, assumptions)
}

pub(super) fn evaluate_function_resource_context(
    state: &CState,
    resources: &[CResourceSpec],
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceContext, CRuntimeError>> {
    let mut context = ResourceContext::new();
    for resource in resources {
        let evaluation_state = state.clone().with_resource_context(
            state
                .resources()
                .clone()
                .unchecked_with_facts(context.facts().iter().cloned()),
        );
        let resource = match evaluate_function_resource_spec(
            &evaluation_state,
            resource,
            assumptions,
            budget,
        )? {
            Ok(resource) => resource,
            Err(error) => return Ok(Err(error)),
        };
        context = match context.try_compose_with_fact(resource, assumptions) {
            Ok(context) => context,
            Err(error) => return Ok(Err(resource_context_runtime_error(error))),
        };
    }
    Ok(Ok(context))
}

fn resource_context_runtime_error(error: ResourceContextValidityError) -> CRuntimeError {
    match error {
        ResourceContextValidityError::DuplicateOwnedResourceFact(resource) => {
            CRuntimeError::DuplicateResource { resource }
        }
        ResourceContextValidityError::OverlappingWriteResources { left, right } => {
            CRuntimeError::OverlappingWriteResources {
                left: Box::new(left),
                right: Box::new(right),
            }
        }
    }
}

pub(super) fn evaluate_function_resource_spec(
    state: &CState,
    resource: &CResourceSpec,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CResourceFact, CRuntimeError>> {
    match resource {
        CResourceSpec::Read(segment) => {
            let segment = match evaluate_loop_effect_segment(state, segment, assumptions, budget)? {
                Ok(segment) => segment,
                Err(_) => {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "could not evaluate a read resource segment".to_string(),
                    )));
                }
            };
            Ok(Ok(CResourceFact::view_memory(CMemoryRange::new(
                segment.base,
                segment.start,
                segment.end,
            ))))
        }
        CResourceSpec::Write(segment) => {
            let segment = match evaluate_loop_effect_segment(state, segment, assumptions, budget)? {
                Ok(segment) => segment,
                Err(_) => {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "could not evaluate a write resource segment".to_string(),
                    )));
                }
            };
            Ok(Ok(CResourceFact::own_memory(CMemoryRange::new(
                segment.base,
                segment.start,
                segment.end,
            ))))
        }
        CResourceSpec::Composite {
            access,
            name,
            arguments,
            parameter_types,
        } => evaluate_function_declared_resource_spec(
            state,
            *access,
            ResourceFamily::Composite,
            name,
            arguments,
            parameter_types,
            assumptions,
            budget,
        ),
        CResourceSpec::Token {
            access,
            name,
            arguments,
            parameter_types,
        } => evaluate_function_declared_resource_spec(
            state,
            *access,
            ResourceFamily::Token,
            name,
            arguments,
            parameter_types,
            assumptions,
            budget,
        ),
    }
}

fn evaluate_function_declared_resource_spec(
    state: &CState,
    access: CResourceAccessMode,
    family: ResourceFamily,
    name: &str,
    arguments: &[CExpression],
    parameter_types: &[CType],
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CResourceFact, CRuntimeError>> {
    if arguments.len() != parameter_types.len() {
        return Ok(Err(CRuntimeError::FunctionContract(format!(
            "resource `{name}` received the wrong number of arguments"
        ))));
    }
    let mut values = Vec::new();
    for (index, (argument, parameter_type)) in arguments.iter().zip(parameter_types).enumerate() {
        let allocation_element_count = (name == CResourceFact::ALLOCATION_RESOURCE_NAME
            && index == 1)
            .then(|| match argument {
                CExpression::Multiply(left, right)
                    if right.as_ref() == &CExpression::Value(int32(CType::Int32.byte_width())) =>
                {
                    Some(left.as_ref())
                }
                CExpression::Multiply(left, right)
                    if left.as_ref() == &CExpression::Value(int32(CType::Int32.byte_width())) =>
                {
                    Some(right.as_ref())
                }
                _ => None,
            })
            .flatten();
        let value = if let Some(element_count) = allocation_element_count {
            let count = match evaluate_loop_effect_segment_value(
                state,
                element_count,
                assumptions,
                &format!("resource `{name}` argument {index} element count"),
                budget,
            )? {
                Ok(CValue::Int32(count)) => count,
                Ok(_) | Err(_) => {
                    return Ok(Err(CRuntimeError::FunctionContract(format!(
                        "resource `{name}` has an invalid allocation element count"
                    ))));
                }
            };
            int32(Bitvector32Term::multiply(
                count,
                Bitvector32Term::Constant(CType::Int32.byte_width()),
            ))
        } else {
            match evaluate_loop_effect_segment_value(
                state,
                argument,
                assumptions,
                &format!("resource `{name}` argument {index}"),
                budget,
            )? {
                Ok(value) => value,
                Err(error) => {
                    return Ok(Err(CRuntimeError::FunctionContract(format!(
                        "could not evaluate resource `{name}` argument {index}: {error}"
                    ))));
                }
            }
        };
        if !parameter_type.accepts(&value) {
            return Ok(Err(CRuntimeError::FunctionContract(format!(
                "resource `{name}` argument {index} has the wrong type"
            ))));
        }
        values.push(value);
    }
    let resource = match family {
        ResourceFamily::Composite => CResource::Composite {
            name: name.to_string(),
            arguments: values,
        },
        ResourceFamily::Token => CResource::Token {
            name: name.to_string(),
            arguments: values,
        },
        ResourceFamily::Memory => {
            return Ok(Err(CRuntimeError::FunctionContract(
                "declared resources cannot use the raw memory family".to_string(),
            )));
        }
    };
    Ok(Ok(match access {
        CResourceAccessMode::Own => CResourceFact::own(resource),
        CResourceAccessMode::View => CResourceFact::View(resource),
    }))
}

fn resource_fact_transfer_priority(resource: &CResourceFact) -> u8 {
    match resource {
        CResourceFact::View(_) => 0,
        CResourceFact::Own(CResource::Memory(_), _) => 1,
        CResourceFact::Own(CResource::Composite { .. } | CResource::Token { .. }, _) => 2,
    }
}

fn unreturned_allocation_obligation(
    actual_state: &CState,
    returned_resources: &ResourceContext,
    function: &CFunction,
    assumptions: &Assumptions,
) -> Result<Option<CResourceFact>, CRuntimeError> {
    let Some(actual) = expand_all_composite_resource_facts(
        actual_state.resources(),
        function.composite_resource_definitions(),
        actual_state.memory(),
        assumptions,
    ) else {
        return Err(CRuntimeError::FunctionContract(
            "could not inspect allocation obligations at function return".to_string(),
        ));
    };
    let mut budget = ExecutionBudget::default();
    let population_bodies = match evaluate_counted_population_body_resources(
        returned_resources,
        actual_state,
        function.composite_resource_definitions(),
        assumptions,
        &mut budget,
    ) {
        Ok(Ok(resources)) => resources,
        Ok(Err(error)) => return Err(error),
        Err(limit) => {
            return Err(CRuntimeError::FunctionContract(format!(
                "counted population allocation inspection hit execution limit {limit:?}"
            )));
        }
    };
    let returned_resources = returned_resources
        .clone()
        .unchecked_with_facts(population_bodies.facts().iter().cloned());
    Ok(actual
        .facts()
        .iter()
        .filter(|fact| fact.allocation().is_some())
        .find(|allocation| {
            expose_composite_resource_fact(
                &returned_resources,
                allocation,
                function.composite_resource_definitions(),
                actual_state.memory(),
                assumptions,
            )
            .is_none()
        })
        .cloned())
}

pub(crate) fn unreturned_allocation_at_function_exit(
    state: &CState,
    value: &CValue,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<Option<CResourceFact>, CRuntimeError>> {
    let function_can_package_allocation =
        function
            .composite_resource_definitions()
            .iter()
            .any(|definition| {
                definition.contains().iter().any(|resource| {
                    matches!(
                        resource,
                        CResourceSpec::Token { name, .. }
                            if name == CResourceFact::ALLOCATION_RESOURCE_NAME
                    )
                })
            });
    if !function_can_package_allocation
        && !state
            .resources()
            .facts()
            .iter()
            .any(|fact| fact.allocation().is_some())
    {
        return Ok(Ok(None));
    }
    let Some(actual_resources) = expand_all_composite_resource_facts(
        state.resources(),
        function.composite_resource_definitions(),
        state.memory(),
        assumptions,
    ) else {
        return Ok(Err(CRuntimeError::FunctionContract(
            "could not inspect allocation obligations at function exit".to_string(),
        )));
    };
    if !actual_resources
        .facts()
        .iter()
        .any(|fact| fact.allocation().is_some())
    {
        return Ok(Ok(None));
    }
    let Some(argument_values) = arguments
        .iter()
        .map(|argument| match argument {
            CExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(Err(CRuntimeError::FunctionContract(
            "allocation-lifetime checking requires concrete symbolic contract arguments"
                .to_string(),
        )));
    };
    let mut output_state = with_contract_argument_views(state, function, &argument_values);
    if function.return_type() != CType::Void {
        output_state
            .locals
            .set_typed("result".to_string(), value.clone(), function.return_type());
    }
    let returned_resources = match evaluate_function_resource_context(
        &output_state,
        function.resource_ensures(),
        assumptions,
        budget,
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    Ok(unreturned_allocation_obligation(
        &output_state,
        &returned_resources,
        function,
        assumptions,
    ))
}

#[allow(clippy::too_many_arguments)]
fn function_outcome_from_body_with_population_transition(
    caller_state: &CState,
    function: &CFunction,
    outcome: CStatementOutcome,
    mut obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
    argument_values: &[CValue],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<(CFunctionOutcome, Vec<ProofObligation>)> {
    let CStatementOutcome::Return { value, mut state } = outcome else {
        return Ok(function_outcome_from_body(
            caller_state,
            function,
            outcome,
            obligations,
            assumptions,
            None,
        ));
    };
    let Some(value) =
        coerce_c_value_to_type(value, function.return_type(), &mut obligations, assumptions)
    else {
        return Ok((
            CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                "{} returned a value that does not match its declared type",
                function.name()
            ))),
            obligations,
        ));
    };
    if function.return_type() != CType::Void {
        state
            .locals
            .set_typed("result".to_string(), value.clone(), function.return_type());
    }
    if let Err(error) = apply_counted_population_transitions(
        caller_state,
        &mut state,
        function,
        argument_values,
        assumptions,
        &mut obligations,
        true,
        budget,
    )? {
        return Ok((CFunctionOutcome::RuntimeError(error), obligations));
    }
    Ok(function_outcome_from_body(
        caller_state,
        function,
        CStatementOutcome::Return { value, state },
        obligations,
        assumptions,
        None,
    ))
}

#[allow(clippy::too_many_arguments)]
fn function_outcome_from_body_with_resource_transfer(
    caller_state: &CState,
    function: &CFunction,
    outcome: CStatementOutcome,
    mut obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
    transfer: &CFunctionResourceTransfer,
    argument_values: &[CValue],
    reestablish_population_invariants: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<(CFunctionOutcome, Vec<ProofObligation>)> {
    let CStatementOutcome::Return { value, mut state } = outcome else {
        return Ok(function_outcome_from_body(
            caller_state,
            function,
            outcome,
            obligations,
            assumptions,
            None,
        ));
    };
    let Some(value) =
        coerce_c_value_to_type(value, function.return_type(), &mut obligations, assumptions)
    else {
        return Ok((
            CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                "{} returned a value that does not match its declared type",
                function.name()
            ))),
            obligations,
        ));
    };

    if function.return_type() != CType::Void {
        state
            .locals
            .set_typed("result".to_string(), value.clone(), function.return_type());
    }
    let population_transition = match apply_counted_population_transitions(
        caller_state,
        &mut state,
        function,
        argument_values,
        assumptions,
        &mut obligations,
        reestablish_population_invariants,
        budget,
    )? {
        Ok(transition) => transition,
        Err(error) => return Ok((CFunctionOutcome::RuntimeError(error), obligations)),
    };
    let caller_resources_after_requirements = match apply_counted_population_transition_resources(
        transfer.caller_resources_after_requirements.clone(),
        &population_transition,
        assumptions,
    ) {
        Ok(resources) => resources,
        Err(error) => return Ok((CFunctionOutcome::RuntimeError(error), obligations)),
    };
    let output_resource_state = with_contract_argument_views(&state, function, argument_values);
    let return_resources = match evaluate_function_return_resources(
        &caller_resources_after_requirements,
        &output_resource_state,
        function,
        assumptions,
        budget,
    )? {
        Ok(resources) => resources,
        Err(CRuntimeError::TypeMismatch) => {
            return Ok((
                CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "could not evaluate {} return resources",
                    function.name()
                ))),
                obligations,
            ));
        }
        Err(error) => return Ok((CFunctionOutcome::RuntimeError(error), obligations)),
    };
    match unreturned_allocation_obligation(&state, &return_resources, function, assumptions) {
        Ok(Some(allocation)) => {
            return Ok((
                CFunctionOutcome::RuntimeError(CRuntimeError::LiveAllocationLeak { allocation }),
                obligations,
            ));
        }
        Err(error) => return Ok((CFunctionOutcome::RuntimeError(error), obligations)),
        Ok(None) => {}
    }

    let mut return_state = caller_state.clone();
    return_state.memory = state.memory;
    return_state.resources = return_resources;
    return_state.counted_populations = state.counted_populations;
    Ok((
        CFunctionOutcome::Return {
            value,
            state: return_state,
        },
        obligations,
    ))
}

pub(super) fn apply_verified_contract_resource_transition(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    outcome: CFunctionOutcome,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(CFunctionOutcome, Vec<ProofObligation>), CRuntimeError>> {
    let Some(argument_values) = arguments
        .iter()
        .map(|argument| match argument {
            CExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(Err(CRuntimeError::FunctionContract(
            "contract resource transition requires symbolic value arguments".to_string(),
        )));
    };
    let Some(callee_state) = bind_c_function_arguments(caller_state, function, &argument_values)
    else {
        return Ok(Err(CRuntimeError::TypeMismatch));
    };
    let transfer = match prepare_function_resource_transfer(
        caller_state,
        &callee_state,
        function,
        assumptions,
        budget,
        true,
    )? {
        Ok(transfer) => transfer,
        Err(error) => return Ok(Err(error)),
    };
    let statement_outcome = match outcome {
        CFunctionOutcome::Return { value, state } => CStatementOutcome::Return { value, state },
        CFunctionOutcome::VerificationDiverges => {
            return Ok(Ok((CFunctionOutcome::VerificationDiverges, Vec::new())));
        }
        CFunctionOutcome::UndefinedBehavior(error) => {
            return Ok(Ok((CFunctionOutcome::UndefinedBehavior(error), Vec::new())));
        }
        CFunctionOutcome::RuntimeError(error) => return Ok(Err(error)),
    };
    let (outcome, obligations) = function_outcome_from_body_with_resource_transfer(
        caller_state,
        function,
        statement_outcome,
        Vec::new(),
        assumptions,
        &transfer,
        &argument_values,
        false,
        budget,
    )?;
    match outcome {
        CFunctionOutcome::RuntimeError(error) => Ok(Err(error)),
        outcome => Ok(Ok((outcome, obligations))),
    }
}

pub(super) fn function_outcome_from_body(
    caller_state: &CState,
    function: &CFunction,
    outcome: CStatementOutcome,
    mut obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
    return_resources: Option<&ResourceContext>,
) -> (CFunctionOutcome, Vec<ProofObligation>) {
    match outcome {
        CStatementOutcome::Return { value, state } => {
            let Some(value) = coerce_c_value_to_type(
                value,
                function.return_type(),
                &mut obligations,
                assumptions,
            ) else {
                return (
                    CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                        "{} returned a value that does not match its declared type",
                        function.name()
                    ))),
                    obligations,
                );
            };

            let mut caller_state = caller_state.clone();
            caller_state.memory = state.memory;
            caller_state.resources = return_resources.cloned().unwrap_or(state.resources);
            caller_state.counted_populations = state.counted_populations;
            (
                CFunctionOutcome::Return {
                    value,
                    state: caller_state,
                },
                obligations,
            )
        }
        CStatementOutcome::Normal(_) => (
            CFunctionOutcome::RuntimeError(CRuntimeError::MissingReturn),
            obligations,
        ),
        CStatementOutcome::VerificationDiverges => {
            (CFunctionOutcome::VerificationDiverges, obligations)
        }
        CStatementOutcome::UndefinedBehavior(undefined_behavior) => (
            CFunctionOutcome::UndefinedBehavior(undefined_behavior),
            obligations,
        ),
        CStatementOutcome::RuntimeError(error) => {
            (CFunctionOutcome::RuntimeError(error), obligations)
        }
    }
}

impl From<u32> for Bitvector32Term {
    fn from(value: u32) -> Self {
        Self::Constant(value)
    }
}

impl From<bool> for ConditionTerm {
    fn from(value: bool) -> Self {
        Self::Constant(value)
    }
}
