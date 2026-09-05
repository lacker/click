use super::prelude::*;
use std::collections::VecDeque;
#[derive(Clone, Debug, Eq, PartialEq)]
struct CFunctionResourceTransfer {
    callee_resources: ResourceContext,
    caller_resources_after_requirements: ResourceContext,
}

#[derive(Clone, Debug)]
enum VerifiedAllocationDeltaError {
    Runtime(CRuntimeError),
    InconsistentReturnedAllocation,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum AllocationContinuity {
    Same,
    Distinct,
    Undecided(ConditionTerm),
    Inconsistent,
}

fn lower_memory_range_under_assumptions(
    range: CMemoryRange,
    assumptions: &PureFactContext,
) -> CMemoryRange {
    assumptions.lower_memory_range_under_assumptions(&range)
}

fn function_needs_outcome_resource_transfer(function: &CFunction) -> bool {
    !function.resource_constructors().is_empty()
        || function
            .composite_resource_definitions()
            .iter()
            .any(CCompositeResourceDefinition::needs_outcome_resource_transfer)
}

fn function_changes_declared_resource_quantities(function: &CFunction) -> bool {
    function.resource_requires() != function.resource_ensures()
}

/// Applies one explicitly authorized abstract-token construction to a return
/// state. Construction is a zero-source resource event: unlike a transfer,
/// it does not consume a caller resource or rely on a body representation.
pub(super) fn construct_c_function_resource(
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    result: &CValue,
    constructed: &CResourceFact,
    assumptions: &PureFactContext,
) -> ExecutionResult<Result<CState, CRuntimeError>> {
    let Some(mut evaluation_state) = c_function_entry_state(state, function, arguments) else {
        return Ok(Err(CRuntimeError::FunctionContract(
            "could not bind function arguments for resource construction".to_string(),
        )));
    };
    if function.return_type() != CType::Void {
        set_function_result(&mut evaluation_state, function, result.clone());
    }
    let mut budget = ExecutionBudget::default();
    let mut authorized = false;
    for specification in function.resource_constructors() {
        let candidate = match evaluate_function_resource_spec(
            &evaluation_state,
            specification,
            assumptions,
            &mut budget,
        )? {
            Ok(candidate) => candidate,
            Err(error) => return Ok(Err(error)),
        };
        if candidate == *constructed {
            authorized = true;
            break;
        }
    }
    if !authorized {
        return Ok(Err(CRuntimeError::FunctionContract(
            "resource construction is not authorized by the function contract".to_string(),
        )));
    }
    let CResourceFact::Own(CResource::Token { .. }, quantity) = constructed else {
        return Ok(Err(CRuntimeError::FunctionContract(
            "resource construction requires one owned abstract token".to_string(),
        )));
    };
    if quantity.as_const() != Some(1) {
        return Ok(Err(CRuntimeError::FunctionContract(
            "resource construction creates exactly one token".to_string(),
        )));
    }
    if state.resources().contains_exact_representation(constructed) {
        return Ok(Err(CRuntimeError::FunctionContract(
            "resource construction would duplicate an existing token".to_string(),
        )));
    }
    let resources = match state
        .resources()
        .clone()
        .try_compose_with_fact(constructed.clone(), assumptions)
    {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(resource_context_runtime_error(error))),
    };
    Ok(Ok(state.clone().with_resource_context(resources)))
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
    assumptions: &PureFactContext,
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
    assumptions: &PureFactContext,
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
    for arguments_path in
        evaluate_c_arguments_paths(state, arguments, assumptions, budget, Some(environment))?
    {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(CFunctionPath {
                outcome,
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        }

        let path_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        let Some((argument_values, argument_obligations)) = coerce_c_function_arguments(
            function,
            &arguments_path.values,
            &arguments_path.obligations,
            &path_assumptions,
        ) else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "{}",
                    argument_binding_error(function, &arguments_path.values)
                ))),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        };
        let Some(callee_state) = bind_c_function_arguments(state, function, &argument_values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "{}",
                    argument_binding_error(function, &argument_values)
                ))),
                facts: arguments_path.facts,
                obligations: argument_obligations,
            });
            continue;
        };

        let body_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &argument_obligations,
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
                        obligations: argument_obligations,
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
            let Some((mut facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &arguments_path.facts,
                &argument_obligations,
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
                        &argument_values,
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
                        &argument_values,
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

            append_string_literal_loadable_facts(function, &outcome, &mut facts);

            paths.push(CFunctionPath {
                outcome,
                facts,
                obligations,
            });
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_function_verification_paths(
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
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
    for arguments_path in crate::instrumentation::measure_operation(
        function.name(),
        "independent kernel execution",
        "verification argument evaluation",
        || evaluate_c_arguments_paths(state, arguments, assumptions, budget, Some(environment)),
    )? {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(CFunctionPath {
                outcome,
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        }

        let path_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        let Some((argument_values, argument_obligations)) = coerce_c_function_arguments(
            function,
            &arguments_path.values,
            &arguments_path.obligations,
            &path_assumptions,
        ) else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "{}",
                    argument_binding_error(function, &arguments_path.values)
                ))),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        };
        let Some(callee_state) = bind_c_function_arguments(state, function, &argument_values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "{}",
                    argument_binding_error(function, &argument_values)
                ))),
                facts: arguments_path.facts,
                obligations: argument_obligations,
            });
            continue;
        };

        let body_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &argument_obligations,
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
                        obligations: argument_obligations,
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
        let body_paths = crate::instrumentation::measure_operation(
            function.name(),
            "independent kernel execution",
            "verification body execution",
            || {
                execute_c_statement_verification_paths(
                    &callee_state,
                    function.body(),
                    &body_assumptions,
                    environment,
                    execution_semantics,
                    budget,
                    variables,
                )
            },
        )?;
        for body_path in body_paths {
            let Some((mut facts, obligations)) = crate::instrumentation::measure_operation(
                function.name(),
                "independent kernel execution",
                "verification fact merge",
                || {
                    merge_execution_pure_facts_and_obligations(
                        &arguments_path.facts,
                        &argument_obligations,
                        &body_path.facts,
                        &body_path.obligations,
                        assumptions,
                    )
                },
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
                        &argument_values,
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
                        &argument_values,
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

            append_string_literal_loadable_facts(function, &outcome, &mut facts);

            paths.push(CFunctionPath {
                outcome,
                facts,
                obligations,
            });
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_function_call_paths(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    if let Some(rule) = environment.get_external_function_rule(function.name()) {
        let assumed_rule = CVerifiedFunctionRule {
            function: rule.function.clone(),
        };
        return execute_verified_function_rule(
            caller_state,
            &assumed_rule,
            arguments,
            assumptions,
            environment,
            budget,
        );
    }
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
                environment,
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
    for arguments_path in evaluate_c_arguments_paths(
        caller_state,
        arguments,
        assumptions,
        budget,
        Some(environment),
    )? {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(CFunctionPath {
                outcome,
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        }

        let path_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        let Some((argument_values, argument_obligations)) = coerce_c_function_arguments(
            function,
            &arguments_path.values,
            &arguments_path.obligations,
            &path_assumptions,
        ) else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "{}",
                    argument_binding_error(function, &arguments_path.values)
                ))),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        };
        let Some(callee_state) =
            bind_c_function_arguments(caller_state, function, &argument_values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "{}",
                    argument_binding_error(function, &argument_values)
                ))),
                facts: arguments_path.facts,
                obligations: argument_obligations,
            });
            continue;
        };

        let body_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &argument_obligations,
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
                    obligations: argument_obligations,
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
                &argument_obligations,
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
                &argument_values,
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

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn execute_verified_function_rule(
    caller_state: &CState,
    rule: &CVerifiedFunctionRule,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    let function = &rule.function;
    budget.consume_function_call()?;
    let existing_variables = crate::instrumentation::measure_operation(
        function.name(),
        "verified function rule application",
        "verified call variable collection",
        || {
            let mut existing_variables = BTreeSet::new();
            collect_c_state_bitvector_variables(caller_state, &mut existing_variables);
            collect_c_function_bitvector_variables(function, &mut existing_variables);
            for argument in arguments {
                collect_c_expression_bitvector_variables(argument, &mut existing_variables);
            }
            collect_assumption_variables(assumptions, &mut existing_variables);
            existing_variables
        },
    );
    let mut variables =
        KernelVariableGenerator::fresh_for(budget.next_kernel_variable, existing_variables);
    let memory_identity = variables.next();
    let result_identity = variables.next();
    budget.next_kernel_variable = variables.next;
    let mut paths = Vec::new();
    for arguments_path in evaluate_c_arguments_paths(
        caller_state,
        arguments,
        assumptions,
        budget,
        Some(environment),
    )? {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(CFunctionPath {
                outcome,
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        }
        let path_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        let Some((argument_values, argument_obligations)) = coerce_c_function_arguments(
            function,
            &arguments_path.values,
            &arguments_path.obligations,
            &path_assumptions,
        ) else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "{}",
                    argument_binding_error(function, &arguments_path.values)
                ))),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        };
        let Some(mut entry_state) =
            bind_c_function_arguments(caller_state, function, &argument_values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "{}",
                    argument_binding_error(function, &argument_values)
                ))),
                facts: arguments_path.facts,
                obligations: argument_obligations,
            });
            continue;
        };
        let path_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &argument_obligations,
        );
        let transfer = match crate::instrumentation::measure_operation(
            function.name(),
            "verified function rule application",
            "verified call resource transfer preparation",
            || {
                prepare_function_resource_transfer(
                    caller_state,
                    &entry_state,
                    function,
                    &path_assumptions,
                    budget,
                    false,
                )
            },
        )? {
            Ok(transfer) => transfer,
            Err(error) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts: arguments_path.facts,
                    obligations: argument_obligations,
                });
                continue;
            }
        };
        entry_state.resources = transfer.callee_resources.clone();
        let entry_contract_state =
            with_contract_argument_views(&entry_state, function, &argument_values);

        let mut obligations = argument_obligations;
        let mut facts = arguments_path.facts;
        let mut established_requirements = Vec::new();
        let requirement_timing = crate::instrumentation::OperationTiming::new(
            function.name(),
            "verified function rule application",
            "verified call requirement checking",
        );
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
                    let obligation_is_proven =
                        super::assumptions::capture_implicit_reasoning_provenance(|| {
                            requirement_assumptions.proves(&guarded)
                        });
                    if obligation_is_proven {
                        super::assumptions::record_reasoning_provenance(
                            &requirement_assumptions,
                            &guarded,
                        );
                    } else {
                        obligations.push(
                            ProofObligation::verification_condition(guarded.clone())
                                .with_context(format!("{} precondition", function.name())),
                        );
                    }
                    established_requirements.push(guarded);
                }
                let requirement_is_proven =
                    super::assumptions::capture_implicit_reasoning_provenance(|| {
                        match &requirement_path.proposition {
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
                        }
                    });
                if requirement_is_proven {
                    super::assumptions::record_reasoning_provenance(
                        &path_assumptions,
                        &requirement_path.proposition,
                    );
                }
                let guarded_requirement = wrap_path_context(
                    requirement_path.proposition,
                    &requirement_path.facts,
                    &requirement_path.obligations,
                );
                if !requirement_is_proven {
                    let guarded_is_proven =
                        super::assumptions::capture_implicit_reasoning_provenance(|| {
                            requirement_assumptions.proves(&guarded_requirement)
                        });
                    if guarded_is_proven {
                        super::assumptions::record_reasoning_provenance(
                            &requirement_assumptions,
                            &guarded_requirement,
                        );
                    } else {
                        obligations.push(
                            ProofObligation::verification_condition(guarded_requirement.clone())
                                .with_context(format!("{} precondition", function.name())),
                        );
                    }
                }
                established_requirements.push(guarded_requirement);
            }
        }
        drop(requirement_timing);

        let effective_assumptions =
            assumptions_with_path_context(assumptions, &facts, &obligations);
        let mut effective_assumptions =
            assumptions_with_propositions(&effective_assumptions, &established_requirements)
                .transport_memory_load_condition_facts();
        let footprint_state = entry_contract_state.clone();
        let mut mutable_ranges = Vec::new();
        let mut footprint_error = None;
        let footprint_timing = crate::instrumentation::OperationTiming::new(
            function.name(),
            "verified function rule application",
            "verified call mutable footprint lowering",
        );
        for segment in function.contract_mutable() {
            let element_width = segment.element_width();
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
            match evaluate_loop_effect_segment_with_facts(
                &footprint_state,
                segment,
                &effective_assumptions,
                budget,
            )? {
                Ok((segment, segment_facts)) => {
                    for fact in &segment_facts {
                        if !facts.contains(fact) {
                            facts.push(fact.clone());
                        }
                    }
                    effective_assumptions =
                        assumptions_with_path_context(&effective_assumptions, &segment_facts, &[]);
                    // Lower the recorded footprint while its defining
                    // equalities (earlier callees' ensures, path facts) are
                    // in scope: every later frame query against this range
                    // then matches entry-vocabulary facts syntactically
                    // instead of re-proving the lowering per query. See the
                    // creation-time lowering design in
                    // issues/indexed-resource-algebra-avoids-pairwise-context-work.md.
                    mutable_ranges.push(lower_memory_range_under_assumptions(
                        CMemoryRange::new_with_element_width(
                            segment.base,
                            segment.start,
                            segment.end,
                            element_width,
                        ),
                        &effective_assumptions,
                    ))
                }
                Err(message) => {
                    footprint_error = Some(message);
                    break;
                }
            }
        }
        drop(footprint_timing);
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
            facts.push(
                ExecutionPureFact::internal(Proposition::CMemoryEffectSummary {
                    before: entry_state.memory.clone(),
                    after: memory.clone(),
                    mutable_ranges: mutable_ranges.clone(),
                })
                .into_certified(),
            );
        }
        let result = symbolic_call_result(function.return_type(), result_identity);
        let mut post_state = entry_state.clone().with_memory(memory);
        if function.return_type() != CType::Void {
            set_function_result(&mut post_state, function, result.clone());
        }
        let mut transition_state = post_state
            .clone()
            .with_resource_context(transfer.callee_resources.clone());
        let population_timing = crate::instrumentation::OperationTiming::new(
            function.name(),
            "verified function rule application",
            "verified call population transition",
        );
        let population_transition = match apply_counted_population_transitions(
            caller_state,
            &mut transition_state,
            function,
            &argument_values,
            &effective_assumptions,
            true,
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
        drop(population_timing);
        post_state.counted_populations = transition_state.counted_populations;
        for obligation in &population_transition.postcondition_obligations {
            // The kernel issues `CVerifiedFunctionRule` only after exact
            // contract certification has discharged these postconditions.
            // Applying that rule instantiates certified consequences; it
            // must not turn them back into caller prerequisites.
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
            with_contract_argument_views(&post_state, function, &argument_values);

        let return_resource_timing = crate::instrumentation::OperationTiming::new(
            function.name(),
            "verified function rule application",
            "verified call return resource evaluation",
        );
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
        drop(return_resource_timing);
        let return_resources =
            activate_population_body_resources(return_resources, &population_transition);

        // Lower the ensures before reconciling allocation ownership so the
        // transition can prove exact continuity when the contract states it.
        // An undecided continuity relation remains symbolic in this one call
        // successor; it is not an execution-path split.
        post_state.resources = return_resources.clone();
        let provisional_post_contract_state =
            with_contract_argument_views(&post_state, function, &argument_values);
        let mut provisional_facts = facts.clone();
        let provisional_ensure_timing = crate::instrumentation::OperationTiming::new(
            function.name(),
            "verified function rule application",
            "verified call provisional ensure lowering",
        );
        add_verified_function_ensure_facts(
            &mut provisional_facts,
            &obligations,
            &provisional_post_contract_state,
            &entry_contract_state,
            function,
            &effective_assumptions,
            budget,
        )?;
        drop(provisional_ensure_timing);

        let allocation_delta_timing = crate::instrumentation::OperationTiming::new(
            function.name(),
            "verified function rule application",
            "verified call heap allocation delta",
        );
        let allocation_assumptions =
            assumptions_with_path_context(&effective_assumptions, &provisional_facts, &obligations);
        let allocation_delta = apply_verified_heap_allocation_delta(
            post_state.memory.clone(),
            &transfer.callee_resources,
            &caller_resources_after_requirements,
            &return_resources,
            function,
            &allocation_assumptions,
        );
        drop(allocation_delta_timing);
        let (memory, allocation_effects) = match allocation_delta {
            Ok(result) => result,
            Err(VerifiedAllocationDeltaError::Runtime(error)) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                });
                continue;
            }
            Err(VerifiedAllocationDeltaError::InconsistentReturnedAllocation) => continue,
        };
        facts.extend(allocation_effects);
        post_state.memory = memory;
        let post_contract_state =
            with_contract_argument_views(&post_state, function, &argument_values);

        let ensure_timing = crate::instrumentation::OperationTiming::new(
            function.name(),
            "verified function rule application",
            "verified call ensure lowering",
        );
        add_verified_function_ensure_facts(
            &mut facts,
            &obligations,
            &post_contract_state,
            &entry_contract_state,
            function,
            &effective_assumptions,
            budget,
        )?;
        drop(ensure_timing);

        let mut return_state = caller_state.clone();
        return_state.memory = post_state.memory;
        return_state.resources = return_resources;
        return_state.counted_populations = post_state.counted_populations;
        return_state.next_local_frame = post_state.next_local_frame;
        let outcome = CFunctionOutcome::Return {
            value: result,
            state: return_state,
        };
        append_string_literal_loadable_facts(function, &outcome, &mut facts);
        paths.push(CFunctionPath {
            outcome,
            facts,
            obligations,
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn add_verified_function_ensure_facts(
    facts: &mut Vec<ExecutionPureFact>,
    obligations: &[ProofObligation],
    post_contract_state: &CState,
    entry_contract_state: &CState,
    function: &CFunction,
    effective_assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<()> {
    for ensure in function.contract_ensures() {
        let ensure_assumptions =
            assumptions_with_path_context(effective_assumptions, facts, obligations);
        // A verified callee certifies that its ensures, including the memory
        // loads used to state them, are well-defined. Lower those loads into
        // explicit path obligations here instead of asking the general prover
        // to rediscover each contextual range proof while applying the call
        // rule. The obligations are retained below as certified consequences
        // of the verified contract.
        let lowering_assumptions = ensure_assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .defer_non_exact_loadability_obligations();
        let ensure_paths = lower_spec_proposition_at_state_with_loop_entry(
            post_contract_state,
            ensure,
            Some(entry_contract_state),
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
                ensure_path.proposition.clone(),
                &ensure_path.facts,
                &[],
            )));
            add_normalized_verified_ensure_facts(
                facts,
                &ensure_path.proposition,
                &ensure_assumptions,
                &ensure_path.facts,
                &ensure_path.obligations,
            );
        }
        // Preserve the source identity of a named predicate ensure. The
        // expanded `ensure` above is the operational authority; this exact
        // registered pair is its definitional surface identity.
        if let Some(unfolding) = function
            .predicate_unfoldings()
            .iter()
            .find(|unfolding| unfolding.body() == ensure)
        {
            let predicate_paths = lower_spec_proposition_at_state_with_loop_entry(
                post_contract_state,
                unfolding.predicate(),
                Some(entry_contract_state),
                &lowering_assumptions,
                budget,
            )?;
            for predicate_path in predicate_paths {
                if predicate_path.obligations.is_empty() {
                    facts.push(ExecutionPureFact::certified(predicate_path.proposition));
                }
            }
        }
    }
    Ok(())
}

/// Publishes direct constant equalities that are consequences of a verified
/// callee ensure and the caller's already-established path facts. Modular
/// calls intentionally havoc mutable memory, so a later call may see a
/// symbolic load rather than the previous call's materialized cell. Keeping
/// the original ensure is sound but can leave the surface certificate with an
/// arithmetic chain it cannot express as an exact assumption. These derived
/// equalities preserve the callee's post-state transition without retaining a
/// pre-havoc cell.
fn add_normalized_verified_ensure_facts(
    facts: &mut Vec<ExecutionPureFact>,
    ensure: &Proposition,
    ensure_assumptions: &PureFactContext,
    ensure_facts: &[ExecutionPureFact],
    ensure_obligations: &[ProofObligation],
) {
    if !ensure_obligations.is_empty()
        || !facts
            .iter()
            .any(|fact| matches!(fact.proposition(), Proposition::CMemoryEffectSummary { .. }))
        || !crate::kernel::eval::proposition_mentions_registered_load_variable(ensure)
    {
        return;
    }
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = ensure
    else {
        return;
    };
    let assumptions = assumptions_with_path_context(ensure_assumptions, ensure_facts, &[])
        .assume_proposition(ensure.clone());
    let Some(left_value) = assumptions.known_signed_constant_after_normalization(left) else {
        return;
    };
    let Some(right_value) = assumptions.known_signed_constant_after_normalization(right) else {
        return;
    };
    if left_value != right_value {
        return;
    }
    let constant = Bitvector32Term::Constant(left_value as i32 as u32);
    for term in [left.as_ref(), right.as_ref()] {
        if signed_bitvector_constant(term).is_some() {
            continue;
        }
        let normalized = wrap_path_context(
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(Box::new(term.clone()), Box::new(constant.clone())),
                true,
            ),
            ensure_facts,
            &[],
        );
        if !facts.iter().any(|fact| fact.proposition() == &normalized) {
            facts.push(ExecutionPureFact::certified(normalized));
        }
    }
}

fn allocation_continuity(
    input_base: &Pointer,
    input_bytes: &Bitvector32Term,
    output_base: &Pointer,
    output_bytes: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> AllocationContinuity {
    if pointers_proven_equal_for_memory_resolution(input_base, output_base, assumptions) {
        if bitvector_terms_proven_equal_for_memory_resolution(
            input_bytes,
            output_bytes,
            assumptions,
        ) {
            return AllocationContinuity::Same;
        }
        let condition = ConditionTerm::Bitvector32Equal(
            Box::new(input_bytes.clone()),
            Box::new(output_bytes.clone()),
        );
        if assumptions.proves(&Proposition::ConditionIs(condition.clone(), false)) {
            AllocationContinuity::Inconsistent
        } else {
            AllocationContinuity::Undecided(condition)
        }
    } else if pointers_proven_distinct_for_memory_resolution(input_base, output_base, assumptions) {
        AllocationContinuity::Distinct
    } else {
        AllocationContinuity::Undecided(ConditionTerm::pointer_equal(
            input_base.clone(),
            output_base.clone(),
        ))
    }
}

#[cfg(test)]
mod allocation_continuity_tests {
    use super::*;

    fn external_pointer(variable: u64) -> Pointer {
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(
                Bitvector32Term::Variable(Variable(variable)),
                4,
            ),
        }
    }

    #[test]
    fn continuity_requires_both_the_allocation_base_and_size() {
        let assumptions = PureFactContext::new();
        let input = external_pointer(930_000);
        assert_eq!(
            allocation_continuity(
                &input,
                &Bitvector32Term::Constant(4),
                &input,
                &Bitvector32Term::Constant(4),
                &assumptions,
            ),
            AllocationContinuity::Same,
        );
        assert_eq!(
            allocation_continuity(
                &input,
                &Bitvector32Term::Constant(4),
                &input,
                &Bitvector32Term::Constant(8),
                &assumptions,
            ),
            AllocationContinuity::Inconsistent,
        );
        assert_eq!(
            allocation_continuity(
                &Pointer {
                    block: PointerBlock::Heap(930_002),
                    offset: PointerOffsetTerm::Constant(0),
                },
                &Bitvector32Term::Constant(4),
                &Pointer {
                    block: PointerBlock::Heap(930_003),
                    offset: PointerOffsetTerm::Constant(0),
                },
                &Bitvector32Term::Constant(4),
                &assumptions,
            ),
            AllocationContinuity::Distinct,
        );

        let other = external_pointer(930_001);
        assert_eq!(
            allocation_continuity(
                &input,
                &Bitvector32Term::Constant(4),
                &other,
                &Bitvector32Term::Constant(4),
                &assumptions,
            ),
            AllocationContinuity::Undecided(ConditionTerm::pointer_equal(input, other)),
        );
    }
}

fn apply_verified_heap_allocation_delta(
    mut memory: CMemory,
    input_resources: &ResourceContext,
    preserved_caller_resources: &ResourceContext,
    output_resources: &ResourceContext,
    function: &CFunction,
    assumptions: &PureFactContext,
) -> Result<(CMemory, Vec<ExecutionPureFact>), VerifiedAllocationDeltaError> {
    let mut effects = Vec::new();
    let input = expand_all_composite_resource_facts(
        input_resources,
        function.composite_resource_definitions(),
        &memory,
        assumptions,
    )
    .ok_or_else(|| {
        VerifiedAllocationDeltaError::Runtime(CRuntimeError::FunctionContract(
            "could not inspect input allocation effects at call".to_string(),
        ))
    })?;
    let output = expand_all_composite_resource_facts(
        output_resources,
        function.composite_resource_definitions(),
        &memory,
        assumptions,
    )
    .ok_or_else(|| {
        VerifiedAllocationDeltaError::Runtime(CRuntimeError::FunctionContract(
            "could not inspect output allocation effects at call".to_string(),
        ))
    })?;
    // Returned projections describe the successor allocation. They decide
    // whether an input allocation continues, but they are not resources that
    // survived from the caller and therefore cannot be stale after the old
    // allocation is freed.
    let preserved = expand_all_composite_resource_facts(
        preserved_caller_resources,
        function.composite_resource_definitions(),
        &memory,
        assumptions,
    )
    .ok_or_else(|| {
        VerifiedAllocationDeltaError::Runtime(CRuntimeError::FunctionContract(
            "could not inspect preserved caller allocation effects at call".to_string(),
        ))
    })?;
    let allocation_assumptions = input
        .observable_facts_assuming_valid(assumptions)
        .into_iter()
        .fold(assumptions.clone(), |assumptions, fact| {
            assumptions.assume_proposition(fact)
        });
    let mut output_allocations_by_block =
        BTreeMap::<PointerBlock, Vec<(Pointer, Bitvector32Term)>>::new();
    for (base, bytes) in output.facts().iter().filter_map(CResourceFact::allocation) {
        output_allocations_by_block
            .entry(base.block.clone())
            .or_default()
            .push((base.clone(), bytes.clone()));
    }

    for allocation in input.facts().iter().filter_map(|fact| {
        fact.allocation()
            .map(|(base, bytes)| (fact, base.clone(), bytes.clone()))
    }) {
        let (fact, base, bytes) = allocation;
        if output
            .cached_support_exposing_fact(fact, &allocation_assumptions)
            .is_some()
            || expose_composite_resource_fact(
                &output,
                fact,
                function.composite_resource_definitions(),
                &memory,
                &allocation_assumptions,
            )
            .is_some()
        {
            continue;
        }
        if let Some(output_allocations) = output_allocations_by_block.get(&base.block) {
            let mut retained = false;
            let mut continuity_is_undecided = false;
            for (output_base, output_bytes) in output_allocations {
                match allocation_continuity(
                    &base,
                    &bytes,
                    output_base,
                    output_bytes,
                    &allocation_assumptions,
                ) {
                    AllocationContinuity::Same => retained = true,
                    AllocationContinuity::Distinct => {}
                    AllocationContinuity::Undecided(_) => continuity_is_undecided = true,
                    AllocationContinuity::Inconsistent => {
                        return Err(VerifiedAllocationDeltaError::InconsistentReturnedAllocation);
                    }
                }
            }
            if retained {
                continue;
            }
            // A contract that does not decide allocation continuity admits a
            // deallocating implementation. Therefore no independent caller
            // resource may still refer to the input allocation. Retire the
            // consumed allocation occurrence without asserting a C `free`;
            // the output occurrence is installed below even when it later
            // proves to have the same pointer value.
            if continuity_is_undecided {
                for resource in preserved.facts() {
                    if !resource.may_refer_to_memory_block(&base.block)
                        || resource.is_proven_separate_from_allocation(
                            &base,
                            &bytes,
                            &allocation_assumptions,
                        )
                    {
                        continue;
                    }
                    return Err(VerifiedAllocationDeltaError::Runtime(
                        CRuntimeError::StaleResourceAfterFree {
                            resource: resource.clone(),
                        },
                    ));
                }
                memory = memory.retire_contract_heap_allocation_claim(&base);
                continue;
            }
        }
        // Only the untransferred caller frame survives independently across
        // the call. Any such resource that can still refer to an allocation
        // the contract definitely retires makes this transition unsafe.
        for resource in preserved.facts() {
            if !resource.may_refer_to_memory_block(&base.block)
                || resource.is_proven_separate_from_allocation(
                    &base,
                    &bytes,
                    &allocation_assumptions,
                )
            {
                continue;
            }
            return Err(VerifiedAllocationDeltaError::Runtime(
                CRuntimeError::StaleResourceAfterFree {
                    resource: resource.clone(),
                },
            ));
        }
        let before_free = memory.clone();
        if memory.live_heap_block_size(&base).is_none() {
            memory = memory
                .with_heap_allocation_claim(base.clone(), bytes.clone())
                .ok_or(VerifiedAllocationDeltaError::Runtime(
                    CRuntimeError::InvalidFree(CInvalidFree::NonHeapPointer),
                ))?;
        }
        memory = memory.free_heap_block(&base).map_err(|error| {
            VerifiedAllocationDeltaError::Runtime(CRuntimeError::InvalidFree(error))
        })?;
        effects.push(ExecutionPureFact::internal(
            Proposition::CHeapAllocationFreed {
                before: before_free,
                after: memory.clone(),
                allocation_base: base,
                bytes,
            },
        ));
    }

    for fact in output.facts() {
        let Some((base, bytes)) = fact.allocation() else {
            continue;
        };
        if input.satisfies_fact(fact, &allocation_assumptions)
            || memory.live_heap_block_size(base).is_some()
        {
            continue;
        }
        memory = memory
            .with_heap_allocation_claim(base.clone(), bytes.clone())
            .ok_or_else(|| {
                VerifiedAllocationDeltaError::Runtime(CRuntimeError::FunctionContract(
                    "returned allocation conflicts with an existing or deallocated identity"
                        .to_string(),
                ))
            })?;
    }
    Ok((memory, effects))
}

fn with_contract_argument_views(state: &CState, function: &CFunction, values: &[CValue]) -> CState {
    let mut state = state.clone();
    for (parameter, value) in function.parameters().iter().zip(values) {
        if parameter.aggregate_layout().is_some() {
            // Aggregate parameters are already represented by the copied
            // address-backed object installed by argument binding. Keeping
            // that binding lets contract field accesses inspect the copy
            // rather than accidentally replacing it with the caller's source
            // pointer.
            continue;
        }
        // Keep the contract view identical to the typed parameter binding.
        // In particular, a C null-pointer constant arrives here as the
        // caller's int32 `0`, but the callee parameter is a pointer.  Using
        // the raw caller value would overwrite the correctly coerced binding
        // and make pointer preconditions impossible to lower.
        let value = coerce_c_function_argument_without_obligations(value, parameter.c_type())
            .expect("function arguments were type-checked before building contract views");
        state.locals.set_typed_volatile(
            parameter.name().to_string(),
            value.clone(),
            parameter.c_type(),
            parameter.is_volatile(),
        );
        if let CValue::Pointer(pointer) = &value {
            let element_width = parameter
                .c_type()
                .pointee_type()
                .map(CType::byte_width)
                .unwrap_or(4);
            state.resources = state
                .resources
                .unchecked_with_fact(CResourceFact::view_memory(
                    CMemoryRange::new_with_element_width(
                        pointer.pointer().clone(),
                        Bitvector32Term::Constant(0),
                        Bitvector32Term::Constant(i32::MAX as u32),
                        element_width,
                    ),
                ));
        }
    }
    state
}

fn set_function_result(state: &mut CState, function: &CFunction, value: CValue) {
    if let Some(layout) = function.return_aggregate_layout()
        && let CValue::Pointer(pointer) = &value
    {
        state.memory = if matches!(pointer.block, PointerBlock::Symbolic(_)) {
            state
                .memory
                .clone()
                .with_block_without_derivation(pointer.block.clone(), layout.size_bytes())
        } else {
            state
                .memory
                .clone()
                .with_block(pointer.block.clone(), layout.size_bytes())
        };
        state.locals.set_aggregate_object_at(
            "result".to_string(),
            layout.clone(),
            pointer.pointer().clone(),
        );
        return;
    }
    state
        .locals
        .set_typed("result".to_string(), value, function.return_type());
}

fn materialize_aggregate_return(
    state: &mut CState,
    function: &CFunction,
    value: CValue,
) -> Option<CValue> {
    let layout = function.return_aggregate_layout()?;
    let CValue::Pointer(pointer) = value else {
        return None;
    };
    if pointer.is_null() {
        return None;
    }
    let source = pointer.pointer().clone();
    let frame = state.next_local_frame;
    let destination = CMemory::frame_local_pointer(frame, "__return");
    state.memory = state
        .memory
        .clone()
        .with_block(destination.block.clone(), layout.size_bytes());
    state.memory = copy_aggregate_fields(state.memory.clone(), &source, &destination, layout);
    state.next_local_frame = frame.saturating_add(1);
    Some(CValue::typed_pointer(destination, function.return_type()))
}

fn coerce_function_return_value(
    value: CValue,
    function: &CFunction,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    // Plain struct returns use `uint8*` as their internal ABI slot, while the
    // source expression that supplies the value retains the pointee type of
    // the object it addresses (for example, `int32*` for `return *source`).
    // The aggregate return materializer copies through the pointer and is the
    // type boundary that validates the complete object. The C0 struct model
    // uses `int32*` for a struct pointer and `uint8*` for an address-backed
    // struct value, so only those two data-pointer views cross this boundary.
    if function.return_aggregate_layout().is_some()
        && let CValue::Pointer(pointer) = &value
        && matches!(pointer.c_type(), CType::Int32Pointer | CType::UInt8Pointer)
        && !pointer.pointer().block.is_function()
    {
        return Some(CValue::typed_pointer(
            pointer.pointer().clone(),
            function.return_type(),
        ));
    }
    coerce_c_value_to_type(value, function.return_type(), obligations, assumptions)
}

fn symbolic_call_result(c_type: CType, variable: Variable) -> CValue {
    match c_type {
        CType::Void => CValue::Void,
        CType::Int16 => CValue::Int16(Bitvector32Term::Variable(variable)),
        CType::Int32 => CValue::Int32(Bitvector32Term::Variable(variable)),
        CType::UInt8 => CValue::UInt8(Bitvector32Term::Variable(variable)),
        CType::UInt16 => CValue::UInt16(Bitvector32Term::Variable(variable)),
        CType::UInt32 => CValue::UInt32(Bitvector32Term::Variable(variable)),
        CType::Int64 => CValue::Int64(Bitvector32Term::Variable(variable)),
        CType::UInt64 => CValue::UInt64(Bitvector32Term::Variable(variable)),
        CType::Float32 => CValue::Float32(Bitvector32Term::Variable(variable)),
        CType::Float64 => CValue::Float64(Bitvector32Term::Variable(variable)),
        CType::Int16Pointer
        | CType::UInt16Pointer
        | CType::Int32Pointer
        | CType::UInt8Pointer
        | CType::UInt32Pointer
        | CType::Int64Pointer
        | CType::UInt64Pointer
        | CType::Int16PointerPointer
        | CType::UInt16PointerPointer
        | CType::Int32PointerPointer
        | CType::UInt8PointerPointer
        | CType::UInt32PointerPointer
        | CType::Int64PointerPointer
        | CType::UInt64PointerPointer
        | CType::Float32Pointer
        | CType::Float64Pointer
        | CType::Float32PointerPointer
        | CType::Float64PointerPointer => {
            CValue::typed_pointer(Pointer::symbolic(variable), c_type)
        }
        CType::FunctionPointer(_) => {
            CValue::typed_pointer(Pointer::symbolic_function(variable), c_type)
        }
        CType::Int32Array(_)
        | CType::UInt8Array(_)
        | CType::Int16Array(_)
        | CType::UInt16Array(_)
        | CType::UInt32Array(_)
        | CType::Int64Array(_)
        | CType::UInt64Array(_)
        | CType::Float32Array(_)
        | CType::Float64Array(_) => {
            unreachable!("C functions cannot return array values")
        }
    }
}

pub(super) fn add_memory_store_obligation(
    memory: &CMemory,
    pointer: &Pointer,
    value: &CValue,
    mut obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
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
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    environment: Option<&CExecutionEnvironment>,
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
                        let value = type_function_address_value(argument, value, environment);
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
        budget.check_path_width(next_paths.len())?;
        paths = next_paths;
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn type_function_address_value(
    expression: &CExpression,
    value: CValue,
    environment: Option<&CExecutionEnvironment>,
) -> CValue {
    let CExpression::FunctionAddress(name) = expression else {
        return value;
    };
    let Some(environment) = environment else {
        return value;
    };
    let Some(function) = environment.get_function(name) else {
        return value;
    };
    match value {
        CValue::Pointer(pointer)
            if pointer.block.is_function() && pointer.c_type() == CType::FunctionPointer(0) =>
        {
            CValue::typed_pointer(pointer.into_pointer(), function.function_pointer_type())
        }
        value => value,
    }
}

fn argument_binding_error(function: &CFunction, values: &[CValue]) -> String {
    if function
        .parameters()
        .iter()
        .zip(values)
        .any(|(parameter, value)| {
            matches!(
                (parameter.c_type(), value),
                (CType::FunctionPointer(expected), CValue::Pointer(actual))
                    if actual.block.is_function()
                        && actual.c_type() != CType::FunctionPointer(expected)
            )
        })
    {
        format!(
            "incompatible signature for function pointer argument to {}",
            function.name()
        )
    } else {
        format!("could not bind arguments for {}", function.name())
    }
}

/// A function-level path carries the loadability of its own string literals
/// across the call boundary. This is intentionally derived from the function
/// metadata rather than by scanning all read-only memory, so a call summary
/// cannot accidentally certify an unrelated block.
fn append_string_literal_loadable_facts(
    function: &CFunction,
    outcome: &CFunctionOutcome,
    facts: &mut Vec<ExecutionPureFact>,
) {
    let CFunctionOutcome::Return { state, .. } = outcome else {
        return;
    };
    for literal in function.string_literals() {
        let base = CMemory::string_literal_pointer(function.name(), literal.name());
        let proposition = Proposition::CMemoryLoadable {
            memory: state.memory.clone(),
            base,
            bytes: Bitvector32Term::Constant(literal.bytes().len() as u32),
        };
        if !facts.iter().any(|fact| fact.proposition() == &proposition) {
            facts.push(ExecutionPureFact::certified(proposition));
        }
    }
}

pub(super) fn bind_c_function_arguments(
    caller_state: &CState,
    function: &CFunction,
    values: &[CValue],
) -> Option<CState> {
    // Preserve the historical value-only representation for parameters whose
    // addresses never escape. Besides avoiding unnecessary memory cells, this
    // keeps ordinary call summaries unchanged. A frame is needed only when
    // the function body actually contains an address-taking expression for a
    // parameter.
    let mut address_taken = BTreeSet::new();
    crate::kernel::loops::collect_address_taken_locals(function.body(), &mut address_taken);
    let address_taken_parameters = function
        .parameters()
        .iter()
        // Taking the address of a pointer parameter's pointee (for example
        // `&p[1]`) mentions `p` while addressing the pointed-to object, not the
        // parameter object itself. Pointer-to-pointer parameters are outside
        // the current C type model, so only scalar parameter objects need a
        // callee stack slot here.
        .filter(|parameter| {
            (address_taken.contains(parameter.name()) || parameter.is_volatile())
                && matches!(
                    parameter.c_type(),
                    CType::Int16
                        | CType::Int32
                        | CType::UInt8
                        | CType::UInt16
                        | CType::UInt32
                        | CType::Float32
                        | CType::Float64
                )
        })
        .map(|parameter| parameter.name())
        .collect::<BTreeSet<_>>();
    let frame = caller_state.next_local_frame();
    let has_aggregate_parameters = function
        .parameters()
        .iter()
        .any(|parameter| parameter.aggregate_layout().is_some());
    let mut callee_state = CState::new()
        .with_memory(caller_state.memory.clone())
        .with_resource_context(caller_state.resources.clone())
        .with_next_local_frame(
            if address_taken_parameters.is_empty() && !has_aggregate_parameters {
                frame
            } else {
                frame.saturating_add(1)
            },
        );
    callee_state.counted_populations = caller_state.counted_populations.clone();
    callee_state = initialize_c_function_globals(&callee_state, function);
    for (parameter, value) in function.parameters().iter().zip(values) {
        if let Some(layout) = parameter.aggregate_layout() {
            let CValue::Pointer(pointer) = value else {
                return None;
            };
            if pointer.is_null() {
                return None;
            }
            let source = pointer.pointer().clone();
            let slot = CMemory::frame_local_pointer(frame, parameter.name());
            // Preserve the caller's memory snapshot for symbolic source
            // loads. Declaring the destination first would make an unknown
            // external field load depend on the callee's fresh block and
            // prevent entry facts from relating it to the caller's value.
            callee_state.memory =
                copy_aggregate_fields(callee_state.memory, &source, &slot, layout);
            callee_state.memory = callee_state
                .memory
                .with_block(slot.block.clone(), layout.size_bytes());
            callee_state.locals.set_aggregate_object_at(
                parameter.name().to_string(),
                layout.clone(),
                slot,
            );
            continue;
        }
        let value = coerce_c_function_argument_without_obligations(value, parameter.c_type())?;
        if address_taken_parameters.contains(parameter.name()) {
            let slot = CMemory::frame_local_pointer(frame, parameter.name());
            callee_state.memory = callee_state
                .memory
                .with_block(slot.block.clone(), value.byte_width())
                .store(slot.clone(), value.clone());
            callee_state.locals.set_typed_volatile_at(
                parameter.name().to_string(),
                value,
                parameter.c_type(),
                slot,
                parameter.is_volatile(),
            );
        } else {
            callee_state.locals.set_typed_volatile(
                parameter.name().to_string(),
                value,
                parameter.c_type(),
                parameter.is_volatile(),
            );
        }
    }
    Some(callee_state)
}

fn coerce_c_function_argument_without_obligations(
    value: &CValue,
    target_type: CType,
) -> Option<CValue> {
    let mut obligations = Vec::new();
    let value = coerce_c_value_to_type(
        value.clone(),
        target_type,
        &mut obligations,
        &PureFactContext::new(),
    )?;
    obligations.is_empty().then_some(value)
}

fn coerce_c_function_arguments(
    function: &CFunction,
    values: &[CValue],
    existing_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
) -> Option<(Vec<CValue>, Vec<ProofObligation>)> {
    if values.len() != function.parameters().len() {
        return None;
    }
    let mut obligations = existing_obligations.to_vec();
    let mut coerced = Vec::with_capacity(values.len());
    for (parameter, value) in function.parameters().iter().zip(values) {
        if parameter.aggregate_layout().is_some() {
            coerced.push(value.clone());
        } else {
            coerced.push(coerce_c_value_to_type(
                value.clone(),
                parameter.c_type(),
                &mut obligations,
                assumptions,
            )?);
        }
    }
    Some((coerced, obligations))
}

/// Installs the stable global and static-local bindings needed by a function's
/// entry and contract states. Existing memory is preserved so nested calls
/// observe writes performed by their caller; a missing block is the fresh
/// program entry case and receives the object's initial value. Static locals
/// use a function-qualified block identity and are therefore initialized once
/// for the whole symbolic execution, not once per call frame.
pub(crate) fn initialize_c_function_globals(state: &CState, function: &CFunction) -> CState {
    let mut state = state.clone();
    for literal in function.string_literals() {
        let slot = CMemory::string_literal_pointer(function.name(), literal.name());
        if !state.memory.has_block(&slot.block) {
            state.memory = state
                .memory
                .with_read_only_block(slot.block.clone(), literal.bytes().len() as u32);
            for (offset, byte) in literal.bytes().iter().copied().enumerate() {
                state.memory = state.memory.store(
                    Pointer {
                        block: slot.block.clone(),
                        offset: PointerOffsetTerm::Constant(offset as i64),
                    },
                    uint8(u32::from(byte)),
                );
            }
        }
        state.locals.set_array_object_at(
            literal.name().to_string(),
            CType::UInt8,
            literal.bytes().len() as u32,
            slot.clone(),
        );
        let literal_resource = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            slot,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(literal.bytes().len() as u32),
            1,
        ));
        if !state
            .resources
            .contains_exact_representation(&literal_resource)
        {
            state.resources = state
                .resources
                .clone()
                .unchecked_with_fact(literal_resource);
        }
    }
    for global in function.global_variables() {
        let slot = CMemory::global_pointer(global.kernel_name());
        if !state.memory.has_block(&slot.block) {
            state.memory = state
                .memory
                .with_block(slot.block.clone(), global.c_type().byte_width())
                .store(slot.clone(), global.initial_value().clone());
        }
        state.locals.set_global_at(
            global.kernel_name().to_string(),
            global.c_type(),
            slot.clone(),
            global.is_volatile(),
        );
        if global.kernel_name() != global.name() && !state.locals.contains_name(global.name()) {
            state.locals.set_global_at(
                global.name().to_string(),
                global.c_type(),
                slot,
                global.is_volatile(),
            );
        }
    }
    for global_array in function.global_arrays() {
        let slot = CMemory::global_pointer(global_array.kernel_name());
        let bytes = global_array
            .length()
            .checked_mul(global_array.element_type().byte_width())
            .expect("validated C global array size");
        if !state.memory.has_block(&slot.block) {
            state.memory = state.memory.with_block(slot.block.clone(), bytes);
            for (index, value) in global_array.initial_values().iter().enumerate() {
                state.memory = state.memory.store(
                    slot.offset_by_bytes(
                        u32::try_from(index)
                            .expect("validated C global array length")
                            .saturating_mul(global_array.element_type().byte_width()),
                    ),
                    value.clone(),
                );
            }
        }
        state.locals.set_array_object_at(
            global_array.kernel_name().to_string(),
            global_array.element_type(),
            global_array.length(),
            slot.clone(),
        );
        if global_array.kernel_name() != global_array.name()
            && !state.locals.contains_name(global_array.name())
        {
            state.locals.set_array_object_at(
                global_array.name().to_string(),
                global_array.element_type(),
                global_array.length(),
                slot,
            );
        }
    }
    for static_local in function.static_variables() {
        let slot = CMemory::static_pointer(function.name(), static_local.kernel_name());
        if !state.memory.has_block(&slot.block) {
            state.memory = state
                .memory
                .with_block(slot.block.clone(), static_local.c_type().byte_width())
                .store(slot.clone(), static_local.initial_value().clone());
        }
        state.locals.set_global_at(
            static_local.kernel_name().to_string(),
            static_local.c_type(),
            slot.clone(),
            static_local.is_volatile(),
        );
        // Contract C fragments use the source spelling. A nested static may
        // have a kernel-only name to distinguish it from another object in a
        // sibling block; expose the spelling only when the callee has not
        // already installed a parameter or another visible binding with it.
        if static_local.kernel_name() != static_local.source_name()
            && !state.locals.contains_name(static_local.source_name())
        {
            state.locals.set_global_at(
                static_local.source_name().to_string(),
                static_local.c_type(),
                slot,
                static_local.is_volatile(),
            );
        }
    }
    for static_array in function.static_arrays() {
        let slot = CMemory::static_pointer(function.name(), static_array.kernel_name());
        let bytes = static_array
            .length()
            .checked_mul(static_array.element_type().byte_width())
            .expect("validated C static local array size");
        if !state.memory.has_block(&slot.block) {
            state.memory = state.memory.with_block(slot.block.clone(), bytes);
            for (index, value) in static_array.initial_values().iter().enumerate() {
                state.memory = state.memory.store(
                    slot.offset_by_bytes(
                        u32::try_from(index)
                            .expect("validated C static local array length")
                            .saturating_mul(static_array.element_type().byte_width()),
                    ),
                    value.clone(),
                );
            }
        }
        state.locals.set_array_object_at(
            static_array.kernel_name().to_string(),
            static_array.element_type(),
            static_array.length(),
            slot.clone(),
        );
        if static_array.kernel_name() != static_array.source_name()
            && !state.locals.contains_name(static_array.source_name())
        {
            state.locals.set_array_object_at(
                static_array.source_name().to_string(),
                static_array.element_type(),
                static_array.length(),
                slot,
            );
        }
    }
    state
}

/// Copy the modeled cells of an address-backed aggregate into a distinct
/// destination block. Fixed scalar-array fields and flattened embedded-struct
/// array leaves are copied one cell at a time. Pointer fields are
/// shallow-copied: the pointer value is duplicated,
/// but the pointed-to allocation is not. Missing cells in automatic storage
/// remain missing so an uninitialized source field stays uninitialized in the
/// copy; opaque/external source cells are represented by typed symbolic loads.
pub(super) fn copy_aggregate_fields(
    mut memory: CMemory,
    source: &Pointer,
    destination: &Pointer,
    layout: &CAggregateLayout,
) -> CMemory {
    for field in layout.fields() {
        let (element_type, element_count) = match field.c_type() {
            CType::Int16
            | CType::Int32
            | CType::UInt8
            | CType::UInt16
            | CType::UInt32
            | CType::Int64
            | CType::UInt64
            | CType::Float32
            | CType::Float64 => (field.c_type(), 1),
            CType::Int32Array(length) => (CType::Int32, length),
            CType::UInt8Array(length) => (CType::UInt8, length),
            CType::Int32Pointer
            | CType::UInt8Pointer
            | CType::Int32PointerPointer
            | CType::UInt8PointerPointer => (field.c_type(), 1),
            _ => continue,
        };
        for index in 0..element_count {
            let element_offset = field
                .offset_bytes()
                .checked_add(
                    index
                        .checked_mul(element_type.byte_width())
                        .expect("validated aggregate field offset"),
                )
                .expect("validated aggregate field offset");
            let source_field = source.offset_by_bytes(element_offset);
            let destination_field = destination.offset_by_bytes(element_offset);
            let value = memory.known_value(&source_field).or_else(|| {
                if memory.is_zeroed_heap_address(&source_field, element_type.byte_width()) {
                    return match element_type {
                        CType::Int16 => Some(int16(0)),
                        CType::Int32 => Some(int32(0)),
                        CType::UInt8 => Some(uint8(0)),
                        CType::Int32Pointer
                        | CType::UInt8Pointer
                        | CType::Int32PointerPointer
                        | CType::UInt8PointerPointer => {
                            Some(CValue::typed_pointer(Pointer::null(), element_type))
                        }
                        CType::UInt16 => Some(uint16(0)),
                        CType::UInt32 => Some(uint32(0)),
                        CType::Int64 => Some(CValue::Int64(Bitvector32Term::Constant(0))),
                        CType::UInt64 => Some(CValue::UInt64(Bitvector32Term::Constant(0))),
                        CType::Float32 => Some(CValue::Float32(Bitvector32Term::Constant(0))),
                        CType::Float64 => Some(CValue::Float64(Bitvector32Term::UInt64Constant(0))),
                        _ => None,
                    };
                }
                if memory.has_block(&source_field.block)
                    && !matches!(source_field.block, PointerBlock::Symbolic(_))
                    && memory.access_in_bounds(&source_field, element_type.byte_width())
                {
                    return None;
                }
                match element_type {
                    CType::Int16 => Some(CValue::Int16(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    CType::Int32 => Some(CValue::Int32(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    CType::UInt8 => Some(CValue::UInt8(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    CType::Int32Pointer
                    | CType::UInt8Pointer
                    | CType::Int32PointerPointer
                    | CType::UInt8PointerPointer => {
                        let pointee_type = element_type.pointee_type()?;
                        let load = crate::kernel::canonical_form_of_load(
                            crate::kernel::intern_c_memory(memory.clone()),
                            source_field.clone(),
                        );
                        Some(CValue::typed_pointer(
                            Pointer {
                                block: source_field.block.clone(),
                                offset: PointerOffsetTerm::scale_int32(
                                    load,
                                    i64::from(pointee_type.byte_width()),
                                ),
                            },
                            element_type,
                        ))
                    }
                    CType::UInt16 => Some(CValue::UInt16(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    CType::UInt32 => Some(CValue::UInt32(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    CType::Int64 => Some(CValue::Int64(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    CType::UInt64 => Some(CValue::UInt64(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    CType::Float32 => Some(CValue::Float32(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    CType::Float64 => Some(CValue::Float64(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    _ => None,
                }
            });
            if let Some(value) = value {
                memory = memory.store(destination_field, value);
            }
        }
    }
    memory
}

fn evaluate_resource_population_body_resources(
    required_resources: &ResourceContext,
    callee_state: &CState,
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    include_ordinary: bool,
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
        if !include_ordinary && !definition.is_counted_population() {
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
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    preserve_explicit_representation: bool,
) -> ExecutionResult<Result<CFunctionResourceTransfer, CRuntimeError>> {
    let preserve_explicit_representation = preserve_explicit_representation
        && function
            .composite_resource_definitions()
            .iter()
            .any(CCompositeResourceDefinition::is_recursive);
    let required_resources =
        match super::assumptions::capture_implicit_reasoning_provenance(|| {
            evaluate_function_resource_context(
                callee_state,
                function.resource_requires(),
                assumptions,
                budget,
            )
        })? {
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
    let population_body_resources = match evaluate_resource_population_body_resources(
        &required_resources,
        callee_state,
        function.composite_resource_definitions(),
        assumptions,
        budget,
        false,
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
        // Proof execution may have opened exactly the recursive branches needed
        // by the body with `observe` or `unfold`. Independent certification
        // must execute from that same definitionally equivalent form.
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
            let body = match evaluate_resource_population_body_resources(
                &singleton,
                callee_state,
                function.composite_resource_definitions(),
                assumptions,
                budget,
                false,
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
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceContext, CRuntimeError>> {
    let ensured_resources = match crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "ensured resource lowering",
        || {
            evaluate_function_resource_context(
                post_state,
                function.resource_ensures(),
                assumptions,
                budget,
            )
        },
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    // A view returned to a caller that already owns the same resource does
    // not create another persistent capability. Keeping both forms would
    // make a later valid mutation or free look as though a stale borrow were
    // still live.
    let newly_ensured_resources = crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "ensured resource view deduplication",
        || {
            ensured_resources
                .facts()
                .iter()
                .filter(|fact| {
                    !fact.is_view()
                        || !caller_resources_after_requirements.satisfies_fact(fact, assumptions)
                })
                .cloned()
                .collect::<Vec<_>>()
        },
    );
    let return_resources = match crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "ensured resource composition",
        || {
            caller_resources_after_requirements
                .clone()
                .try_compose_with_facts_delaying_normalization(newly_ensured_resources, assumptions)
        },
    ) {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(resource_context_runtime_error(error))),
    };
    let Some(projected_cores_by_support) = crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "ensured resource core projection",
        || {
            let _assumptions_id_scope = crate::kernel::PureFactContextIdScope::enter(assumptions);
            ensured_resources
                .facts()
                .iter()
                .filter(|support| support.is_own())
                .map(|support| {
                    let singleton = ResourceContext::new().unchecked_with_fact(support.clone());
                    let expanded = expand_all_composite_resource_facts(
                        &singleton,
                        function.composite_resource_definitions(),
                        post_state.memory(),
                        assumptions,
                    )?;
                    let expansion = expanded.facts().to_vec();
                    let projected = expansion
                        .iter()
                        .filter_map(|fact| fact.core_with_assumptions(assumptions))
                        // These duplicable cores are certified projections of
                        // `support`; publishing them needs no proof-aware
                        // search through the caller's existing resources.
                        // Exact duplicates are the only entries worth
                        // suppressing here. Equivalent alternate spellings
                        // remain supported by this occurrence and disappear
                        // with it.
                        .filter(|core| !return_resources.contains_exact_representation(core))
                        .collect::<BTreeSet<_>>()
                        .into_iter()
                        .collect::<Vec<_>>();
                    Some((support.clone(), expansion, projected))
                })
                .collect::<Option<Vec<_>>>()
        },
    ) else {
        return Ok(Err(CRuntimeError::FunctionContract(format!(
            "could not expand ensured composite resources after call: {ensured_resources:?}"
        ))));
    };
    // The callee has already certified every ensured composite and its
    // instantiated body. Its duplicable cores are therefore observations of
    // certified ownership, not independent persistent caller capabilities.
    // Record their exact support so consuming that ownership removes only
    // its projections through the reverse index.
    let return_resources = projected_cores_by_support.into_iter().fold(
        return_resources,
        |resources, (support, expansion, projected)| {
            resources
                .unchecked_with_supported_facts(&support, projected)
                .with_cached_supported_expansion(&support, expansion)
        },
    );
    Ok(Ok(return_resources))
}

fn counted_population_quantities(
    resources: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    tracked_state: &CState,
    assumptions: &PureFactContext,
    track_ordinary_populations: bool,
) -> BTreeMap<(String, Vec<CValue>), Bitvector32Term> {
    let mut quantities = BTreeMap::<(String, Vec<CValue>), Bitvector32Term>::new();
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
        // Every declared composite denotes a population. Most singleton
        // resources never expose their count at the surface, but their body
        // still has one population-wide owner whose lifetime follows the
        // first produced and last consumed unit.
        let has_declared_body = definitions.iter().any(|definition| {
            definition.name() == name
                && definition_has_population_wide_body(definition, track_ordinary_populations)
        });
        let population_is_observed = tracked_state.observes_population_family(name)
            || tracked_state
                .counted_population_proven_equal(name, arguments, assumptions)
                .is_some();
        if !has_declared_body && !population_is_observed {
            continue;
        }
        let Some(quantity) = fact.owned_quantity_term() else {
            continue;
        };
        quantities
            .entry((name.clone(), arguments.clone()))
            .and_modify(|total| {
                *total = Bitvector32Term::add(total.clone(), quantity.clone());
            })
            .or_insert_with(|| quantity.clone());
    }
    quantities
}

fn definition_has_population_wide_body(
    definition: &CCompositeResourceDefinition,
    track_ordinary_populations: bool,
) -> bool {
    definition.is_counted_population()
        || (track_ordinary_populations
            && !definition.is_recursive()
            && definition.condition().is_none()
            && definition
                .contains()
                .iter()
                .all(resource_spec_has_snapshot_independent_footprint))
}

fn population_quantity_is_zero(quantity: &Bitvector32Term, assumptions: &PureFactContext) -> bool {
    quantity == &Bitvector32Term::Constant(0)
        || assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(quantity.clone()),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        ))
}

fn population_quantity_is_positive(
    quantity: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    quantity.as_const().is_some_and(|value| value > 0)
        || assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterThan(
                Box::new(quantity.clone()),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        ))
}

fn population_quantities_are_equal(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    left == right
        || assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(left.clone()), Box::new(right.clone())),
            true,
        ))
}

fn resource_spec_has_snapshot_independent_footprint(resource: &CResourceSpec) -> bool {
    match resource {
        CResourceSpec::ViewMemory(segment) | CResourceSpec::OwnMemory(segment) => {
            segment.guard.is_none()
                && c_expression_is_snapshot_independent(&segment.base)
                && c_expression_is_snapshot_independent(&segment.start)
                && c_expression_is_snapshot_independent(&segment.end)
        }
        CResourceSpec::Composite { arguments, .. } | CResourceSpec::Token { arguments, .. } => {
            arguments.iter().all(c_expression_is_snapshot_independent)
        }
        CResourceSpec::Quantified { quantity, resource } => {
            c_expression_is_snapshot_independent(quantity)
                && resource_spec_has_snapshot_independent_footprint(resource)
        }
    }
}

fn population_body_requires_positive_witness(definition: &CCompositeResourceDefinition) -> bool {
    fn resource_is_duplicable_view(resource: &CResourceSpec) -> bool {
        match resource {
            CResourceSpec::ViewMemory(_) => true,
            CResourceSpec::Quantified { resource, .. } => resource_is_duplicable_view(resource),
            CResourceSpec::Composite { access, .. } | CResourceSpec::Token { access, .. } => {
                *access == CResourceAccessMode::View
            }
            CResourceSpec::OwnMemory(_) => false,
        }
    }

    !definition.facts().is_empty()
        || definition
            .contains()
            .iter()
            .any(|resource| !resource_is_duplicable_view(resource))
}

fn c_expression_is_snapshot_independent(expression: &CExpression) -> bool {
    match expression {
        CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => true,
        CExpression::Cast { expression, .. } => c_expression_is_snapshot_independent(expression),
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_is_snapshot_independent(condition)
                && c_expression_is_snapshot_independent(then_branch)
                && c_expression_is_snapshot_independent(else_branch)
        }
        CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. } => {
            c_expression_is_snapshot_independent(expression)
        }
        CExpression::AddressOf(inner)
        | CExpression::Not(inner)
        | CExpression::BitwiseNot(inner) => c_expression_is_snapshot_independent(inner),
        CExpression::PointerOffsetBytes { pointer, .. } => {
            c_expression_is_snapshot_independent(pointer)
        }
        CExpression::Load(_) | CExpression::TypedLoad { .. } | CExpression::Index(_, _) => false,
        CExpression::LessThan(left, right)
        | CExpression::LessEqual(left, right)
        | CExpression::GreaterThan(left, right)
        | CExpression::GreaterEqual(left, right)
        | CExpression::Equal(left, right)
        | CExpression::NotEqual(left, right)
        | CExpression::And(left, right)
        | CExpression::Or(left, right)
        | CExpression::Add(left, right)
        | CExpression::Subtract(left, right)
        | CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right) => {
            c_expression_is_snapshot_independent(left)
                && c_expression_is_snapshot_independent(right)
        }
    }
}

#[derive(Default)]
struct CCountedPopulationTransition {
    activated_body_resources: Vec<CResourceFact>,
    finalized_body_resources: Vec<CResourceFact>,
    population_facts: Vec<Proposition>,
    postcondition_obligations: Vec<ProofObligation>,
}

fn apply_counted_population_transition_resources(
    mut resources: ResourceContext,
    transition: &CCountedPopulationTransition,
    assumptions: &PureFactContext,
) -> Result<ResourceContext, CRuntimeError> {
    for resource in &transition.finalized_body_resources {
        for representation in [
            Some(resource.clone()),
            resource.core_with_assumptions(assumptions),
        ]
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

fn activate_population_body_resources(
    mut resources: ResourceContext,
    transition: &CCountedPopulationTransition,
) -> ResourceContext {
    for resource in &transition.activated_body_resources {
        if !resources.facts().contains(resource) {
            // The folded units and this body are two parts of one declared
            // population representation. The body is installed once when
            // that population becomes nonempty; it is not another unit.
            resources = resources.unchecked_with_fact(resource.clone());
        }
    }
    resources
}

fn apply_counted_population_transitions(
    caller_state: &CState,
    post_state: &mut CState,
    function: &CFunction,
    argument_values: &[CValue],
    assumptions: &PureFactContext,
    reestablish_invariants: bool,
    track_ordinary_populations: bool,
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
        track_ordinary_populations,
    );
    let ensured_quantities = counted_population_quantities(
        &ensured,
        function.composite_resource_definitions(),
        caller_state,
        assumptions,
        track_ordinary_populations,
    );
    let caller_quantities = counted_population_quantities(
        caller_state.resources(),
        function.composite_resource_definitions(),
        caller_state,
        assumptions,
        track_ordinary_populations,
    );
    let keys = required_quantities
        .keys()
        .chain(ensured_quantities.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut transition = CCountedPopulationTransition::default();
    let mut transition_guaranteed_facts = Vec::new();
    for (name, arguments) in keys {
        let declared_population_definition = function
            .composite_resource_definitions()
            .iter()
            .find(|definition| definition.name() == name);
        let population_body_definition = declared_population_definition.filter(|definition| {
            definition_has_population_wide_body(definition, track_ordinary_populations)
        });
        let required_quantity = required_quantities
            .get(&(name.clone(), arguments.clone()))
            .cloned()
            .unwrap_or(Bitvector32Term::Constant(0));
        let ensured_quantity = ensured_quantities
            .get(&(name.clone(), arguments.clone()))
            .cloned()
            .unwrap_or(Bitvector32Term::Constant(0));
        if population_quantities_are_equal(&required_quantity, &ensured_quantity, assumptions) {
            let refreshes_ordinary_population = track_ordinary_populations
                && population_quantity_is_positive(&required_quantity, assumptions)
                && caller_state.counted_population(&name, &arguments).is_some()
                && population_body_definition
                    .is_some_and(|definition| !definition.is_counted_population());
            if refreshes_ordinary_population {
                let singleton = ResourceContext::new().unchecked_with_fact(CResourceFact::own(
                    CResource::Composite {
                        name: name.clone(),
                        arguments: arguments.clone(),
                    },
                ));
                let finalized = match evaluate_resource_population_body_resources(
                    &singleton,
                    &entry_state,
                    function.composite_resource_definitions(),
                    assumptions,
                    budget,
                    true,
                )? {
                    Ok(resources) => resources,
                    Err(error) => return Ok(Err(error)),
                };
                let activated = match evaluate_resource_population_body_resources(
                    &singleton,
                    post_state,
                    function.composite_resource_definitions(),
                    assumptions,
                    budget,
                    true,
                )? {
                    Ok(resources) => resources,
                    Err(error) => return Ok(Err(error)),
                };
                transition
                    .finalized_body_resources
                    .extend(finalized.facts().iter().cloned());
                transition
                    .activated_body_resources
                    .extend(activated.facts().iter().cloned());
            }
            // A resource-neutral contract preserves this exact population.
            // Do not ask general arithmetic reasoning to rediscover
            // `old_count + 0 != 0`; on large proof contexts that turns a
            // constant-time ledger update into an expensive search.
            if caller_state.counted_population(&name, &arguments).is_none() {
                let visible_count = caller_quantities
                    .get(&(name.clone(), arguments.clone()))
                    .cloned()
                    .unwrap_or(required_quantity);
                if population_quantity_is_positive(&visible_count, assumptions) {
                    *post_state =
                        post_state
                            .clone()
                            .with_counted_population(name, arguments, visible_count);
                }
            }
            continue;
        }
        let consumes_entire_population =
            population_quantity_is_zero(&ensured_quantity, assumptions)
                && caller_state
                    .counted_population(&name, &arguments)
                    .is_some_and(|old_count| {
                        population_quantities_are_equal(old_count, &required_quantity, assumptions)
                    });
        let tracked_prior = caller_state.counted_population(&name, &arguments).cloned();
        let visible_prior = caller_quantities
            .get(&(name.clone(), arguments.clone()))
            .cloned();
        let prior_count_for_transition = tracked_prior.clone().or_else(|| visible_prior.clone());
        let new_count = if let Some((required, ensured)) = required_quantity
            .as_const()
            .zip(ensured_quantity.as_const())
        {
            let prior = tracked_prior.clone().or_else(|| visible_prior.clone());
            if let Some(prior) = prior {
                if ensured >= required {
                    Bitvector32Term::add(prior, Bitvector32Term::Constant(ensured - required))
                } else {
                    Bitvector32Term::subtract(prior, Bitvector32Term::Constant(required - ensured))
                }
            } else if required > 0 || ensured > 0 {
                Bitvector32Term::Constant(ensured)
            } else {
                return Ok(Err(CRuntimeError::FunctionContract(format!(
                    "counted population `{name}` is not initialized"
                ))));
            }
        } else {
            let prior_count = match tracked_prior.or(visible_prior) {
                Some(prior_count) => prior_count,
                None if population_quantity_is_zero(&required_quantity, assumptions) => {
                    Bitvector32Term::Constant(0)
                }
                None => {
                    return Ok(Err(CRuntimeError::FunctionContract(format!(
                        "counted population `{name}` is not initialized"
                    ))));
                }
            };
            // Replacing the entire visible population is the common symbolic
            // contract case. Preserve the ensured quantity directly instead
            // of asking later checks to rediscover cancellation.
            if population_quantities_are_equal(&prior_count, &required_quantity, assumptions) {
                ensured_quantity.clone()
            } else {
                Bitvector32Term::add(
                    Bitvector32Term::subtract(prior_count, required_quantity.clone()),
                    ensured_quantity.clone(),
                )
            }
        };
        let population_was_initialized =
            caller_state.counted_population(&name, &arguments).is_some()
                || caller_quantities
                    .get(&(name.clone(), arguments.clone()))
                    .is_some_and(|quantity| population_quantity_is_positive(quantity, assumptions))
                || population_quantity_is_positive(&required_quantity, assumptions);
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
            if population_body_definition.is_some() {
                let singleton = ResourceContext::new().unchecked_with_fact(CResourceFact::own(
                    CResource::Composite {
                        name: name.clone(),
                        arguments: arguments.clone(),
                    },
                ));
                let finalized = match evaluate_resource_population_body_resources(
                    &singleton,
                    &entry_state,
                    function.composite_resource_definitions(),
                    assumptions,
                    budget,
                    true,
                )? {
                    Ok(resources) => resources,
                    Err(error) => return Ok(Err(error)),
                };
                transition
                    .finalized_body_resources
                    .extend(finalized.facts().iter().cloned());
            }
        } else {
            *post_state = post_state.clone().with_counted_population(
                name.clone(),
                arguments.clone(),
                new_count.clone(),
            );
            let activates_ordinary_population = track_ordinary_populations
                && population_body_definition
                    .is_some_and(|definition| !definition.is_counted_population());
            if !population_was_initialized && activates_ordinary_population {
                let singleton = ResourceContext::new().unchecked_with_fact(CResourceFact::own(
                    CResource::Composite {
                        name: name.clone(),
                        arguments: arguments.clone(),
                    },
                ));
                let activated = match evaluate_resource_population_body_resources(
                    &singleton,
                    post_state,
                    function.composite_resource_definitions(),
                    assumptions,
                    budget,
                    true,
                )? {
                    Ok(resources) => resources,
                    Err(error) => return Ok(Err(error)),
                };
                transition
                    .activated_body_resources
                    .extend(activated.facts().iter().cloned());
            }
            // A visible ensured unit witnesses nonemptiness. The transition
            // preserves the population cardinality invariant algebraically:
            // entry count >= required units, then both sides change by the
            // same net contract quantity. Only a population with no locally
            // returned unit needs an explicit proof that unseen units remain.
            if population_quantity_is_zero(&ensured_quantity, assumptions)
                && declared_population_definition
                    .is_none_or(population_body_requires_positive_witness)
            {
                transition.postcondition_obligations.push(
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
                let guaranteed = Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedGreaterEqual(
                        Box::new(new_count.clone()),
                        Box::new(ensured_quantity.clone()),
                    ),
                    true,
                );
                if let (Some(new_count), Some(ensured_count)) =
                    (new_count.as_const(), ensured_quantity.as_const())
                    && (new_count as i32) < (ensured_count as i32)
                {
                    return Ok(Err(CRuntimeError::FunctionContract(format!(
                        "invalid counted population transition for `{name}`: post-count {new_count} is below returned quantity {ensured_count}"
                    ))));
                }
                let residual_is_certified_nonnegative =
                    population_quantity_is_zero(&ensured_quantity, assumptions)
                        && prior_count_for_transition.as_ref().is_some_and(|prior| {
                            new_count
                                == Bitvector32Term::subtract(
                                    prior.clone(),
                                    required_quantity.clone(),
                                )
                                && assumptions.proves(&Proposition::ConditionIs(
                                    ConditionTerm::Bitvector32SignedGreaterEqual(
                                        Box::new(required_quantity.clone()),
                                        Box::new(Bitvector32Term::Constant(0)),
                                    ),
                                    true,
                                ))
                                && assumptions.proves(&Proposition::ConditionIs(
                                    ConditionTerm::Bitvector32SignedLessEqual(
                                        Box::new(required_quantity.clone()),
                                        Box::new(prior.clone()),
                                    ),
                                    true,
                                ))
                        });
                if assumptions.proves(&guaranteed) || residual_is_certified_nonnegative {
                    transition_guaranteed_facts.push(guaranteed);
                } else {
                    transition.postcondition_obligations.push(
                        ProofObligation::verification_condition(guaranteed)
                            .with_context("returned resource quantity fits post-population"),
                    );
                }
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
    let mut active_populations = Vec::new();
    for population in post_contract_state.counted_populations() {
        if population_quantity_is_zero(&population.count, assumptions) {
            continue;
        }
        let population_body = function
            .composite_resource_definitions()
            .iter()
            .find(|definition| {
                definition.name() == population.name
                    && definition_has_population_wide_body(definition, true)
            });
        let Some(population_body) = population_body else {
            continue;
        };
        if !population_body_requires_positive_witness(population_body) {
            continue;
        }
        if !population_quantity_is_positive(&population.count, assumptions) {
            transition.postcondition_obligations.push(
                ProofObligation::verification_condition(Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedGreaterThan(
                        Box::new(population.count.clone()),
                        Box::new(Bitvector32Term::Constant(0)),
                    ),
                    true,
                ))
                .with_context("resource population body is active"),
            );
        }
        active_populations.push(CResourceFact::own(CResource::Composite {
            name: population.name.clone(),
            arguments: population.arguments.clone(),
        }));
    }
    let active_populations = ResourceContext::new().unchecked_with_facts(active_populations);
    let Some(population_facts) = evaluate_resource_population_fact_propositions(
        &active_populations,
        function.composite_resource_definitions(),
        &post_contract_state,
        &PureFactContext::new(),
        true,
    ) else {
        return Ok(Err(CRuntimeError::FunctionContract(
            "could not evaluate resource population postcondition".to_string(),
        )));
    };
    for proposition in population_facts {
        if let Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right),
            true,
        ) = &proposition
            && let (Some(left), Some(right)) = (left.as_const(), right.as_const())
            && (left as i32) < (right as i32)
        {
            return Ok(Err(CRuntimeError::FunctionContract(format!(
                "invalid population fact: post-count {left} is below visible quantity {right}"
            ))));
        }
        transition.population_facts.push(proposition.clone());
        if !assumptions.proves(&proposition) && !transition_guaranteed_facts.contains(&proposition)
        {
            transition.postcondition_obligations.push(
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
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CState, CRuntimeError>> {
    let Some(callee_state) = bind_c_function_arguments(caller_state, function, argument_values)
    else {
        return Ok(Err(CRuntimeError::FunctionContract(format!(
            "could not bind contract-entry arguments for {}",
            function.name()
        ))));
    };
    let transfer = match crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "contract resource transfer preparation",
        || {
            prepare_function_resource_transfer(
                caller_state,
                &callee_state,
                function,
                assumptions,
                budget,
                true,
            )
        },
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
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    expand_composite_resource_fact_with_children(
        context,
        composite,
        definitions,
        memory,
        assumptions,
    )
    .map(|(expanded, _, _)| expanded)
}

pub(super) fn expand_composite_resource_fact_with_children(
    context: &ResourceContext,
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Option<(ResourceContext, Vec<CResourceFact>, Vec<CResourceFact>)> {
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
        return Some((context.clone(), Vec::new(), Vec::new()));
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
    let raw_children = if composite.is_own() {
        child_facts.clone()
    } else {
        child_facts
            .iter()
            .map(|fact| CResourceFact::View(fact.resource().clone()))
            .collect()
    };
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
        .filter(|child| {
            !expanded.facts().contains(child)
                && !resource_context_contains_exact_owned_fact(&expanded, child, assumptions)
        })
        .cloned()
        .collect::<Vec<_>>();
    expanded = expanded
        .try_compose_certified_group_into_valid_context_delaying_normalization(missing, assumptions)
        .ok()?;
    Some((expanded, children, raw_children))
}

fn resource_context_contains_exact_owned_fact(
    context: &ResourceContext,
    required: &CResourceFact,
    assumptions: &PureFactContext,
) -> bool {
    if !required.is_own() {
        return false;
    }
    if let CResourceFact::Own(CResource::Memory(required_range), _) = required {
        let exact_parts = context
            .facts()
            .iter()
            .filter(|available| {
                available.memory_own_range().is_some_and(|available_range| {
                    memory_range_covers(required_range, available_range, assumptions)
                })
            })
            .cloned()
            .collect::<Vec<_>>();
        let exact_parts = ResourceContext::new().unchecked_with_facts(exact_parts);
        return exact_parts.validity_error(assumptions).is_none()
            && exact_parts.satisfies_fact(required, assumptions);
    }
    context.facts().iter().any(|available| {
        if !available.is_own() || available.family() != required.family() {
            return false;
        }
        ResourceContext::new()
            .unchecked_with_fact(available.clone())
            .without_fact_delaying_normalization(required, assumptions)
            .is_some_and(|remaining| remaining.is_empty())
    })
}

pub(super) fn evaluate_guarded_contract_condition(
    condition: &SpecProposition,
    state: &CState,
    assumptions: &PureFactContext,
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
        super::assumptions::record_reasoning_provenance(assumptions, &path.proposition);
        return Some(true);
    }
    let false_proposition = match &path.proposition {
        Proposition::ConditionIs(condition, value) => {
            Proposition::ConditionIs(condition.clone(), !value)
        }
        Proposition::Not(body) => body.as_ref().clone(),
        proposition => Proposition::Not(Box::new(proposition.clone())),
    };
    if proves_body_condition(&false_proposition) {
        super::assumptions::record_reasoning_provenance(assumptions, &false_proposition);
        Some(false)
    } else {
        None
    }
}

fn evaluate_composite_resource_body_condition(
    definition: &CCompositeResourceDefinition,
    state: &CState,
    assumptions: &PureFactContext,
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
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    let mut cached = context.clone();
    let supports = context
        .facts()
        .iter()
        .filter(|fact| matches!(fact.resource(), CResource::Composite { .. }))
        .filter_map(|support| {
            context
                .cached_supported_expansion(support)
                .map(|expansion| (support.clone(), expansion.to_vec()))
        })
        .collect::<Vec<_>>();
    for (support, expansion) in supports {
        if expansion.as_slice() == [support.clone()] {
            continue;
        }
        cached = cached.without_exact_representation(&support)?;
        let missing = expansion
            .into_iter()
            .filter(|fact| {
                !cached.facts().contains(fact)
                    && !resource_context_contains_exact_owned_fact(&cached, fact, assumptions)
            })
            .collect::<Vec<_>>();
        cached = cached
            .try_compose_certified_group_into_valid_context_delaying_normalization(
                missing,
                assumptions,
            )
            .ok()?;
    }
    expand_composite_resource_context(&cached, definitions, memory, assumptions)
        .map(|(resources, _)| resources)
}

/// Continues through recursive composites only while their guards are
/// decidable in the current contract path. Unknown branches remain folded.
fn expand_decidable_composite_resource_frontier(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
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
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    // Exposure unfolds composites until the target is held. A memory target
    // is looked up by structure at every context first: the indexed answer
    // for a cell an unfolded body names outright. Only when no unfolding
    // holds it by structure does each context, in the same order, answer
    // with the reasoning the resource algebra applies.
    let structural = target.memory_range().is_some();
    let mut visited = Vec::new();
    let mut seen = BTreeSet::new();
    let mut pending = VecDeque::from([context.clone()]);
    while let Some(context) = pending.pop_front() {
        if !seen.insert(context.clone()) {
            continue;
        }
        if structural && context.satisfies_memory_fact_structurally(target) {
            return Some(context);
        }
        // The composite whose pointer argument is the target's base by
        // structure is unfolded first: when any composite holds the cell,
        // it is that one.
        let mut composites = context
            .facts()
            .iter()
            .filter(|fact| matches!(fact.resource(), CResource::Composite { .. }))
            .cloned()
            .collect::<Vec<_>>();
        if let Some(required) = target.memory_range() {
            composites
                .sort_by_key(|composite| !composite_names_pointer_base(composite, required.base()));
        }
        for composite in &composites {
            let expanded = expand_composite_resource_fact(
                &context,
                composite,
                definitions,
                memory,
                assumptions,
            )?;
            if expanded == context {
                continue;
            }
            if structural && expanded.satisfies_memory_fact_structurally(target) {
                return Some(expanded);
            }
            pending.push_back(expanded);
        }
        visited.push(context);
    }
    visited
        .into_iter()
        .find(|context| context.satisfies_fact(target, assumptions))
}

/// Whether a composite fact names the base of `pointer` among its pointer
/// arguments by structure: the same pointer, or one that `pointer` is a
/// constant offset from.
fn composite_names_pointer_base(composite: &CResourceFact, pointer: &Pointer) -> bool {
    let CResource::Composite { arguments, .. } = composite.resource() else {
        return false;
    };
    arguments.iter().any(|argument| {
        let CValue::Pointer(argument) = argument else {
            return false;
        };
        argument.pointer() == pointer
            || pointer
                .element_index_from_base_with_width(argument.pointer(), 1)
                .is_some()
    })
}

fn expand_composite_resource_context(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
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
    assumptions: &PureFactContext,
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
    let (mut expanded, children, _) = expand_composite_resource_fact_with_children(
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
    assumptions: &PureFactContext,
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

pub(super) fn evaluate_resource_population_fact_propositions(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    state: &CState,
    assumptions: &PureFactContext,
    include_ordinary: bool,
) -> Option<Vec<Proposition>> {
    let mut populations = BTreeMap::<(String, Vec<CValue>), Bitvector32Term>::new();
    for fact in context.facts() {
        let (name, arguments) = match fact.resource() {
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                (name, arguments)
            }
            CResource::Memory(_) => continue,
        };
        let Some(quantity) = fact.owned_quantity_term() else {
            continue;
        };
        populations
            .entry((name.clone(), arguments.clone()))
            .and_modify(|total| {
                *total = Bitvector32Term::add(total.clone(), quantity.clone());
            })
            .or_insert_with(|| quantity.clone());
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
        if let Some(population_count) = population_count {
            propositions.push(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedGreaterEqual(
                    Box::new(population_count.clone()),
                    Box::new(visible_quantity),
                ),
                true,
            ));
        }
        // Resource expansion checks ownership relations, but a composite's
        // declared pure facts must also be checked from the kernel-side body
        // state. Ordinary resources do not need a population ledger merely
        // to validate those facts; this is deliberately independent of the
        // population-wide accounting policy below. A body with no facts has
        // no additional proposition to validate here.
        let check_declared_facts = definition.is_counted_population()
            || include_ordinary
            || !definition.facts().is_empty();
        if !check_declared_facts {
            continue;
        }
        let body_active = match population_count {
            Some(_) => {
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
                evaluate_composite_resource_body_condition(
                    definition,
                    &population_state,
                    &evaluation_assumptions,
                    &mut budget,
                )?
            }
            None if !definition.is_counted_population() && !include_ordinary => {
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
                match evaluate_composite_resource_body_condition(
                    definition,
                    &population_state,
                    &evaluation_assumptions,
                    &mut budget,
                ) {
                    Some(active) => active,
                    None => continue,
                }
            }
            None => return None,
        };
        if population_count.is_none() && (definition.is_counted_population() || include_ordinary) {
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
        if !body_active {
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
    assumptions: &PureFactContext,
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
    let mut child_facts = Vec::new();
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
            && let Some(owned_child) = child.owned_resource()
        {
            children.push(owned_child.clone());
        }
        child_facts.push(child);
    }
    let mut propositions = Vec::new();
    if composite.is_own() {
        // The child context is the compact authority for ownership-derived
        // separation. Publishing one carrier lets certification answer
        // member-pair queries on demand instead of materializing O(N^2)
        // `CResourceSeparate` propositions.
        let child_context = ResourceContext::new()
            .try_compose_with_facts(child_facts, assumptions)
            .ok()?;
        propositions.push(Proposition::CResourceComposition(child_context));
    }
    for child in &children {
        propositions.push(Proposition::CResourceContains {
            parent: composite.resource().clone(),
            child: child.clone(),
        });
    }
    Some(propositions)
}

pub(super) fn evaluate_composite_resource_loadable_propositions(
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
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
    if !evaluate_composite_resource_body_condition(
        definition,
        &state,
        &evaluation_assumptions,
        &mut budget,
    )? {
        return Some(Vec::new());
    }

    let mut propositions = Vec::new();
    for resource in definition.contains() {
        let segment = match resource {
            CResourceSpec::ViewMemory(segment) | CResourceSpec::OwnMemory(segment) => segment,
            CResourceSpec::Quantified { .. }
            | CResourceSpec::Composite { .. }
            | CResourceSpec::Token { .. } => continue,
        };
        let evaluated = match evaluate_function_resource_spec(
            &state,
            resource,
            &evaluation_assumptions,
            &mut budget,
        )
        .ok()?
        {
            Ok(resource) => resource,
            Err(_) => return None,
        };
        let range = evaluated.memory_range()?;
        let element_width = segment.element_width();
        propositions.push(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: range
                .base()
                .offset_by_elements(range.start().clone(), element_width),
            bytes: Bitvector32Term::multiply(
                Bitvector32Term::subtract(range.end().clone(), range.start().clone()),
                Bitvector32Term::Constant(element_width),
            ),
        });
    }
    Some(propositions)
}

pub(super) fn evaluate_composite_resource_fact_propositions(
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    resources: &ResourceContext,
    assumptions: &PureFactContext,
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
    assumptions: &PureFactContext,
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
    required.facts().iter().all(|fact| {
        let satisfied = available.satisfies_fact(fact, assumptions);
        satisfied
    })
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
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    fn consume(
        available: &ResourceContext,
        required: &CResourceFact,
        definitions: &[CCompositeResourceDefinition],
        memory: &CMemory,
        assumptions: &PureFactContext,
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
        let direct_remaining = crate::instrumentation::measure_operation(
            "kernel",
            "resource containment",
            "resource containment: direct consumption",
            || {
                available
                    .clone()
                    .without_fact_delaying_normalization(required, assumptions)
            },
        );
        if let Some(remaining) = direct_remaining {
            return Some(remaining);
        }
        let normalized = crate::instrumentation::measure_operation(
            "kernel",
            "resource containment",
            "resource containment: normalization",
            || available.clone().normalized(assumptions),
        );
        if &normalized != available
            && let Some(remaining) =
                normalized.without_fact_delaying_normalization(required, assumptions)
        {
            return Some(remaining);
        }

        let required_context = ResourceContext::new().unchecked_with_fact(required.clone());
        if let Some(expanded_required) = crate::instrumentation::measure_operation(
            "kernel",
            "resource containment",
            "resource containment: expand required",
            || {
                expand_composite_resource_fact(
                    &required_context,
                    required,
                    definitions,
                    memory,
                    assumptions,
                )
            },
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
            let Some(expanded_available) = crate::instrumentation::measure_operation(
                "kernel",
                "resource containment",
                "resource containment: expand available",
                || {
                    expand_composite_resource_fact(
                        available,
                        composite,
                        definitions,
                        memory,
                        assumptions,
                    )
                },
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
    assumptions: &PureFactContext,
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
    assumptions: &PureFactContext,
) -> bool {
    resource_context_definitionally_contains(left, right, definitions, memory, assumptions)
        && resource_context_definitionally_contains(right, left, definitions, memory, assumptions)
}

pub(super) fn evaluate_function_resource_context(
    state: &CState,
    resources: &[CResourceSpec],
    assumptions: &PureFactContext,
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
        ResourceContextValidityError::OverlappingOwnedMemoryResources { left, right } => {
            CRuntimeError::OverlappingOwnedMemoryResources {
                left: Box::new(left),
                right: Box::new(right),
            }
        }
    }
}

pub(super) fn evaluate_function_resource_spec(
    state: &CState,
    resource: &CResourceSpec,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CResourceFact, CRuntimeError>> {
    match resource {
        CResourceSpec::Quantified { quantity, resource } => {
            let (access, name) = match resource.as_ref() {
                CResourceSpec::Composite { access, name, .. }
                | CResourceSpec::Token { access, name, .. } => (access, name),
                _ => {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "symbolic quantities require a user-declared resource".to_string(),
                    )));
                }
            };
            if *access != CResourceAccessMode::Own
                || name == CResourceFact::ALLOCATION_RESOURCE_NAME
            {
                return Ok(Err(CRuntimeError::FunctionContract(
                    "symbolic quantities require owned user-declared resources".to_string(),
                )));
            }
            let quantity = match evaluate_loop_effect_segment_value(
                state,
                quantity,
                assumptions,
                "declared resource quantity",
                budget,
            )? {
                Ok(CValue::Int32(quantity)) => quantity,
                Ok(_) | Err(_) => {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "declared resource quantity must evaluate to int32".to_string(),
                    )));
                }
            };
            let nonnegative = Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedGreaterEqual(
                    Box::new(quantity.clone()),
                    Box::new(Bitvector32Term::Constant(0)),
                ),
                true,
            );
            if !assumptions.proves(&nonnegative) {
                return Ok(Err(CRuntimeError::FunctionContract(
                    "declared resource quantity is not proved nonnegative".to_string(),
                )));
            }
            let inner = match evaluate_function_resource_spec(state, resource, assumptions, budget)?
            {
                Ok(inner) => inner,
                Err(error) => return Ok(Err(error)),
            };
            let CResourceFact::Own(inner, _) = inner else {
                return Ok(Err(CRuntimeError::FunctionContract(
                    "declared resource quantity did not lower to owned authority".to_string(),
                )));
            };
            Ok(Ok(CResourceFact::own_quantity(inner, quantity)))
        }
        CResourceSpec::ViewMemory(segment) => {
            let element_width = segment.element_width();
            let segment = match evaluate_loop_effect_segment(state, segment, assumptions, budget)? {
                Ok(segment) => segment,
                Err(_) => {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "could not evaluate a viewed memory resource segment".to_string(),
                    )));
                }
            };
            Ok(Ok(CResourceFact::view_memory(
                CMemoryRange::new_with_element_width(
                    segment.base,
                    segment.start,
                    segment.end,
                    element_width,
                ),
            )))
        }
        CResourceSpec::OwnMemory(segment) => {
            let element_width = segment.element_width();
            let segment = match evaluate_loop_effect_segment(state, segment, assumptions, budget)? {
                Ok(segment) => segment,
                Err(_) => {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "could not evaluate an owned memory resource segment".to_string(),
                    )));
                }
            };
            Ok(Ok(CResourceFact::own_memory(
                CMemoryRange::new_with_element_width(
                    segment.base,
                    segment.start,
                    segment.end,
                    element_width,
                ),
            )))
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

/// Lowers the nonnegativity conditions implicit in quantified resource
/// requirements. A function may assume these at its own entry just as it may
/// assume its ordinary `requires`; call sites still use
/// `evaluate_function_resource_spec` and must prove every condition.
pub(super) fn quantified_resource_requirement_assumptions(
    state: &CState,
    resources: &[CResourceSpec],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<Vec<Proposition>, CRuntimeError>> {
    let mut propositions = Vec::new();
    for resource in resources {
        let CResourceSpec::Quantified { quantity, .. } = resource else {
            continue;
        };
        let quantity = match evaluate_loop_effect_segment_value(
            state,
            quantity,
            assumptions,
            "declared resource quantity",
            budget,
        )? {
            Ok(CValue::Int32(quantity)) => quantity,
            Ok(_) | Err(_) => {
                return Ok(Err(CRuntimeError::FunctionContract(
                    "declared resource quantity must evaluate to int32".to_string(),
                )));
            }
        };
        propositions.push(Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(quantity),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        ));
    }
    Ok(Ok(propositions))
}

fn evaluate_function_declared_resource_spec(
    state: &CState,
    access: CResourceAccessMode,
    family: ResourceFamily,
    name: &str,
    arguments: &[CExpression],
    parameter_types: &[CType],
    assumptions: &PureFactContext,
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
        let accepts_allocation_pointer = name == CResourceFact::ALLOCATION_RESOURCE_NAME
            && index == 0
            && matches!(&value, CValue::Pointer(pointer) if pointer.c_type().pointee_type().is_some());
        if !accepts_allocation_pointer && !parameter_type.accepts(&value) {
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
    assumptions: &PureFactContext,
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
    let population_bodies = match evaluate_resource_population_body_resources(
        returned_resources,
        actual_state,
        function.composite_resource_definitions(),
        assumptions,
        &mut budget,
        false,
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
            returned_resources
                .cached_support_exposing_fact(allocation, assumptions)
                .is_none()
                && expose_composite_resource_fact(
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
    assumptions: &PureFactContext,
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
            "allocation-delta checking requires concrete symbolic contract arguments".to_string(),
        )));
    };
    let mut output_state = with_contract_argument_views(state, function, &argument_values);
    if function.return_type() != CType::Void {
        set_function_result(&mut output_state, function, value.clone());
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
    assumptions: &PureFactContext,
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
    let Some(value) = coerce_function_return_value(value, function, &mut obligations, assumptions)
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
        set_function_result(&mut state, function, value.clone());
    }
    let population_transition = match apply_counted_population_transitions(
        caller_state,
        &mut state,
        function,
        argument_values,
        assumptions,
        true,
        false,
        budget,
    )? {
        Ok(transition) => transition,
        Err(error) => return Ok((CFunctionOutcome::RuntimeError(error), obligations)),
    };
    obligations.extend(population_transition.postcondition_obligations);
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
    assumptions: &PureFactContext,
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
    let Some(value) = coerce_function_return_value(value, function, &mut obligations, assumptions)
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
        set_function_result(&mut state, function, value.clone());
    }
    let population_transition = match crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "return counted population transition",
        || {
            apply_counted_population_transitions(
                caller_state,
                &mut state,
                function,
                argument_values,
                assumptions,
                reestablish_population_invariants,
                false,
                budget,
            )
        },
    )? {
        Ok(transition) => transition,
        Err(error) => return Ok((CFunctionOutcome::RuntimeError(error), obligations)),
    };
    obligations.extend(
        population_transition
            .postcondition_obligations
            .iter()
            .cloned(),
    );
    let caller_resources_after_requirements = match crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "return population resource update",
        || {
            apply_counted_population_transition_resources(
                transfer.caller_resources_after_requirements.clone(),
                &population_transition,
                assumptions,
            )
        },
    ) {
        Ok(resources) => resources,
        Err(error) => return Ok((CFunctionOutcome::RuntimeError(error), obligations)),
    };
    let output_resource_state = with_contract_argument_views(&state, function, argument_values);
    let return_resources = match crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "return resource evaluation",
        || {
            evaluate_function_return_resources(
                &caller_resources_after_requirements,
                &output_resource_state,
                function,
                assumptions,
                budget,
            )
        },
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
    match crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "return allocation obligation check",
        || unreturned_allocation_obligation(&state, &return_resources, function, assumptions),
    ) {
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
    return_state.next_local_frame = state.next_local_frame;
    Ok((
        CFunctionOutcome::Return {
            value,
            state: return_state,
        },
        obligations,
    ))
}

/// The function-exit rule the verification execution applies to a body
/// outcome, so that a completed proof path ends in the same contract-level
/// state an independent execution would: the contract's resource transfer
/// when a composite needs one at the outcome, the declared-population
/// transition when the contract changes counted quantities, and otherwise
/// the plain outcome. A void fallthrough completes as a return first.
pub(super) fn contract_exit_outcome(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    outcome: CStatementOutcome,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
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
            "contract exit rule requires symbolic value arguments".to_string(),
        )));
    };
    let outcome = complete_void_fallthrough(function, outcome);
    // A proof may hold the body's exit resources in a split representation
    // (one owned token twice rather than a quantity of two). Execution
    // composes its resources as it goes; compose the retained ones the same
    // way so the completed outcome is the canonical one certification compares.
    let outcome = match outcome {
        CStatementOutcome::Return { value, mut state } => {
            state.resources = match ResourceContext::new()
                .try_compose_with_facts(state.resources.facts().iter().cloned(), assumptions)
            {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(resource_context_runtime_error(error))),
            };
            CStatementOutcome::Return { value, state }
        }
        other => other,
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
    if function_needs_outcome_resource_transfer(function) {
        function_outcome_from_body_with_resource_transfer(
            caller_state,
            function,
            outcome,
            obligations,
            assumptions,
            &transfer,
            &argument_values,
            true,
            budget,
        )
        .map(Ok)
    } else if function_changes_declared_resource_quantities(function) {
        function_outcome_from_body_with_population_transition(
            caller_state,
            function,
            outcome,
            obligations,
            assumptions,
            &argument_values,
            budget,
        )
        .map(Ok)
    } else {
        Ok(Ok(function_outcome_from_body(
            caller_state,
            function,
            outcome,
            obligations,
            assumptions,
            None,
        )))
    }
}

pub(super) fn apply_verified_contract_resource_transition(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    outcome: CFunctionOutcome,
    assumptions: &PureFactContext,
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
    let (outcome, obligations) = crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "contract resource outcome reconstruction",
        || {
            function_outcome_from_body_with_resource_transfer(
                caller_state,
                function,
                statement_outcome,
                Vec::new(),
                assumptions,
                &transfer,
                &argument_values,
                false,
                budget,
            )
        },
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
    assumptions: &PureFactContext,
    return_resources: Option<&ResourceContext>,
) -> (CFunctionOutcome, Vec<ProofObligation>) {
    match outcome {
        CStatementOutcome::Return { value, mut state } => {
            let Some(value) =
                coerce_function_return_value(value, function, &mut obligations, assumptions)
            else {
                return (
                    CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                        "{} returned a value that does not match its declared type",
                        function.name()
                    ))),
                    obligations,
                );
            };
            let value = if function.return_aggregate_layout().is_some() {
                let Some(value) = materialize_aggregate_return(&mut state, function, value) else {
                    return (
                        CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                            "{} returned an invalid struct value",
                            function.name()
                        ))),
                        obligations,
                    );
                };
                value
            } else {
                value
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
        CStatementOutcome::Break(_) | CStatementOutcome::Continue(_) => (
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

#[cfg(test)]
mod provisional_ensure_obligation_tests {
    use super::*;

    #[test]
    fn provisional_ensure_loadability_work_ignores_unrelated_facts() {
        let memory = CMemory::new();
        let data = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let state = CState::new()
            .with_local("data", CValue::pointer(data.clone()))
            .with_memory(memory.clone());
        let ensure = SpecProposition::Comparison {
            left: SpecExpression::MemoryLoad {
                memory: SpecMemory::Current,
                pointer: Box::new(SpecExpression::PointerOffset {
                    pointer: Box::new(SpecExpression::CExpression(c_variable("data"))),
                    elements: Box::new(SpecExpression::CExpression(c_int32_literal(1))),
                    byte_width: 4,
                }),
                value_type: CType::Int32,
            },
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_int32_literal(0)),
        };
        let function = c_function(
            CType::Int32,
            "provisional_loadability_probe",
            vec![c_parameter("data", CType::Int32Pointer)],
            c_return(c_int32_literal(0)),
        )
        .with_contract(Vec::new(), vec![ensure], Vec::new(), Vec::new(), true);
        let base_assumptions =
            PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: data.clone(),
                bytes: Bitvector32Term::Constant(8),
            });
        let element_loadable = Proposition::CMemoryLoadable {
            memory,
            base: data.offset_by_int32_elements(Bitvector32Term::Constant(1)),
            bytes: Bitvector32Term::Constant(4),
        };
        let mut work_by_size = Vec::new();
        for unrelated_count in [16, 64, 256, 1024] {
            let mut assumptions = base_assumptions.clone();
            for index in 0..unrelated_count {
                assumptions = assumptions.assume_proposition(Proposition::Predicate {
                    name: format!("unrelated_{index}"),
                    arguments: Vec::new(),
                });
            }
            let mut facts = Vec::new();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                add_verified_function_ensure_facts(
                    &mut facts,
                    &[],
                    &state,
                    &state,
                    &function,
                    &assumptions,
                    &mut ExecutionBudget::new(),
                )
            });
            result.expect("the provisional ensure should lower");
            assert!(
                facts
                    .iter()
                    .any(|fact| fact.proposition() == &element_loadable),
                "contextual loadability must remain an explicit provisional obligation"
            );
            work_by_size.push((unrelated_count, work));
        }

        let baseline = work_by_size[0].1.max(1);
        let largest = work_by_size.last().unwrap().1;
        assert!(
            largest <= baseline * 2,
            "provisional ensure work should be independent of unrelated facts: {work_by_size:?}"
        );
    }
}
