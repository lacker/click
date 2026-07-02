use super::prelude::*;

#[derive(Clone, Debug, Eq, PartialEq)]
struct CFunctionResourceTransfer {
    callee_resources: ResourceContext,
    return_resources: ResourceContext,
}

pub(super) fn execute_c_function_paths(
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &Assumptions,
    environment: &CFunctionEnvironment,
    budget: &mut ExecutionBudget,
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
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
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
        for body_path in execute_c_statement_paths(
            &callee_state,
            function.body(),
            &body_assumptions,
            environment,
            budget,
        )? {
            let Some((facts, obligations)) = merge_path_facts_and_obligations(
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
            let (outcome, obligations) = function_outcome_from_body(
                state,
                function,
                body_path.outcome,
                obligations,
                &return_assumptions,
                None,
            );

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
    environment: &CFunctionEnvironment,
    budget: &mut ExecutionBudget,
    variables: &mut VerificationVariableGenerator,
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
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
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
        for body_path in execute_c_statement_verification_paths(
            &callee_state,
            function.body(),
            &body_assumptions,
            environment,
            budget,
            variables,
        )? {
            let Some((facts, obligations)) = merge_path_facts_and_obligations(
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
            let (outcome, obligations) = function_outcome_from_body(
                state,
                function,
                body_path.outcome,
                obligations,
                &return_assumptions,
                None,
            );

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
    environment: &CFunctionEnvironment,
    budget: &mut ExecutionBudget,
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
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
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
            budget,
        )? {
            let Some((facts, obligations)) = merge_path_facts_and_obligations(
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
            let (outcome, obligations) = function_outcome_from_body(
                caller_state,
                function,
                body_path.outcome,
                obligations,
                &return_assumptions,
                Some(&resource_transfer.return_resources),
            );

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
                let Some((facts, obligations)) = merge_path_facts_and_obligations(
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
    for (parameter, value) in function.parameters().iter().zip(values) {
        if !parameter.c_type().accepts(value) {
            return None;
        }
        callee_state.locals.set_typed(
            parameter.name().to_string(),
            value.clone(),
            parameter.c_type(),
        );
    }
    Some(callee_state)
}

fn prepare_function_resource_transfer(
    caller_state: &CState,
    callee_state: &CState,
    function: &CFunction,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CFunctionResourceTransfer, CRuntimeError>> {
    let required_resources = match evaluate_function_resource_context(
        callee_state,
        function.resource_requires(),
        assumptions,
        budget,
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    let ensured_resources = match evaluate_function_resource_context(
        callee_state,
        function.resource_ensures(),
        assumptions,
        budget,
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };

    let mut required_resource_list = required_resources.resources().to_vec();
    required_resource_list.sort_by_key(resource_transfer_priority);

    let mut return_resources = caller_state.resources().clone();
    for resource in &required_resource_list {
        let Some(resources) = return_resources.without_resource(resource, assumptions) else {
            return Ok(Err(CRuntimeError::MissingResource {
                resource: resource.clone(),
            }));
        };
        return_resources = resources;
    }
    return_resources = return_resources
        .with_resources_normalized(ensured_resources.resources().iter().cloned(), assumptions);
    if let Some(resource) = return_resources.duplicate_named_resource() {
        return Ok(Err(CRuntimeError::DuplicateResource {
            resource: resource.clone(),
        }));
    }
    if let Some((left, right)) = return_resources.overlapping_write_pair(assumptions) {
        return Ok(Err(CRuntimeError::OverlappingWriteResources {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        }));
    }

    Ok(Ok(CFunctionResourceTransfer {
        callee_resources: required_resources,
        return_resources,
    }))
}

fn evaluate_function_resource_context(
    state: &CState,
    resources: &[CResourceSpec],
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceContext, CRuntimeError>> {
    let mut context = ResourceContext::new();
    for resource in resources {
        let resource = match evaluate_function_resource_spec(state, resource, assumptions, budget)?
        {
            Ok(resource) => resource,
            Err(error) => return Ok(Err(error)),
        };
        context = context.with_resource(resource);
        if let Some(resource) = context.duplicate_named_resource() {
            return Ok(Err(CRuntimeError::DuplicateResource {
                resource: resource.clone(),
            }));
        }
        if let Some((left, right)) = context.overlapping_write_pair(assumptions) {
            return Ok(Err(CRuntimeError::OverlappingWriteResources {
                left: Box::new(left.clone()),
                right: Box::new(right.clone()),
            }));
        }
    }
    Ok(Ok(context))
}

fn evaluate_function_resource_spec(
    state: &CState,
    resource: &CResourceSpec,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CResource, CRuntimeError>> {
    match resource {
        CResourceSpec::Read(segment) => {
            let segment = match evaluate_loop_effect_segment(state, segment, assumptions, budget)? {
                Ok(segment) => segment,
                Err(_) => return Ok(Err(CRuntimeError::TypeMismatch)),
            };
            Ok(Ok(CResource::Read(CMemoryRange::new(
                segment.base,
                segment.start,
                segment.end,
            ))))
        }
        CResourceSpec::Write(segment) => {
            let segment = match evaluate_loop_effect_segment(state, segment, assumptions, budget)? {
                Ok(segment) => segment,
                Err(_) => return Ok(Err(CRuntimeError::TypeMismatch)),
            };
            Ok(Ok(CResource::Write(CMemoryRange::new(
                segment.base,
                segment.start,
                segment.end,
            ))))
        }
        CResourceSpec::Free(segment) => {
            let segment = match evaluate_loop_effect_segment(state, segment, assumptions, budget)? {
                Ok(segment) => segment,
                Err(_) => return Ok(Err(CRuntimeError::TypeMismatch)),
            };
            Ok(Ok(CResource::Free(CMemoryRange::new(
                segment.base,
                segment.start,
                segment.end,
            ))))
        }
        CResourceSpec::Named {
            name,
            arguments,
            parameter_types,
        } => {
            if arguments.len() != parameter_types.len() {
                return Ok(Err(CRuntimeError::TypeMismatch));
            }
            let mut values = Vec::new();
            for (index, (argument, parameter_type)) in
                arguments.iter().zip(parameter_types).enumerate()
            {
                let value = match evaluate_loop_effect_segment_value(
                    state,
                    argument,
                    assumptions,
                    &format!("resource `{name}` argument {index}"),
                    budget,
                )? {
                    Ok(value) => value,
                    Err(_) => return Ok(Err(CRuntimeError::TypeMismatch)),
                };
                if !parameter_type.accepts(&value) {
                    return Ok(Err(CRuntimeError::TypeMismatch));
                }
                values.push(value);
            }
            Ok(Ok(CResource::Named {
                name: name.clone(),
                arguments: values,
            }))
        }
    }
}

fn resource_transfer_priority(resource: &CResource) -> u8 {
    match resource {
        CResource::Read(_) => 0,
        CResource::Write(_) => 1,
        CResource::Free(_) => 2,
        CResource::Named { .. } => 3,
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
                    CFunctionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    obligations,
                );
            };

            let mut caller_state = caller_state.clone();
            caller_state.memory = state.memory;
            caller_state.resources = return_resources.cloned().unwrap_or(state.resources);
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
