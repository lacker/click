use super::prelude::*;

#[derive(Clone, Debug, Eq, PartialEq)]
struct CFunctionResourceTransfer {
    callee_resources: ResourceContext,
    caller_resources_after_requirements: ResourceContext,
    return_resources: ResourceContext,
}

pub(super) fn execute_c_function_paths(
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &Assumptions,
    environment: &CFunctionEnvironment,
    call_semantics: CCallSemantics,
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
            call_semantics,
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
    call_semantics: CCallSemantics,
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
            call_semantics,
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
    call_semantics: CCallSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    match call_semantics {
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
            call_semantics,
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

fn execute_verified_function_rule(
    caller_state: &CState,
    rule: &CVerifiedFunctionRule,
    arguments: &[CExpression],
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    let function = &rule.function;
    budget.consume_function_call()?;
    let call = budget.allocate_opaque_call();
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
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
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
        entry_state.resources = transfer.callee_resources;
        let entry_contract_state =
            with_contract_argument_views(&entry_state, &arguments_path.values);

        let mut obligations = arguments_path.obligations;
        let mut facts = arguments_path.facts;
        for requirement in function.contract_requires() {
            let requirement_paths = lower_spec_proposition_at_state_with_loop_entry(
                &entry_contract_state,
                requirement,
                Some(&entry_contract_state),
                &path_assumptions,
                budget,
            )?;
            let Some(requirement_path) = requirement_paths.into_iter().next() else {
                obligations.push(
                    ProofObligation::verification_condition(false_equals_true_proposition())
                        .with_context(format!("{} precondition", function.name())),
                );
                continue;
            };
            obligations.extend(requirement_path.obligations);
            obligations.push(
                ProofObligation::verification_condition(requirement_path.proposition)
                    .with_context(format!("{} precondition", function.name())),
            );
            facts.extend(requirement_path.facts);
        }

        let effective_assumptions =
            assumptions_with_path_context(assumptions, &facts, &obligations);
        let footprint_state = entry_contract_state.clone();
        let mut mutable_ranges = Vec::new();
        let mut footprint_error = None;
        for segment in function.contract_mutable() {
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
                Variable(8_000_000 + call),
                &mutable_ranges,
                &effective_assumptions,
            )
        };
        if !mutable_ranges.is_empty() {
            facts.push(ExecutionPureFact::new(Proposition::CMemoryEffectSummary {
                before: entry_state.memory.clone(),
                after: memory.clone(),
                mutable_ranges: mutable_ranges.clone(),
            }));
        }
        let result = symbolic_call_result(function.return_type(), Variable(8_100_000 + call));
        let mut post_state = entry_state.clone().with_memory(memory);
        post_state
            .locals
            .set_typed("result".to_string(), result.clone(), function.return_type());
        post_state.resources = transfer.return_resources.clone();
        let output_resource_state =
            with_contract_argument_views(&post_state, &arguments_path.values);

        let ensured_resources = match evaluate_function_resource_context(
            &output_resource_state,
            function.resource_ensures(),
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
        let return_resources = match transfer
            .caller_resources_after_requirements
            .try_compose_with_facts(
                ensured_resources.facts().iter().cloned(),
                &effective_assumptions,
            ) {
            Ok(resources) => resources,
            Err(error) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(resource_context_runtime_error(error)),
                    facts,
                    obligations,
                });
                continue;
            }
        };
        post_state.resources = return_resources.clone();
        let post_contract_state = with_contract_argument_views(&post_state, &arguments_path.values);

        for ensure in function.contract_ensures() {
            let ensure_paths = lower_spec_proposition_at_state_with_loop_entry(
                &post_contract_state,
                ensure,
                Some(&entry_contract_state),
                &effective_assumptions,
                budget,
            )?;
            for ensure_path in ensure_paths.into_iter().take(1) {
                facts.extend(ensure_path.facts);
                facts.push(ExecutionPureFact::new(ensure_path.proposition));
            }
        }

        let mut return_state = caller_state.clone();
        return_state.memory = post_state.memory;
        return_state.resources = return_resources;
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

fn with_contract_argument_views(state: &CState, values: &[CValue]) -> CState {
    let mut state = state.clone();
    for value in values {
        if let CValue::Pointer(pointer) = value {
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
        CType::Int32 => CValue::Int32(Bitvector32Term::Variable(variable)),
        CType::UInt8 => CValue::UInt8(Bitvector32Term::Variable(variable)),
        CType::Int32Pointer => CValue::Pointer(Pointer {
            block: format!("call-result:{}", variable.0).into(),
            offset: PointerOffsetTerm::Constant(0),
        }),
        CType::UInt8Pointer => CValue::Pointer(Pointer {
            block: format!("call-result:{}", variable.0).into(),
            offset: PointerOffsetTerm::Constant(0),
        }),
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
        let Some(resources) = return_resources.without_fact(resource, assumptions) else {
            return Ok(Err(CRuntimeError::MissingResource {
                resource: resource.clone(),
            }));
        };
        return_resources = resources;
    }
    let caller_resources_after_requirements = return_resources.clone();
    return_resources = match return_resources
        .try_compose_with_facts(ensured_resources.facts().iter().cloned(), assumptions)
    {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(resource_context_runtime_error(error))),
    };

    Ok(Ok(CFunctionResourceTransfer {
        callee_resources: required_resources,
        caller_resources_after_requirements,
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

fn evaluate_function_resource_spec(
    state: &CState,
    resource: &CResourceSpec,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CResourceFact, CRuntimeError>> {
    match resource {
        CResourceSpec::Read(segment) => {
            let segment = match evaluate_loop_effect_segment(state, segment, assumptions, budget)? {
                Ok(segment) => segment,
                Err(_) => return Ok(Err(CRuntimeError::TypeMismatch)),
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
                Err(_) => return Ok(Err(CRuntimeError::TypeMismatch)),
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
        return Ok(Err(CRuntimeError::TypeMismatch));
    }
    let mut values = Vec::new();
    for (index, (argument, parameter_type)) in arguments.iter().zip(parameter_types).enumerate() {
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
    let resource = match family {
        ResourceFamily::Composite => CResource::Composite {
            name: name.to_string(),
            arguments: values,
        },
        ResourceFamily::Token => CResource::Token {
            name: name.to_string(),
            arguments: values,
        },
        ResourceFamily::Memory => return Ok(Err(CRuntimeError::TypeMismatch)),
    };
    Ok(Ok(match access {
        CResourceAccessMode::Own => CResourceFact::Own(resource),
        CResourceAccessMode::View => CResourceFact::View(resource),
    }))
}

fn resource_fact_transfer_priority(resource: &CResourceFact) -> u8 {
    match resource {
        CResourceFact::View(_) => 0,
        CResourceFact::Own(CResource::Memory(_)) => 1,
        CResourceFact::Own(CResource::Composite { .. } | CResource::Token { .. }) => 2,
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
