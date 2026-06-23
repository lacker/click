fn execute_c_function_paths(
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

            paths.push(CFunctionPath {
                outcome: function_outcome_from_body(caller_state, function, body_path.outcome),
                facts,
                obligations,
            });
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn execute_c_function_verification_paths(
    caller_state: &CState,
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

            paths.push(CFunctionPath {
                outcome: function_outcome_from_body(caller_state, function, body_path.outcome),
                facts,
                obligations,
            });
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn add_memory_store_obligation(
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

fn evaluate_c_arguments_paths(
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

fn bind_c_function_arguments(
    caller_state: &CState,
    function: &CFunction,
    values: &[CValue],
) -> Option<CState> {
    let mut callee_state = CState::new().with_memory(caller_state.memory.clone());
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

fn function_outcome_from_body(
    caller_state: &CState,
    function: &CFunction,
    outcome: CStatementOutcome,
) -> CFunctionOutcome {
    match outcome {
        CStatementOutcome::Return { value, state } => {
            if !function.return_type().accepts(&value) {
                return CFunctionOutcome::RuntimeError(CRuntimeError::TypeMismatch);
            }

            let mut caller_state = caller_state.clone();
            caller_state.memory = state.memory;
            CFunctionOutcome::Return {
                value,
                state: caller_state,
            }
        }
        CStatementOutcome::Normal(_) => {
            CFunctionOutcome::RuntimeError(CRuntimeError::MissingReturn)
        }
        CStatementOutcome::UndefinedBehavior(undefined_behavior) => {
            CFunctionOutcome::UndefinedBehavior(undefined_behavior)
        }
        CStatementOutcome::RuntimeError(error) => CFunctionOutcome::RuntimeError(error),
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
