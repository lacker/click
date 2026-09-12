use super::prelude::*;

#[cfg(test)]
mod pointee_const_return_tests {
    use super::*;
    // Surface planning; only this test reaches it from inside the kernel.
    use crate::surface::planning::proposition_search::PropositionSearch;

    #[test]
    fn pointee_const_return_rebinding_is_allowed_but_store_through_pointer_is_not() {
        let value = CValue::typed_pointer(Pointer::symbolic(Variable(916)), CType::Int32Pointer);
        let mut state = CState::new().with_local("p", value.clone());
        state.locals.set_typed_with_all_qualifiers(
            "q",
            value,
            CType::Int32Pointer,
            false,
            false,
            false,
            true,
        );
        let environment = CExecutionEnvironment::new();
        let paths = execute_c_statement_paths(
            &state,
            &c_assign("q", c_variable("p")),
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        let CStatementOutcome::Normal(state) = &paths[0].outcome else {
            panic!("const pointee does not prohibit rebinding")
        };
        assert!(matches!(
            state.locals.binding("q"),
            Some(CLocalBinding::Object {
                pointee_constant: true,
                ..
            })
        ));
        let paths = execute_c_statement_paths(
            state,
            &c_store(c_variable("q"), c_int32_literal(1)),
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        assert!(matches!(
            &paths[0].outcome,
            CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory)
        ));
    }

    #[test]
    fn pointee_const_return_inline_call_preserves_pointer_identity() {
        let function = CFunction::new(
            CType::Int32Pointer,
            "view",
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_variable("p")),
        )
        .with_return_pointee_constant(true)
        .with_inline_body();
        let value = CValue::typed_pointer(Pointer::symbolic(Variable(917)), CType::Int32Pointer);
        let state = CState::new().with_local("p", value.clone());
        let environment = CExecutionEnvironment::new().with_function(function);
        let paths = execute_c_call_assign_paths(
            &state,
            "temporary",
            "view",
            &[c_variable("p")],
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        let CStatementOutcome::Normal(state) = &paths[0].outcome else {
            panic!("inline call must return")
        };
        let result = state.locals.get("temporary").unwrap();
        assert!(matches!(result, CValue::Pointer(pointer) if pointer.pointee_constant()));
        let equality =
            c_value_comparison_proposition(result, CComparisonOperator::Equal, &value).unwrap();
        assert!(PureFactContext::new().proves(&equality));
        assert!(paths[0].obligations.is_empty());
    }

    #[test]
    fn pointee_const_return_direct_and_callback_calls_preserve_const() {
        let function = CFunction::new(
            CType::UInt8Pointer,
            "text",
            Vec::new(),
            c_return(c_int32_literal(0)),
        )
        .with_return_pointee_constant(true);
        let function_type = function.function_pointer_type();
        let environment = CExecutionEnvironment::new().with_function(function);
        let paths = execute_c_call_assign_paths(
            &CState::new(),
            "temporary",
            "text",
            &[],
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        assert!(matches!(&paths[0].outcome, CStatementOutcome::Normal(state)
            if matches!(state.locals.binding("temporary"), Some(CLocalBinding::Object { pointee_constant: true, .. }))));
        let state = CState::new().with_local(
            "callback",
            CValue::typed_pointer(
                Pointer {
                    block: PointerBlock::Function("text".to_string()),
                    offset: PointerOffsetTerm::Constant(0),
                },
                function_type,
            ),
        );
        let paths = execute_c_call_assign_paths(
            &state,
            "temporary",
            "callback",
            &[],
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        assert!(matches!(&paths[0].outcome, CStatementOutcome::Normal(state)
            if matches!(state.locals.binding("temporary"), Some(CLocalBinding::Object { pointee_constant: true, .. }))));

        let state = state.with_local(
            "mutable",
            CValue::typed_pointer(Pointer::null(), CType::UInt8Pointer),
        );
        let paths = execute_c_call_assign_paths(
            &state,
            "mutable",
            "callback",
            &[],
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        assert!(matches!(
            &paths[0].outcome,
            CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
        ));

        let incompatible =
            CType::FunctionPointer(CType::function_pointer_signature(CType::UInt8Pointer, &[]));
        let state = CState::new().with_local(
            "callback",
            CValue::typed_pointer(
                Pointer {
                    block: PointerBlock::Function("text".into()),
                    offset: PointerOffsetTerm::Constant(0),
                },
                incompatible,
            ),
        );
        let paths = execute_c_call_assign_paths(
            &state,
            "temporary",
            "callback",
            &[],
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        assert!(matches!(
            &paths[0].outcome,
            CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(_))
        ));
    }

    #[test]
    fn pointee_const_return_assignment_preserves_destination_and_temporary_qualifiers() {
        for source_const in [false, true] {
            for destination_const in [false, true] {
                for immutable in [false, true] {
                    let value = CValue::typed_pointer(
                        Pointer::symbolic(Variable(912)),
                        CType::UInt8Pointer,
                    )
                    .with_pointer_pointee_constant(source_const);
                    let mut state = CState::new();
                    state.locals.set_typed_with_all_qualifiers(
                        "text",
                        value.clone(),
                        CType::UInt8Pointer,
                        false,
                        false,
                        immutable,
                        destination_const,
                    );
                    let result = assign_call_result(
                        &mut state,
                        "text",
                        value,
                        &mut Vec::new(),
                        &PureFactContext::new(),
                    );
                    assert_eq!(
                        result.is_some(),
                        !immutable && (!source_const || destination_const)
                    );
                    if result.is_some() {
                        assert!(
                            matches!(state.locals.binding("text"), Some(CLocalBinding::Object { value: CValue::Pointer(pointer), pointee_constant, .. })
                            if *pointee_constant == destination_const && pointer.pointee_constant() == destination_const)
                        );
                    }
                }
            }
        }
        let value = CValue::typed_pointer(Pointer::symbolic(Variable(913)), CType::UInt8Pointer)
            .with_pointer_pointee_constant(true);
        let mut state = CState::new();
        assert!(
            assign_call_result(
                &mut state,
                "temporary",
                value,
                &mut Vec::new(),
                &PureFactContext::new()
            )
            .is_some()
        );
        assert!(matches!(
            state.locals.binding("temporary"),
            Some(CLocalBinding::Object {
                pointee_constant: true,
                ..
            })
        ));
    }

    #[test]
    fn pointee_const_return_symbolic_callback_checks_signature_and_destination() {
        let template = CFunction::new(CType::Int32Pointer, "view", vec![], CStatement::Skip)
            .with_return_pointee_constant(true)
            .with_contract(vec![], vec![], vec![], vec![], true);
        let contract = CFunctionContract::new("View", template).unwrap();
        let qualified = contract.function_pointer_type();
        let unqualified =
            CType::FunctionPointer(CType::function_pointer_signature(CType::Int32Pointer, &[]));
        let pointer = Pointer {
            block: PointerBlock::FunctionSymbolic(Variable(890)),
            offset: PointerOffsetTerm::Constant(0),
        };
        let value = CValue::typed_pointer(pointer.clone(), qualified);
        let assumptions = PureFactContext::new().assume_proposition(Proposition::Predicate {
            name: contract.predicate_name(),
            arguments: vec![Term::CState(CState::new()), Term::CValue(value)],
        });
        let environment = CExecutionEnvironment::new().with_function_contract(contract);
        for (signature, mutable_destination) in
            [(qualified, false), (qualified, true), (unqualified, false)]
        {
            let mut state = CState::new().with_local(
                "callback",
                CValue::typed_pointer(pointer.clone(), signature),
            );
            if mutable_destination {
                state = state.with_local(
                    "temporary",
                    CValue::typed_pointer(Pointer::null(), CType::Int32Pointer),
                );
            }
            let paths = execute_c_call_assign_paths(
                &state,
                "temporary",
                "callback",
                &[],
                &assumptions,
                &environment,
                CExecutionSemantics::EXECUTE_BODIES,
                &mut ExecutionBudget::default(),
            )
            .unwrap();
            if signature == qualified && !mutable_destination {
                assert!(matches!(&paths[0].outcome, CStatementOutcome::Normal(state)
                    if matches!(state.locals.binding("temporary"), Some(CLocalBinding::Object { value: CValue::Pointer(pointer), pointee_constant: true, .. }) if pointer.pointee_constant())));
            } else {
                assert!(matches!(
                    &paths[0].outcome,
                    CStatementOutcome::RuntimeError(_)
                ));
            }
        }
    }
}

fn assign_call_result(
    state: &mut CState,
    target: &str,
    value: CValue,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<()> {
    if value == CValue::Void {
        return None;
    }
    let (c_type, volatile, pointee_volatile, pointee_constant) = match state.locals.binding(target)
    {
        Some(
            CLocalBinding::Object {
                c_type,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
                ..
            }
            | CLocalBinding::UninitializedObject {
                c_type,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
                ..
            }
            | CLocalBinding::GlobalObject {
                c_type,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
                ..
            },
        ) => {
            if *constant {
                return None;
            }
            (*c_type, *volatile, *pointee_volatile, *pointee_constant)
        }
        Some(_) => return None,
        None => (
            value.c_type(),
            false,
            false,
            matches!(&value, CValue::Pointer(pointer) if pointer.pointee_constant()),
        ),
    };
    let value = super::functions::coerce_c_value_with_pointee_constant(
        value,
        c_type,
        pointee_constant,
        obligations,
        assumptions,
    )?
    .with_pointer_pointee_volatile(pointee_volatile);
    sync_stack_local(state, target, &value);
    state.locals.set_typed_with_all_qualifiers(
        target.to_string(),
        value,
        c_type,
        volatile,
        pointee_volatile,
        false,
        pointee_constant,
    );
    Some(())
}

pub(super) fn execute_c_call_assign_paths(
    state: &CState,
    target: &str,
    function_name: &str,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    if function_name == "realloc" {
        if environment.selected_call_contract.is_some() {
            return Ok(vec![CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(
                    "step(Contract) requires a function-pointer call".to_string(),
                )),
                facts: Vec::new(),
                obligations: Vec::new(),
            }]);
        }
        return execute_c_realloc_assign_paths(state, target, arguments, assumptions, budget);
    }

    if let Some(CType::FunctionPointer(signature)) = state.locals.object_type(function_name) {
        return execute_c_indirect_call_assign_paths(
            state,
            target,
            function_name,
            CType::FunctionPointer(signature),
            arguments,
            assumptions,
            environment,
            execution_semantics,
            budget,
        );
    }

    let Some(function) = environment.get_function(function_name) else {
        return Ok(vec![CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::UnknownFunction(
                function_name.to_string(),
            )),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    };

    let paths = execute_c_function_call_paths(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
    )?
    .into_iter()
    .map(|mut path| {
        let outcome = match path.outcome {
            CFunctionOutcome::Return { value, mut state } => {
                if value == CValue::Void {
                    return CStatementExecutionPath {
                        outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: path.facts,
                        obligations: path.obligations,
                    };
                }
                if let Some(layout) = function.return_aggregate_layout() {
                    if matches!(
                        state.locals.binding(target),
                        Some(CLocalBinding::AggregateObject { constant: true, .. })
                    ) {
                        return CStatementExecutionPath {
                            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            facts: path.facts,
                            obligations: path.obligations,
                        };
                    }
                    let Some(target_layout) = state.locals.aggregate_layout(target) else {
                        return CStatementExecutionPath {
                            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            facts: path.facts,
                            obligations: path.obligations,
                        };
                    };
                    if target_layout != layout {
                        return CStatementExecutionPath {
                            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            facts: path.facts,
                            obligations: path.obligations,
                        };
                    }
                    let CValue::Pointer(pointer) = &value else {
                        return CStatementExecutionPath {
                            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            facts: path.facts,
                            obligations: path.obligations,
                        };
                    };
                    if pointer.is_null() {
                        return CStatementExecutionPath {
                            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            facts: path.facts,
                            obligations: path.obligations,
                        };
                    }
                    let Some(slot) = state.locals.slot(target).cloned() else {
                        return CStatementExecutionPath {
                            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            facts: path.facts,
                            obligations: path.obligations,
                        };
                    };
                    let next_memory = match copy_aggregate_fields_checked(
                        state.memory.clone(),
                        pointer.pointer(),
                        &slot,
                        layout,
                    ) {
                        Ok(memory) => memory,
                        Err(undefined_behavior) => {
                            return CStatementExecutionPath {
                                outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                                facts: path.facts,
                                obligations: path.obligations,
                            };
                        }
                    };
                    state.set_memory(next_memory);
                    return CStatementExecutionPath {
                        outcome: CStatementOutcome::Normal(state),
                        facts: path.facts,
                        obligations: path.obligations,
                    };
                }
                if state.locals.is_array_object(target) {
                    return CStatementExecutionPath {
                        outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: path.facts,
                        obligations: path.obligations,
                    };
                }
                if assign_call_result(
                    &mut state,
                    target,
                    value,
                    &mut path.obligations,
                    assumptions,
                )
                .is_some()
                {
                    CStatementOutcome::Normal(state)
                } else {
                    CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
                }
            }
            CFunctionOutcome::VerificationDiverges => CStatementOutcome::VerificationDiverges,
            CFunctionOutcome::UndefinedBehavior(undefined_behavior) => {
                CStatementOutcome::UndefinedBehavior(undefined_behavior)
            }
            CFunctionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
        };

        CStatementExecutionPath {
            outcome,
            facts: path.facts,
            obligations: path.obligations,
        }
    })
    .collect::<Vec<_>>();
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_call_paths(
    state: &CState,
    function_name: &str,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    if let Some(CType::FunctionPointer(signature)) = state.locals.object_type(function_name) {
        let paths = execute_c_indirect_call_paths(
            state,
            function_name,
            CType::FunctionPointer(signature),
            arguments,
            assumptions,
            environment,
            execution_semantics,
            budget,
        )?
        .into_iter()
        .map(|path| CStatementExecutionPath {
            outcome: match path.outcome {
                CFunctionOutcome::Return { state, .. } => CStatementOutcome::Normal(state),
                CFunctionOutcome::VerificationDiverges => CStatementOutcome::VerificationDiverges,
                CFunctionOutcome::UndefinedBehavior(error) => {
                    CStatementOutcome::UndefinedBehavior(error)
                }
                CFunctionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
            },
            facts: path.facts,
            obligations: path.obligations,
        })
        .collect::<Vec<_>>();
        budget.check_path_width(paths.len())?;
        return Ok(paths);
    }

    let Some(function) = environment.get_function(function_name) else {
        return Ok(vec![CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::UnknownFunction(
                function_name.to_string(),
            )),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    };

    let paths = execute_c_function_call_paths(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
    )?
    .into_iter()
    .map(|path| CStatementExecutionPath {
        outcome: match path.outcome {
            CFunctionOutcome::Return { state, .. } => CStatementOutcome::Normal(state),
            CFunctionOutcome::VerificationDiverges => CStatementOutcome::VerificationDiverges,
            CFunctionOutcome::UndefinedBehavior(undefined_behavior) => {
                CStatementOutcome::UndefinedBehavior(undefined_behavior)
            }
            CFunctionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
        },
        facts: path.facts,
        obligations: path.obligations,
    })
    .collect::<Vec<_>>();
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn execute_c_indirect_call_assign_paths(
    state: &CState,
    target: &str,
    function_name: &str,
    function_type: CType,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let paths = execute_c_indirect_call_paths(
        state,
        function_name,
        function_type,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
    )?;
    Ok(paths
        .into_iter()
        .map(|mut path| {
            let outcome = match path.outcome {
                CFunctionOutcome::Return { value, mut state } => {
                    if value == CValue::Void || state.locals.is_array_object(target) {
                        CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
                    } else if assign_call_result(
                        &mut state,
                        target,
                        value,
                        &mut path.obligations,
                        assumptions,
                    )
                    .is_some()
                    {
                        CStatementOutcome::Normal(state)
                    } else {
                        CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
                    }
                }
                CFunctionOutcome::VerificationDiverges => CStatementOutcome::VerificationDiverges,
                CFunctionOutcome::UndefinedBehavior(undefined_behavior) => {
                    CStatementOutcome::UndefinedBehavior(undefined_behavior)
                }
                CFunctionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
            };
            CStatementExecutionPath {
                outcome,
                facts: path.facts,
                obligations: path.obligations,
            }
        })
        .collect())
}

fn execute_c_indirect_call_paths(
    state: &CState,
    function_name: &str,
    function_type: CType,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    if function_type == CType::FunctionPointer(CallbackSignature::UNSPECIFIED) {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                "indirect calls require a supported callback signature".into(),
            )),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    }
    let mut paths = Vec::new();
    for target_path in evaluate_c_expression_paths(
        state,
        &c_variable(function_name.to_string()),
        assumptions,
        budget,
    )? {
        let CExpressionPath {
            outcome,
            facts,
            obligations,
        } = target_path;
        let target_names = match outcome {
            CExpressionOutcome::Value(CValue::Pointer(pointer))
                if pointer.offset == PointerOffsetTerm::Constant(0) =>
            {
                match &pointer.block {
                    PointerBlock::Function(name)
                        if environment.selected_call_contract.is_none() =>
                    {
                        vec![Ok(name.clone())]
                    }
                    PointerBlock::FunctionSymbolic(_) | PointerBlock::Function(_) => {
                        let target_assumptions =
                            assumptions_with_path_context(assumptions, &facts, &obligations);
                        let contracts = target_assumptions
                            .function_contract_facts_for(pointer.pointer())
                            .filter_map(|(name, _)| environment.get_function_contract(name))
                            .filter(|contract| contract.function_pointer_type() == function_type)
                            .collect::<Vec<_>>();
                        if let Some(selected) = &environment.selected_call_contract
                            && !contracts
                                .iter()
                                .any(|contract| contract.name() == selected.as_ref())
                        {
                            paths.push(CFunctionPath {
                                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                                    format!("contract `{selected}` is not established for this callback with its call signature"))),
                                facts, obligations,
                            });
                            continue;
                        }
                        if contracts.is_empty() {
                            paths.push(CFunctionPath {
                                outcome: CFunctionOutcome::RuntimeError(
                                    CRuntimeError::AbstractFunctionPointerCall(
                                        function_name.to_string(),
                                    ),
                                ),
                                facts,
                                obligations,
                            });
                            continue;
                        }
                        for mut call_path in execute_c_function_contracts_paths(
                            state,
                            &contracts,
                            arguments,
                            &target_assumptions,
                            environment,
                            budget,
                        )? {
                            let mut merged_facts = facts.clone();
                            merged_facts.extend(call_path.facts);
                            let mut merged_obligations = obligations.clone();
                            merged_obligations.extend(call_path.obligations);
                            call_path.facts = merged_facts;
                            call_path.obligations = merged_obligations;
                            paths.push(call_path);
                        }
                        continue;
                    }
                    _ => vec![Err(CRuntimeError::TypeMismatch)],
                }
            }
            CExpressionOutcome::Value(_) => vec![Err(CRuntimeError::TypeMismatch)],
            CExpressionOutcome::UndefinedBehavior(error) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::UndefinedBehavior(error),
                    facts,
                    obligations,
                });
                continue;
            }
            CExpressionOutcome::RuntimeError(error) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                });
                continue;
            }
        };

        for target_name in target_names {
            let Ok(target_name) = target_name else {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(target_name.unwrap_err()),
                    facts: facts.clone(),
                    obligations: obligations.clone(),
                });
                continue;
            };
            let Some(function) = environment.get_function(&target_name) else {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(CRuntimeError::UnknownFunction(
                        target_name,
                    )),
                    facts: facts.clone(),
                    obligations: obligations.clone(),
                });
                continue;
            };
            if function.function_pointer_type() != function_type {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                        format!(
                            "function pointer target `{}` has an incompatible signature",
                            function.name()
                        ),
                    )),
                    facts: facts.clone(),
                    obligations: obligations.clone(),
                });
                continue;
            }
            let target_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            for mut call_path in execute_c_function_call_paths(
                state,
                function,
                arguments,
                &target_assumptions,
                environment,
                execution_semantics,
                budget,
            )? {
                let mut merged_facts = facts.clone();
                merged_facts.extend(call_path.facts);
                let mut merged_obligations = obligations.clone();
                merged_obligations.extend(call_path.obligations);
                call_path.facts = merged_facts;
                call_path.obligations = merged_obligations;
                paths.push(CFunctionPath {
                    outcome: call_path.outcome,
                    facts: call_path.facts,
                    obligations: call_path.obligations,
                });
            }
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_statement_paths_with_prefix(
    state: &CState,
    statement: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    prefix_facts: &[ExecutionPureFact],
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let effective_assumptions =
        assumptions_with_path_context(assumptions, prefix_facts, prefix_obligations);
    let paths = execute_c_statement_paths(
        state,
        statement,
        &effective_assumptions,
        environment,
        execution_semantics,
        budget,
    )?
    .into_iter()
    .filter_map(|path| {
        let (facts, obligations) = merge_execution_pure_facts_and_obligations(
            prefix_facts,
            prefix_obligations,
            &path.facts,
            &path.obligations,
            assumptions,
        )?;
        Some(CStatementExecutionPath {
            outcome: path.outcome,
            facts,
            obligations,
        })
    })
    .collect::<Vec<_>>();
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_statement_verification_paths(
    state: &CState,
    statement: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    // `Seq` only groups source statements; it is not another statement step.
    if !matches!(statement, CStatement::Seq(_, _)) {
        budget.consume_statement_step()?;
    }
    if execution_semantics.loops == CLoopSemantics::ApplyVerifiedRules
        && matches!(
            statement,
            CStatement::While {
                invariant_checks,
                effect_checks,
                ..
            } if !invariant_checks.is_empty() || !effect_checks.is_empty()
        )
    {
        let Some(rule) = environment.applicable_verified_loop_rule(state, statement, assumptions)
        else {
            return Ok(Vec::new());
        };
        let paths = rule
            .paths
            .iter()
            .cloned()
            .map(|mut path| {
                path.facts = path
                    .facts
                    .into_iter()
                    .map(ExecutionPureFact::into_certified)
                    .collect();
                path
            })
            .collect::<Vec<_>>();
        budget.check_path_width(paths.len())?;
        return Ok(paths);
    }
    let paths = match statement {
        CStatement::Seq(first, second) => {
            let mut paths = Vec::new();
            for first_path in execute_c_statement_verification_paths(
                state,
                first,
                assumptions,
                environment,
                execution_semantics,
                budget,
                variables,
            )? {
                match first_path.outcome {
                    CStatementOutcome::Normal(state) => {
                        paths.extend(execute_c_statement_verification_paths_with_prefix(
                            &state,
                            second,
                            assumptions,
                            environment,
                            execution_semantics,
                            &first_path.facts,
                            &first_path.obligations,
                            budget,
                            variables,
                        )?);
                    }
                    outcome @ (CStatementOutcome::Break(_)
                    | CStatementOutcome::Continue(_)
                    | CStatementOutcome::Return { .. }
                    | CStatementOutcome::VerificationDiverges
                    | CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_)) => paths.push(CStatementExecutionPath {
                        outcome,
                        facts: first_path.facts,
                        obligations: first_path.obligations,
                    }),
                }
            }
            paths
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut paths = Vec::new();
            for condition_path in
                evaluate_c_expression_paths(state, condition, assumptions, budget)?
            {
                let CExpressionPath {
                    outcome,
                    facts,
                    obligations,
                } = condition_path;
                match outcome {
                    CExpressionOutcome::Value(value) => {
                        for truthiness_path in
                            c_truthiness_paths(value, facts, obligations, assumptions)
                        {
                            let branch = if truthiness_path.is_true {
                                then_branch
                            } else {
                                else_branch
                            };
                            let branch_assumptions = assumptions_with_path_context(
                                assumptions,
                                &truthiness_path.facts,
                                &truthiness_path.obligations,
                            );
                            let branch_state =
                                resolve_pending_heap_allocations(state, &branch_assumptions);
                            paths.extend(execute_c_statement_verification_paths_with_prefix(
                                &branch_state,
                                branch,
                                assumptions,
                                environment,
                                execution_semantics,
                                &truthiness_path.facts,
                                &truthiness_path.obligations,
                                budget,
                                variables,
                            )?);
                        }
                    }
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                        paths.push(CStatementExecutionPath {
                            outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                            facts,
                            obligations,
                        })
                    }
                    CExpressionOutcome::RuntimeError(error) => {
                        paths.push(CStatementExecutionPath {
                            outcome: CStatementOutcome::RuntimeError(error),
                            facts,
                            obligations,
                        })
                    }
                }
            }
            paths
        }
        CStatement::While {
            condition,
            invariant,
            invariant_checks,
            effect_checks,
            resource_specs,
            ranking_measures,
            structural_measure,
            body,
            do_while,
        } if !invariant_checks.is_empty()
            || !effect_checks.is_empty()
            || !ranking_measures.is_empty()
            || structural_measure.is_some() =>
        {
            execute_c_while_verification_paths(
                state,
                condition,
                invariant,
                invariant_checks,
                effect_checks,
                resource_specs,
                ranking_measures,
                structural_measure.as_deref(),
                body,
                assumptions,
                environment,
                execution_semantics,
                budget,
                variables,
                *do_while,
            )?
        }
        _ => {
            // Loop verification and verified-call execution share one symbolic
            // identity stream. The loop paths allocate through `variables`,
            // while ordinary statement execution allocates opaque-call
            // identities through `budget`; synchronize both sides before and
            // after crossing that boundary so neither can reuse an identity.
            budget.next_kernel_variable = budget.next_kernel_variable.max(variables.next);
            let operation = match statement {
                CStatement::Skip => "verification statement: skip",
                CStatement::Break => "verification statement: break",
                CStatement::Continue => "verification statement: continue",
                CStatement::ContinueWithStep { .. } => {
                    "verification statement: continue with for step"
                }
                CStatement::Declare { .. } => "verification statement: declare",
                CStatement::DeclareAggregate { .. } => "verification statement: declare aggregate",
                CStatement::CopyAggregate { .. } => "verification statement: aggregate copy",
                CStatement::Assign { .. } => "verification statement: assign",
                CStatement::CallAssign { .. } => "verification statement: call assign",
                CStatement::Call { .. } => "verification statement: call",
                CStatement::HeapAllocate { .. } => "verification statement: heap allocate",
                CStatement::HeapFree { .. } => "verification statement: heap free",
                CStatement::Assert { .. } => "verification statement: assert",
                CStatement::Return(_) => "verification statement: return",
                CStatement::Store { .. } => "verification statement: store",
                CStatement::TypedStore { .. } => "verification statement: typed store",
                CStatement::Update { .. } => "verification statement: update",
                CStatement::While { .. } => "verification statement: while",
                CStatement::Switch { .. } => "verification statement: switch",
                CStatement::Seq(_, _) | CStatement::If { .. } => unreachable!(),
            };
            let paths = crate::instrumentation::measure_operation(
                "kernel",
                "independent kernel execution",
                operation,
                || {
                    execute_c_statement_paths(
                        state,
                        statement,
                        assumptions,
                        environment,
                        execution_semantics,
                        budget,
                    )
                },
            );
            variables.next = variables.next.max(budget.next_kernel_variable);
            paths?
        }
    };
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_statement_verification_paths_with_prefix(
    state: &CState,
    statement: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    prefix_facts: &[ExecutionPureFact],
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let effective_assumptions =
        assumptions_with_path_context(assumptions, prefix_facts, prefix_obligations);
    let paths = execute_c_statement_verification_paths(
        state,
        statement,
        &effective_assumptions,
        environment,
        execution_semantics,
        budget,
        variables,
    )?
    .into_iter()
    .filter_map(|path| {
        let (facts, obligations) = merge_execution_pure_facts_and_obligations(
            prefix_facts,
            prefix_obligations,
            &path.facts,
            &path.obligations,
            assumptions,
        )?;
        Some(CStatementExecutionPath {
            outcome: path.outcome,
            facts,
            obligations,
        })
    })
    .collect::<Vec<_>>();
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_while_verification_paths(
    state: &CState,
    condition: &CExpression,
    invariant: &[Proposition],
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    resource_specs: &[CResourceSpec],
    ranking_measures: &[CExpression],
    structural_measure: Option<&str>,
    body: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
    do_while: bool,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    execute_c_while_exit_paths(
        state,
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        resource_specs,
        ranking_measures,
        structural_measure,
        body,
        assumptions,
        environment,
        Some(environment),
        &[],
        execution_semantics,
        false,
        do_while,
        budget,
        variables,
    )
}

/// Checks the state components that a loop back edge cannot silently reset.
/// Scalar locals and ordinary memory cells are handled by the existing loop
/// abstraction and effect checks; heap lifetime, resource ownership, and
/// counted resource populations are separate semantic state and must either
/// be unchanged at the loop-state join.
pub(crate) fn c_loop_state_components_match_at_back_edge(
    top_state: &CState,
    next_state: &CState,
    assumptions: &PureFactContext,
    composite_resource_definitions: &[CCompositeResourceDefinition],
) -> Result<(), String> {
    c_loop_state_components_match_at_back_edge_inner(
        top_state,
        next_state,
        composite_resource_definitions,
        assumptions,
    )
}

/// Whether a post-body loop condition still has a feasible true path.
///
/// This is deliberately conservative for non-value condition outcomes: an
/// unresolved condition is treated as potentially continuing, so callers do
/// not export a state-changing body path as a final exit accidentally.
pub(crate) fn c_loop_condition_may_continue(
    state: &CState,
    condition: &CExpression,
    assumptions: &PureFactContext,
) -> Result<bool, String> {
    c_loop_condition_feasibility(state, condition, assumptions)
        .map(|(may_continue, _)| may_continue)
        .map_err(|limit| format!("could not classify the loop condition: {limit:?}"))
}

fn c_loop_condition_feasibility(
    state: &CState,
    condition: &CExpression,
    assumptions: &PureFactContext,
) -> ExecutionResult<(bool, bool)> {
    let mut budget = ExecutionBudget::for_c_expression(condition);
    let expression_paths = evaluate_c_expression_paths(state, condition, assumptions, &mut budget)?;
    let mut may_continue = false;
    let mut may_exit = false;
    for path in expression_paths {
        match path.outcome {
            CExpressionOutcome::Value(value) => {
                if condition_path_is_ruled_out(&path.facts, assumptions) {
                    continue;
                }
                for path in c_truthiness_paths(value, path.facts, path.obligations, assumptions) {
                    if path.is_true {
                        may_continue = true;
                    } else {
                        may_exit = true;
                    }
                }
            }
            CExpressionOutcome::UndefinedBehavior(_) | CExpressionOutcome::RuntimeError(_) => {
                may_continue = true;
                may_exit = true;
            }
        }
    }
    Ok((may_continue, may_exit))
}

fn condition_path_is_ruled_out(facts: &[ExecutionPureFact], assumptions: &PureFactContext) -> bool {
    facts.iter().any(|fact| {
        let Proposition::ConditionIs(condition, value) = fact.proposition() else {
            return false;
        };
        condition_value_is_proven(assumptions, condition, !value)
    })
}

/// Decide one bare condition through the exact fact index, the intrinsic
/// rule, and the frozen condition checker. This is deliberately not the
/// general proposition prover: a kernel route that prunes an execution path
/// or a mutable-footprint check must be a theory decision over the named
/// condition, not a logical proof search over unrelated ambient facts.
pub(super) fn condition_is_decided(
    assumptions: &PureFactContext,
    condition: &ConditionTerm,
) -> Option<bool> {
    assumptions
        .exact_condition_value(condition)
        .or_else(|| PureFactContext::decide_intrinsically(condition))
        .or_else(|| {
            (!assumptions.should_defer_non_exact_condition_reasoning())
                .then(|| assumptions.decide(condition))
                .flatten()
        })
}

fn condition_is_decided_true(assumptions: &PureFactContext, condition: &ConditionTerm) -> bool {
    condition_is_decided(assumptions, condition) == Some(true)
}

fn condition_value_is_proven(
    assumptions: &PureFactContext,
    condition: &ConditionTerm,
    value: bool,
) -> bool {
    condition_is_decided(assumptions, condition) == Some(value)
        || (!value
            && condition_complement(condition)
                .is_some_and(|complement| condition_is_decided_true(assumptions, &complement)))
}

fn condition_complement(condition: &ConditionTerm) -> Option<ConditionTerm> {
    match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => Some(
            ConditionTerm::signed_greater_equal(left.as_ref().clone(), right.as_ref().clone()),
        ),
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => Some(
            ConditionTerm::signed_greater_than(left.as_ref().clone(), right.as_ref().clone()),
        ),
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => Some(
            ConditionTerm::signed_less_equal(left.as_ref().clone(), right.as_ref().clone()),
        ),
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => Some(
            ConditionTerm::signed_less_than(left.as_ref().clone(), right.as_ref().clone()),
        ),
        _ => None,
    }
}

fn c_loop_state_components_match_at_back_edge_inner(
    top_state: &CState,
    next_state: &CState,
    composite_resource_definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let mut changed = Vec::new();
    if top_state.memory().heap != next_state.memory().heap {
        changed.push("heap allocation lifetime");
    }
    if !crate::kernel::api::contract_certification::resource_contexts_definitionally_equal_with_definitions(
        composite_resource_definitions,
        top_state.memory(),
        top_state.resources(),
        next_state.memory(),
        next_state.resources(),
        assumptions,
    ) {
        changed.push("resource ownership");
    }
    if !crate::kernel::api::counted_populations_definitionally_equal(
        top_state,
        next_state,
        composite_resource_definitions,
        assumptions,
    ) {
        changed.push("counted resource populations");
    }
    if changed.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "loop state join changes {}; the body path does not reach the loop-head state",
            changed.join(", ")
        ))
    }
}

pub(super) fn execute_c_while_exit_paths_with_proven_phases(
    state: &CState,
    condition: &CExpression,
    invariant: &[Proposition],
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    resource_specs: &[CResourceSpec],
    ranking_measures: &[CExpression],
    structural_measure: Option<&str>,
    body: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    initialization_proven: bool,
    preservation_proven: bool,
    final_exit_candidates: &[CLoopFinalExitCandidate],
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
    do_while: bool,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    execute_c_while_exit_paths(
        state,
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        resource_specs,
        ranking_measures,
        structural_measure,
        body,
        assumptions,
        environment,
        (!preservation_proven).then_some(environment),
        final_exit_candidates,
        execution_semantics,
        initialization_proven,
        do_while,
        budget,
        variables,
    )
}

#[allow(clippy::too_many_arguments)]
fn execute_c_while_exit_paths(
    state: &CState,
    condition: &CExpression,
    invariant: &[Proposition],
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    resource_specs: &[CResourceSpec],
    ranking_measures: &[CExpression],
    structural_measure: Option<&str>,
    body: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    preservation_environment: Option<&CExecutionEnvironment>,
    final_exit_candidates: &[CLoopFinalExitCandidate],
    execution_semantics: CExecutionSemantics,
    initialization_proven: bool,
    do_while: bool,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let mut base_obligations = Vec::new();
    for proposition in invariant {
        if add_proof_obligation(&mut base_obligations, assumptions, proposition.clone()).is_none() {
            return Ok(Vec::new());
        }
    }

    let composite_resource_definitions = environment_composite_resource_definitions(environment);
    let head = prepare_loop_top_state(
        state,
        effect_checks,
        invariant_checks,
        resource_specs,
        &composite_resource_definitions,
        body,
        assumptions,
        budget,
        variables,
    )?;
    // Entry invariants are checked at the real loop entry, with the loop's
    // binders already bound to the instances they name there. `old(...)` keeps
    // reading the state as the enclosing proof wrote it, under the identities
    // that proof used.
    let entry_obligations = if initialization_proven {
        Vec::new()
    } else {
        collect_invariant_check_obligations(
            &head.entry,
            state,
            invariant_checks,
            InvariantPhase::Entry,
            assumptions,
            budget,
        )?
    };
    let top_state = head.top.clone();
    // The guard and the invariants are read with the selected arm's cells
    // published (D7); the loop's exit outcome stays `top_state`, so that read
    // authority never leaves the head.
    let guard_state = head.guard.clone();
    let whole_loop_effect_summaries = head.summaries.clone();
    let (preservation_obligations, mut final_exit_paths) =
        if let Some(environment) = preservation_environment {
            let summary = collect_loop_preservation_summary(
                state,
                &head,
                condition,
                invariant_checks,
                effect_checks,
                resource_specs,
                ranking_measures,
                structural_measure,
                &composite_resource_definitions,
                &whole_loop_effect_summaries,
                body,
                assumptions,
                environment,
                execution_semantics,
                do_while,
                budget,
                variables,
            )?;
            (summary.obligations, summary.final_exit_paths)
        } else {
            (Vec::new(), Vec::new())
        };
    let mut loop_check_obligations = Vec::new();
    // A loop may only declare resources the enclosing context actually holds.
    for failure in &head.resource_failures {
        loop_check_obligations.push(
            ProofObligation::verification_condition(false_equals_true_proposition())
                .with_context(failure.clone()),
        );
    }
    append_required_proof_obligations(&mut loop_check_obligations, assumptions, &entry_obligations);
    append_required_proof_obligations(
        &mut loop_check_obligations,
        assumptions,
        &preservation_obligations,
    );
    for path in &mut final_exit_paths {
        append_required_proof_obligations(
            &mut path.obligations,
            assumptions,
            &loop_check_obligations,
        );
    }
    let whole_loop_effect_facts = whole_loop_effect_summaries
        .iter()
        .cloned()
        .map(ExecutionPureFact::new)
        .collect::<Vec<_>>();

    let (initial_may_continue, initial_may_exit) = if do_while {
        (!final_exit_candidates.is_empty(), false)
    } else if final_exit_candidates.is_empty() {
        (true, true)
    } else {
        c_loop_condition_feasibility(state, condition, assumptions)?
    };
    let mut paths = Vec::new();
    paths.append(&mut final_exit_paths);
    if initial_may_continue {
        for candidate in final_exit_candidates {
            let candidate_assumptions =
                assumptions_with_propositions(assumptions, candidate.pure_facts());
            for assumption in assume_condition_truthiness(
                candidate.state(),
                condition,
                &candidate_assumptions,
                &[],
                &[],
                false,
                budget,
            )? {
                let candidate_facts = candidate
                    .pure_facts()
                    .iter()
                    .cloned()
                    .map(ExecutionPureFact::certified)
                    .collect::<Vec<_>>();
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &candidate_facts,
                    &[],
                    &assumption.facts,
                    &assumption.obligations,
                    assumptions,
                ) else {
                    continue;
                };
                // A guard that did not evaluate here decides nothing: this is
                // not an exit, it is a refusal that carries the guard's own
                // outcome.
                if let Some(outcome) = assumption.undecided_outcome() {
                    paths.push(CStatementExecutionPath {
                        outcome: outcome.clone(),
                        facts,
                        obligations,
                    });
                    continue;
                }
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::Normal(head.restored_exit_state(candidate.state())),
                    facts,
                    obligations,
                });
            }
        }
    }
    let invariant_contexts = assume_invariant_checks(
        &guard_state,
        state,
        invariant_checks,
        assumptions,
        &whole_loop_effect_facts,
        &base_obligations,
        budget,
    )?;
    let mut has_live_iteration = false;
    for (invariant_facts, invariant_obligations) in &invariant_contexts {
        if do_while
            || !assume_condition_truthiness(
                &guard_state,
                condition,
                assumptions,
                invariant_facts,
                invariant_obligations,
                true,
                budget,
            )?
            .is_empty()
        {
            has_live_iteration = true;
            break;
        }
    }
    if initial_may_exit {
        for (invariant_facts, invariant_obligations) in invariant_contexts {
            let condition_contexts = assume_condition_truthiness(
                &guard_state,
                condition,
                assumptions,
                &invariant_facts,
                &invariant_obligations,
                false,
                budget,
            )?;
            for assumption in condition_contexts {
                let CConditionAssumption {
                    branch,
                    mut facts,
                    mut obligations,
                } = assumption;
                append_required_proof_obligations(
                    &mut obligations,
                    assumptions,
                    &loop_check_obligations,
                );
                // An operand the function has no authority to read leaves the
                // guard undecided. This is not the exit: assuming the
                // negation of the operands that did evaluate would assume
                // strictly less than `!condition`, and the loop would export
                // an exit state the C never reaches that way.
                if let CConditionBranch::Undecided(outcome) = branch {
                    paths.push(CStatementExecutionPath {
                        outcome,
                        facts,
                        obligations,
                    });
                    continue;
                }
                // D7 applied to refutation at the loop exit, the same way the
                // head and the back edge apply it. The invariants and the
                // failed loop condition are the exit's premises, and a
                // premise that contradicts a field-free arm's own fact says
                // the binder's model is not that constructor: an ascending
                // walk learns `ctx.model != Context::Left(..)` from the
                // failed guard `parent != 0` against that arm's
                // `fact parent != 0`, which is what lets the proof after the
                // loop close those arms by contradiction instead of
                // unfolding a frame whose cells the arm does not describe.
                let exit_assumptions = assumptions_with_path_context(assumptions, &facts, &[]);
                for fact in crate::kernel::refuted_instance_arm_model_facts(
                    top_state.resources(),
                    &composite_resource_definitions,
                    &top_state,
                    &exit_assumptions,
                ) {
                    facts.push(ExecutionPureFact::new(fact));
                }
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::Normal(top_state.clone()),
                    facts,
                    obligations,
                });
            }
        }
    }
    if paths.is_empty() {
        let mut obligations = base_obligations;
        append_required_proof_obligations(&mut obligations, assumptions, &loop_check_obligations);
        if !has_live_iteration {
            obligations.push(
                ProofObligation::verification_condition(false_equals_true_proposition())
                    .with_context("loop has neither a safe exit nor a safe iteration"),
            );
        }
        paths.push(CStatementExecutionPath {
            outcome: CStatementOutcome::VerificationDiverges,
            facts: whole_loop_effect_facts,
            obligations,
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum InvariantPhase {
    Entry,
    Preservation,
}

pub(super) fn invariant_context(
    check: &CLoopInvariantCheck,
    phase: InvariantPhase,
) -> Option<&str> {
    match phase {
        InvariantPhase::Entry => check.entry_context(),
        InvariantPhase::Preservation => check.preservation_context(),
    }
}

pub(super) fn collect_invariant_check_obligations(
    state: &CState,
    loop_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    phase: InvariantPhase,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ProofObligation>> {
    collect_invariant_check_obligations_with_mode(
        state,
        loop_entry_state,
        invariant_checks,
        phase,
        assumptions,
        budget,
        false,
    )
}

pub(super) fn collect_invariant_check_obligations_without_search(
    state: &CState,
    loop_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    phase: InvariantPhase,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ProofObligation>> {
    collect_invariant_check_obligations_with_mode(
        state,
        loop_entry_state,
        invariant_checks,
        phase,
        assumptions,
        budget,
        true,
    )
}

#[allow(clippy::too_many_arguments)]
fn collect_invariant_check_obligations_with_mode(
    state: &CState,
    loop_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    phase: InvariantPhase,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    without_search: bool,
) -> ExecutionResult<Vec<ProofObligation>> {
    let mut contexts = vec![(Vec::new(), Vec::new())];
    let mut all_obligations = Vec::new();
    for check in invariant_checks {
        let mut next_contexts = Vec::new();
        for (facts, obligations) in contexts {
            let effective_assumptions = if without_search {
                assumptions_with_path_context(assumptions, &facts, &obligations)
                    .defer_non_exact_condition_reasoning()
                    .defer_non_exact_loadability_obligations()
            } else {
                assumptions_with_path_context(assumptions, &facts, &obligations)
            };
            for path in lower_spec_proposition_at_state_with_loop_entry(
                state,
                check.proposition(),
                Some(loop_entry_state),
                &effective_assumptions,
                budget,
            )? {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &facts,
                    &obligations,
                    &path.facts,
                    &path.obligations,
                    if without_search {
                        &effective_assumptions
                    } else {
                        assumptions
                    },
                ) else {
                    continue;
                };
                let mut obligations = obligations;
                let obligation_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                // The guards this wrap inserts, then the head chain the
                // invariant's own lowering recorded: one record for the
                // obligation proposition, produced by the same wrap that
                // built it, so a consumer introducing its head never pairs
                // a hidden guard with a written connective.
                let (proposition, guards) =
                    wrap_path_context_with_introductions(path.proposition, &facts, &obligations);
                let mut introductions = guards;
                introductions.extend(path.introductions.iter().cloned());
                let introductions = std::sync::Arc::new(introductions);
                if without_search {
                    add_required_proof_obligation_without_search(
                        &mut obligations,
                        &obligation_assumptions,
                        proposition,
                        invariant_context(check, phase),
                        Some(&introductions),
                    );
                    append_required_proof_obligations_without_search(
                        &mut all_obligations,
                        assumptions,
                        &obligations,
                    );
                } else {
                    add_required_proof_obligation_with_context(
                        &mut obligations,
                        &obligation_assumptions,
                        proposition,
                        invariant_context(check, phase),
                        Some(&introductions),
                    );
                    append_required_proof_obligations(
                        &mut all_obligations,
                        assumptions,
                        &obligations,
                    );
                }
                next_contexts.push((facts, obligations));
            }
        }
        contexts = next_contexts;
    }
    Ok(all_obligations)
}

/// The back-edge ranking members of a ranked loop's invariant bundle.
///
/// Membership order is fixed so a retained certificate is stable across runs
/// and sites: one `0 <= component` obligation per declared component at the
/// back edge, in declaration order, then exactly one decrease obligation.
/// The decrease obligation is `post < pre` for a single component; for a
/// tuple it is the right-nested disjunction over pivots
/// `(post0 < pre0) or ((post0 == pre0) and (post1 < pre1)) or ...`, so the
/// pivot is an ordinary arm choice a proof makes with `left` and `right` and
/// expansion prints, rather than a kernel search over pivot indices.
///
/// `pre` reads each component at the iteration entry and `post` at the back
/// edge. Work is linear in the declared measure; no ambient fact is scanned.
pub(super) fn collect_loop_ranking_obligations(
    state: &CState,
    iteration_entry_state: &CState,
    ranking_measures: &[CExpression],
) -> Result<Vec<ProofObligation>, String> {
    if ranking_measures.is_empty() {
        return Ok(Vec::new());
    }
    let mut pre = Vec::with_capacity(ranking_measures.len());
    let mut post = Vec::with_capacity(ranking_measures.len());
    for measure in ranking_measures {
        pre.push(crate::kernel::termination::c_ranking_measure_term(
            measure,
            iteration_entry_state,
        )?);
        post.push(crate::kernel::termination::c_ranking_measure_term(
            measure, state,
        )?);
    }
    let mut obligations = Vec::with_capacity(ranking_measures.len() + 1);
    for (measure, post) in ranking_measures.iter().zip(post.iter()) {
        obligations.push(
            ProofObligation::verification_condition(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), post.clone()),
                true,
            ))
            // A ranking member is one condition read from the declared
            // measure: no lowering wrapped it, so its recorded chain is
            // empty. Recording that keeps the bundle's member records
            // aligned with its members.
            .with_introductions(LoweringIntroductions::new())
            .with_context(format!(
                "loop ranking component `{}` is nonnegative at the back edge",
                crate::kernel::termination::c_ranking_measure_display(measure)
            )),
        );
    }
    let arm = |pivot: usize| {
        let strict = Proposition::ConditionIs(
            ConditionTerm::signed_less_than(post[pivot].clone(), pre[pivot].clone()),
            true,
        );
        (0..pivot).rev().fold(strict, |rest, index| {
            Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::equal(post[index].clone(), pre[index].clone()),
                    true,
                )),
                Box::new(rest),
            )
        })
    };
    let decrease = (0..ranking_measures.len())
        .rev()
        .fold(None, |rest: Option<Proposition>, pivot| match rest {
            None => Some(arm(pivot)),
            Some(rest) => Some(Proposition::Or(Box::new(arm(pivot)), Box::new(rest))),
        })
        .expect("a ranked loop declares at least one component");
    obligations.push(
        ProofObligation::verification_condition(decrease)
            .with_introductions(LoweringIntroductions::new())
            .with_context(format!(
                "loop ranking measure `{}` decreases at the back edge",
                crate::kernel::termination::c_ranking_measures_display(ranking_measures)
            )),
    );
    Ok(obligations)
}

/// The ranking members, or one refusal obligation naming why the declared
/// measure has no value at this state. A measure that does not read as a
/// scalar int32 expression is a proof failure at the loop, never a silently
/// dropped ranking obligation.
pub(super) fn loop_ranking_obligations_or_refusal(
    state: &CState,
    iteration_entry_state: &CState,
    ranking_measures: &[CExpression],
) -> Vec<ProofObligation> {
    match collect_loop_ranking_obligations(state, iteration_entry_state, ranking_measures) {
        Ok(obligations) => obligations,
        Err(message) => vec![
            ProofObligation::verification_condition(false_equals_true_proposition())
                .with_context(message),
        ],
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct LoopPreservationSummary {
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) final_exit_paths: Vec<CStatementExecutionPath>,
}

pub(super) fn collect_loop_preservation_summary(
    loop_entry_state: &CState,
    head: &CLoopHead,
    condition: &CExpression,
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    resource_specs: &[CResourceSpec],
    ranking_measures: &[CExpression],
    structural_measure: Option<&str>,
    composite_resource_definitions: &[CCompositeResourceDefinition],
    whole_loop_effect_summaries: &[Proposition],
    body: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    do_while: bool,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<LoopPreservationSummary> {
    let mut obligations = Vec::new();
    let mut final_exit_paths = Vec::new();
    // The body executes from the loop's own resource context; everything the
    // enclosing frame withheld is returned on the way out.
    let top_state = &head.body;
    let binders = c_loop_binders(resource_specs);
    let whole_loop_effect_facts = whole_loop_effect_summaries
        .iter()
        .cloned()
        .map(ExecutionPureFact::new)
        .collect::<Vec<_>>();
    for (invariant_facts, invariant_obligations) in assume_invariant_checks(
        top_state,
        loop_entry_state,
        invariant_checks,
        assumptions,
        &whole_loop_effect_facts,
        &[],
        budget,
    )? {
        let condition_contexts = if do_while {
            vec![CConditionAssumption {
                branch: CConditionBranch::Decided(true),
                facts: invariant_facts.clone(),
                obligations: invariant_obligations.clone(),
            }]
        } else {
            assume_condition_truthiness(
                top_state,
                condition,
                assumptions,
                &invariant_facts,
                &invariant_obligations,
                true,
                budget,
            )?
        };
        for assumption in condition_contexts {
            // The body cannot run from a guard that produced no value: this
            // iteration is not entered, it is unproven. Refuse it here rather
            // than letting the iteration disappear from the rule.
            if let Some(outcome) = assumption.undecided_outcome() {
                obligations.push(
                    ProofObligation::verification_condition(false_equals_true_proposition())
                        .with_context(undecided_loop_guard_context(outcome)),
                );
                continue;
            }
            let CConditionAssumption {
                facts: condition_facts,
                obligations: condition_obligations,
                ..
            } = assumption;
            for body_path in execute_c_statement_verification_paths_with_prefix(
                top_state,
                body,
                assumptions,
                environment,
                execution_semantics,
                &condition_facts,
                &condition_obligations,
                budget,
                variables,
            )? {
                match body_path.outcome {
                    CStatementOutcome::Normal(next_state)
                    | CStatementOutcome::Continue(next_state) => {
                        // The back edge binds the loop's names again exactly as
                        // the head did. A body that refolded its instance under
                        // another name still hands the binder back, and a body
                        // that ends with no instance at those arguments fails
                        // here, named.
                        let back_edge_assumptions = assumptions_with_path_context(
                            assumptions,
                            &body_path.facts,
                            &body_path.obligations,
                        );
                        let (next_state, binder_failure) =
                            match c_loop_state_with_loop_binders_rebound(
                                top_state,
                                &next_state,
                                &binders,
                                &back_edge_assumptions,
                            ) {
                                Ok(rebound) => (rebound, None),
                                Err(failure) => (next_state, Some(failure)),
                            };
                        // Both back-edge directions come from one evaluation
                        // of the guard, so a path the guard did not decide is
                        // reported once instead of twice.
                        let condition_contexts = assume_condition_branches(
                            &next_state,
                            condition,
                            assumptions,
                            &body_path.facts,
                            &body_path.obligations,
                            budget,
                        )?;
                        for assumption in condition_contexts {
                            // Neither the back edge nor the exit is taken
                            // when the guard produced no value; the loop
                            // rule cannot certify this edge at all.
                            if let Some(outcome) = assumption.undecided_outcome() {
                                obligations.push(
                                    ProofObligation::verification_condition(
                                        false_equals_true_proposition(),
                                    )
                                    .with_context(undecided_loop_guard_context(outcome)),
                                );
                                continue;
                            }
                            let CConditionAssumption {
                                branch,
                                facts: condition_facts,
                                obligations: condition_obligations,
                            } = assumption;
                            let may_continue = matches!(branch, CConditionBranch::Decided(true));
                            let path_assumptions = assumptions_with_path_context(
                                assumptions,
                                &condition_facts,
                                &condition_obligations,
                            );
                            let effect_obligations = collect_loop_effect_check_obligations(
                                top_state,
                                &next_state,
                                effect_checks,
                                &condition_facts,
                                &condition_obligations,
                                assumptions,
                                budget,
                            )?;
                            let mut path_obligations = if do_while && !may_continue {
                                Vec::new()
                            } else {
                                collect_invariant_check_obligations(
                                    &next_state,
                                    loop_entry_state,
                                    invariant_checks,
                                    InvariantPhase::Preservation,
                                    &path_assumptions,
                                    budget,
                                )?
                            };
                            // A ranked loop's back edge carries the same
                            // ranking members the surface bundle spells.
                            // Only a continuing edge is a back edge.
                            if may_continue {
                                path_obligations.extend(loop_ranking_obligations_or_refusal(
                                    &next_state,
                                    top_state,
                                    ranking_measures,
                                ));
                                // A structural measure is not a ranking
                                // member: the kernel decides the descent
                                // here and reports a refusal obligation
                                // naming the binder when it does not hold.
                                if let Some(measure) = structural_measure
                                    && let Some(failure) = loop_structural_descent_failure(
                                        top_state,
                                        &next_state,
                                        &binders,
                                        measure,
                                        composite_resource_definitions,
                                        &path_assumptions,
                                    )
                                {
                                    path_obligations.push(
                                        ProofObligation::verification_condition(
                                            false_equals_true_proposition(),
                                        )
                                        .with_context(failure),
                                    );
                                }
                            }
                            let mut state_obligations = condition_obligations.clone();
                            // A binder the body did not hand back is the
                            // whole verdict for this edge; the ownership
                            // join would only repeat it less precisely.
                            let join_failure = if !may_continue {
                                None
                            } else if let Some(failure) = &binder_failure {
                                Some(failure.clone())
                            } else {
                                c_loop_state_components_match_at_back_edge_inner(
                                    top_state,
                                    &c_loop_state_with_head_binder_models(
                                        &next_state,
                                        top_state,
                                        &binders,
                                    ),
                                    composite_resource_definitions,
                                    &path_assumptions,
                                )
                                .err()
                            };
                            if let Some(message) = join_failure {
                                state_obligations.push(
                                    ProofObligation::verification_condition(
                                        false_equals_true_proposition(),
                                    )
                                    .with_context(message),
                                );
                            }
                            append_required_proof_obligations(
                                &mut obligations,
                                assumptions,
                                &state_obligations,
                            );
                            append_required_proof_obligations_under_path_context(
                                &mut obligations,
                                assumptions,
                                &effect_obligations,
                                &condition_facts,
                                &condition_obligations,
                            );
                            append_required_proof_obligations_under_path_context(
                                &mut obligations,
                                assumptions,
                                &path_obligations,
                                &condition_facts,
                                &condition_obligations,
                            );
                            if !may_continue {
                                let final_path_facts = condition_facts.clone();
                                let final_path_obligations = condition_obligations.clone();
                                let mut final_obligations = condition_obligations;
                                append_required_proof_obligations_under_path_context(
                                    &mut final_obligations,
                                    assumptions,
                                    &effect_obligations,
                                    &final_path_facts,
                                    &final_path_obligations,
                                );
                                append_required_proof_obligations_under_path_context(
                                    &mut final_obligations,
                                    assumptions,
                                    &path_obligations,
                                    &final_path_facts,
                                    &final_path_obligations,
                                );
                                final_exit_paths.push(CStatementExecutionPath {
                                    outcome: CStatementOutcome::Normal(
                                        head.restored_exit_state(&next_state),
                                    ),
                                    facts: final_path_facts,
                                    obligations: final_obligations,
                                });
                            }
                        }
                    }
                    CStatementOutcome::Break(next_state) => {
                        let path_assumptions = assumptions_with_path_context(
                            assumptions,
                            &body_path.facts,
                            &body_path.obligations,
                        );
                        let effect_obligations = collect_loop_effect_check_obligations(
                            top_state,
                            &next_state,
                            effect_checks,
                            &body_path.facts,
                            &body_path.obligations,
                            assumptions,
                            budget,
                        )?;
                        let path_obligations = collect_invariant_check_obligations(
                            &next_state,
                            loop_entry_state,
                            invariant_checks,
                            InvariantPhase::Preservation,
                            &path_assumptions,
                            budget,
                        )?;
                        let final_path_facts = body_path.facts;
                        let final_path_obligations = body_path.obligations;
                        let mut final_obligations = final_path_obligations.clone();
                        append_required_proof_obligations_under_path_context(
                            &mut final_obligations,
                            assumptions,
                            &effect_obligations,
                            &final_path_facts,
                            &final_path_obligations,
                        );
                        append_required_proof_obligations_under_path_context(
                            &mut final_obligations,
                            assumptions,
                            &path_obligations,
                            &final_path_facts,
                            &final_path_obligations,
                        );
                        final_exit_paths.push(CStatementExecutionPath {
                            outcome: CStatementOutcome::Normal(
                                head.restored_exit_state(&next_state),
                            ),
                            facts: final_path_facts,
                            obligations: final_obligations,
                        });
                    }
                    CStatementOutcome::Return { .. }
                    | CStatementOutcome::VerificationDiverges
                    | CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_) => {
                        let mut path_obligations = body_path.obligations;
                        path_obligations.push(
                            ProofObligation::verification_condition(false_equals_true_proposition())
                                .with_context("loop preservation body safety"),
                        );
                        append_required_proof_obligations(
                            &mut obligations,
                            assumptions,
                            &path_obligations,
                        );
                    }
                }
            }
        }
    }
    Ok(LoopPreservationSummary {
        obligations,
        final_exit_paths,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct EvaluatedMemorySegment {
    pub(super) base: Pointer,
    pub(super) start: Bitvector32Term,
    pub(super) end: Bitvector32Term,
    pub(super) element_width: u32,
}

fn evaluate_whole_loop_effect_ranges(
    before_state: &CState,
    effect_checks: &[CLoopEffectCheck],
    include_mutable_summaries: bool,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<(Vec<Vec<CMemoryRange>>, bool)> {
    let mut ranges_by_summary = Vec::new();
    let mut all_ranges_evaluable = true;
    for check in effect_checks {
        if check.span() != CLoopEffectSpan::Whole {
            continue;
        }

        let ranges = match check.effect() {
            CLoopEffect::Immutable => Vec::new(),
            // A mutable clause is an upper bound. Without a memory-writing
            // body, it is not evidence of mutation and should not block an
            // enclosing immutable claim.
            CLoopEffect::Mutable(_) if !include_mutable_summaries => continue,
            CLoopEffect::Mutable(segments) => {
                if let Some(validated) = check.validated_ranges() {
                    ranges_by_summary.push(validated.to_vec());
                    continue;
                }
                if check.origin() == CLoopEffectOrigin::InheritedResourceDerived {
                    // The source-oriented segments are diagnostic metadata;
                    // an inherited resource frame is authoritative only after
                    // entry transition setup has installed fixed ranges.
                    all_ranges_evaluable = false;
                    continue;
                }
                let mut ranges = Vec::new();
                let mut failed = false;
                for segment in segments {
                    let element_width = segment.element_width;
                    match evaluate_loop_effect_segment(before_state, segment, assumptions, budget)?
                    {
                        Ok(segment) => ranges.push(CMemoryRange::new_with_element_width(
                            segment.base,
                            segment.start,
                            segment.end,
                            element_width,
                        )),
                        Err(_) => {
                            failed = true;
                            break;
                        }
                    }
                }
                if failed {
                    all_ranges_evaluable = false;
                    continue;
                }
                ranges
            }
        };
        ranges_by_summary.push(ranges);
    }
    Ok((ranges_by_summary, all_ranges_evaluable))
}

pub(super) fn collect_whole_loop_effect_summaries(
    before_state: &CState,
    after_state: &CState,
    ranges_by_summary: &[Vec<CMemoryRange>],
) -> Vec<Proposition> {
    ranges_by_summary
        .iter()
        .map(|ranges| Proposition::CMemoryEffectSummary {
            before: before_state.memory().clone(),
            after: after_state.memory().clone(),
            mutable_ranges: ranges.clone(),
        })
        .collect()
}

/// The abstract head of one loop.
///
/// `top` is the state the enclosing frame continues from; `body` is the state
/// the body executes from. They differ only in the resource context, and only
/// when the loop declares resources of its own: the body then owns exactly
/// what the loop declared, and the rest of the enclosing frame's resources are
/// withheld until the loop exits.
pub(super) struct CLoopHead {
    pub(super) top: CState,
    pub(super) body: CState,
    /// The head state the loop reads its guard and invariants from: `top`
    /// with the cells of each folded matched instance's selected arm
    /// published as views (D7). Ownership is untouched, and the loop's exit
    /// outcome is `top`, so the extra read authority never leaves the head.
    pub(super) guard: CState,
    /// The loop's entry state with each binder bound to the instance it
    /// names. Entry invariant checks read binder fields from here, so a loop
    /// binder that renames an enclosing instance is available at entry too.
    pub(super) entry: CState,
    pub(super) summaries: Vec<Proposition>,
    /// Why a declared loop resource could not be taken from the enclosing
    /// resource context. A non-empty list is a verification failure.
    pub(super) resource_failures: Vec<String>,
}

impl CLoopHead {
    /// Whether the body executes with a narrower resource context than the
    /// enclosing frame holds.
    pub(super) fn narrows_resources(&self) -> bool {
        self.body.resources() != self.top.resources()
    }

    /// The enclosing frame's resource context, restored onto a state the body
    /// left with the loop's declared resources intact. A body that changed
    /// that context keeps its own: the withheld resources are returned only
    /// against an unchanged loop-level exchange.
    pub(super) fn restored_exit_state(&self, state: &CState) -> CState {
        if !self.narrows_resources() || state.resources() != self.body.resources() {
            return state.clone();
        }
        state
            .clone()
            .with_resource_context(self.top.resources().clone())
    }
}

/// Every composite resource definition this environment's functions declare,
/// in first-seen order and without repeats.
pub(super) fn environment_composite_resource_definitions(
    environment: &CExecutionEnvironment,
) -> Vec<CCompositeResourceDefinition> {
    environment
        .functions
        .values()
        .flat_map(|function| function.composite_resource_definitions().iter().cloned())
        .fold(Vec::new(), |mut definitions, definition| {
            if !definitions.contains(&definition) {
                definitions.push(definition);
            }
            definitions
        })
}

pub(super) fn prepare_loop_top_state(
    entry_state: &CState,
    effect_checks: &[CLoopEffectCheck],
    invariant_checks: &[CLoopInvariantCheck],
    resource_specs: &[CResourceSpec],
    definitions: &[CCompositeResourceDefinition],
    body: &CStatement,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<CLoopHead> {
    let include_mutable_summaries = statement_may_write_memory(entry_state, body);
    let (effect_ranges, all_ranges_evaluable) = evaluate_whole_loop_effect_ranges(
        entry_state,
        effect_checks,
        include_mutable_summaries,
        assumptions,
        budget,
    )?;
    // A verified footprint is an edge fact, not merely a copy-back hint. If
    // any whole mutable segment could not be evaluated, keep the old barrier
    // semantics for the entire loop; the failed effect check still produces
    // its own false proof obligation. Preserve Some(empty) for a checked
    // immutable/no-write summary, distinct from no footprint at all.
    let loop_havoc_ranges = (all_ranges_evaluable && !effect_ranges.is_empty())
        .then(|| effect_ranges.iter().flatten().cloned().collect::<Vec<_>>());
    let mut top_state =
        havoc_loop_modified_locals(entry_state, body, variables, loop_havoc_ranges.as_deref());
    let mut summaries =
        collect_whole_loop_effect_summaries(entry_state, &top_state, &effect_ranges);

    // Whole-loop effects are part of the induction hypothesis at the abstract
    // head and are checked independently at every back edge.
    let mut framed_memory = top_state.memory().clone();
    if !summaries.is_empty() {
        std::sync::Arc::make_mut(&mut framed_memory.blocks).extend(
            entry_state
                .memory()
                .blocks
                .iter()
                .map(|(key, value)| (key.clone(), value.clone())),
        );
    }
    for (pointer, value) in entry_state.memory().cells.iter() {
        if pointer.block.starts_with("local:") {
            continue;
        }
        let is_stable = summaries.iter().any(|summary| {
            let Proposition::CMemoryEffectSummary { mutable_ranges, .. } = summary else {
                return false;
            };
            assumptions.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
        });
        if is_stable {
            std::sync::Arc::make_mut(&mut framed_memory.cells)
                .insert(pointer.clone(), value.clone());
        }
    }
    for ((pointer, c_type), value) in entry_state.memory().union_cells.iter() {
        if pointer.block.starts_with("local:") {
            continue;
        }
        let is_stable = summaries.iter().any(|summary| {
            let Proposition::CMemoryEffectSummary { mutable_ranges, .. } = summary else {
                return false;
            };
            assumptions.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
        });
        if is_stable {
            std::sync::Arc::make_mut(&mut framed_memory.union_cells)
                .insert((pointer.clone(), *c_type), value.clone());
        }
    }

    if framed_memory != *top_state.memory() {
        top_state = top_state.with_memory(framed_memory);
        summaries = collect_whole_loop_effect_summaries(entry_state, &top_state, &effect_ranges);
    }
    // A loop binder takes the instance the enclosing context holds and gives
    // it fresh fields: the head is an arbitrary visit, so only the invariants
    // say what model the binder carries there. The enclosing frame continues
    // from that same head, which is why the loop's exit sees the final model.
    let (entry_state, head_state, top_state, mut resource_failures) =
        match rebind_loop_binder_instances(entry_state, resource_specs, assumptions, budget)? {
            Ok(rebound) => {
                // The head is an arbitrary visit, so the binder's arguments
                // are read from the havocked locals rather than from the
                // values the loop was entered with (D5). That is what lets a
                // body that advances its cursor find its binder again.
                let head_carrier = top_state
                    .clone()
                    .with_resource_context(rebound.resources().clone());
                let head_state = havoc_loop_binder_instance_fields(
                    &head_carrier,
                    resource_specs,
                    assumptions,
                    budget,
                )?;
                let top_state = top_state.with_resource_context(head_state.resources().clone());
                (rebound, head_state, top_state, Vec::new())
            }
            Err(failure) => (
                entry_state.clone(),
                entry_state.clone(),
                top_state,
                vec![failure],
            ),
        };
    // The loop's declarations are evaluated where the loop starts, over the
    // head's models: the clause arguments are the ones at loop entry, and the
    // models are the fresh ones an arbitrary visit carries.
    let (body_state, body_failures) =
        loop_body_resource_context(&head_state, &top_state, resource_specs, assumptions, budget)?;
    resource_failures.extend(body_failures);
    // D7 at a loop head: the invariants play the part of a contract's
    // requirements, so a folded matched instance publishes the cells of the
    // arm they select. That is what lets a guard such as `root->left != 0`
    // read through the focused subtree the binder holds.
    let guard_state = with_selected_arm_views(
        &top_state,
        &top_state,
        invariant_checks,
        definitions,
        assumptions,
        budget,
    )?;
    let body_state = with_selected_arm_views(
        &body_state,
        &top_state,
        invariant_checks,
        definitions,
        assumptions,
        budget,
    )?;
    Ok(CLoopHead {
        top: top_state,
        body: body_state,
        guard: guard_state,
        entry: entry_state,
        summaries,
        resource_failures,
    })
}

/// `state` with the cells of every folded matched instance's selected arm
/// published as read authority (D7).
///
/// The premises are this loop's own invariants, assumed at `premise_state`.
/// The decision itself is [`crate::kernel::select_resource_model_arm`], the
/// one arm-selection mechanism; nothing here proves by cases, and ownership
/// is untouched. An instance whose arm the invariants do not select publishes
/// nothing, exactly as a contract clause's would.
///
/// Cost is the selected arms' own clauses plus one lowering of each invariant.
fn with_selected_arm_views(
    state: &CState,
    premise_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<CState> {
    if definitions.is_empty() {
        return Ok(state.clone());
    }
    let contexts = assume_invariant_checks(
        premise_state,
        premise_state,
        invariant_checks,
        assumptions,
        &[],
        &[],
        budget,
    )?;
    // Two invariant readings would be two different premise sets, and a
    // published arm must be the one every reading selects. One reading is the
    // ordinary case; anything else publishes nothing.
    let [(facts, obligations)] = contexts.as_slice() else {
        return Ok(state.clone());
    };
    let head_assumptions = assumptions_with_path_context(assumptions, facts, obligations);
    let views = crate::kernel::functions::selected_instance_arm_views(
        state.resources(),
        definitions,
        state,
        &head_assumptions,
    );
    if views.is_empty() {
        return Ok(state.clone());
    }
    Ok(state
        .clone()
        .with_resource_context(state.resources().clone().unchecked_with_facts(views)))
}

/// Builds the resource context a declaring loop's body executes with.
///
/// The loop takes its declared resources out of the enclosing context, exactly
/// as a call takes a callee's requirements out of its caller's. What remains is
/// viewed rather than owned, so a body store outside the loop's owned memory
/// fails at the store for want of a resource, and the loop's havoc footprint
/// is the memory it owns. A loop that declares views of its own keeps no
/// ambient read authority either.
fn loop_body_resource_context(
    entry_state: &CState,
    top_state: &CState,
    resource_specs: &[CResourceSpec],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<(CState, Vec<String>)> {
    if resource_specs.is_empty() {
        return Ok((top_state.clone(), Vec::new()));
    }
    let declared = match evaluate_function_resource_context(
        entry_state,
        resource_specs,
        // A loop head has no composite-definition environment in scope,
        // so its clauses see each other's declared cells but not the
        // cells inside a folded composite.
        &[],
        assumptions,
        budget,
    )? {
        Ok(declared) => declared,
        Err(error) => {
            return Ok((
                top_state.clone(),
                vec![format!(
                    "loop declares a resource the enclosing function does not hold: {error:?}"
                )],
            ));
        }
    };
    let mut withheld = entry_state.resources().clone();
    for fact in declared.facts() {
        let Some(remaining) = withheld.clone().without_fact(fact, assumptions) else {
            return Ok((
                top_state.clone(),
                vec![format!(
                    "loop declares a resource the enclosing function does not hold: {fact:?}"
                )],
            ));
        };
        withheld = remaining;
    }
    let mut body_resources = declared.clone();
    if !resource_specs.iter().any(resource_spec_is_view) {
        for fact in withheld.facts() {
            let Some(viewed) = viewed_form_of_resource_fact(fact) else {
                continue;
            };
            if body_resources.satisfies_fact(&viewed, assumptions) {
                continue;
            }
            match body_resources
                .clone()
                .try_compose_with_fact(viewed, assumptions)
            {
                Ok(composed) => body_resources = composed,
                // An un-composable remainder is read authority the body
                // simply does not get; it is not a contract failure.
                Err(_) => continue,
            }
        }
    }
    Ok((
        top_state.clone().with_resource_context(body_resources),
        Vec::new(),
    ))
}

/// Whether a declared loop resource asks only to read.
fn resource_spec_is_view(spec: &CResourceSpec) -> bool {
    spec.is_view()
}

/// One `owns name: resource(args);` loop binder: the name the header writes
/// and the instance identity it binds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CLoopBinder {
    identity: Variable,
    name: String,
    /// The declared resource the binder names. The back edge re-evaluates its
    /// arguments in the state the body reached (D5), so a body that advances
    /// its cursor hands the loop the instance at the new arguments.
    spec: Option<CResourceSpec>,
}

/// The binders a loop's `owns name: resource(args);` clauses declare.
pub(crate) fn c_loop_binders(resource_specs: &[CResourceSpec]) -> Vec<CLoopBinder> {
    resource_specs
        .iter()
        .filter_map(|spec| {
            Some(CLoopBinder {
                identity: spec.instance_identity()?,
                name: spec.instance_binder().unwrap_or("<unnamed>").to_string(),
                spec: Some(spec.clone()),
            })
        })
        .collect()
}

/// Binds each `owns name: resource(args);` loop binder to the owned instance
/// it names, whatever identity the surrounding proof gave that instance.
///
/// A loop header names an instance the way a callee contract does, and there
/// is no binder map: the binder takes the unique owned instance of its family
/// whose arguments, evaluated in this state, are provably the declared ones.
/// The same rule runs at the loop head and at the back edge, so a body that
/// refolded its instance under another name still hands the loop binder back.
///
/// The search reads the family's shape bucket of the resource context and
/// checks the arguments of those instances alone, so it costs the instances
/// of one family rather than the surrounding context.
fn rebind_loop_binder_instances(
    state: &CState,
    resource_specs: &[CResourceSpec],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CState, String>> {
    if !resource_specs.iter().any(CResourceSpec::is_instance) {
        return Ok(Ok(state.clone()));
    }
    let mut state = state.clone();
    let mut claimed: BTreeSet<Variable> = BTreeSet::new();
    for spec in resource_specs {
        let Some(identity) = spec.instance_identity() else {
            continue;
        };
        let binder = spec.instance_binder().unwrap_or("<unnamed>").to_string();
        let Some(inner) = spec.instance_resource_spec() else {
            continue;
        };
        let (name, arguments) =
            match evaluate_function_resource_spec(&state, &inner, assumptions, budget)? {
                Ok(CResourceFact::Own(CResource::Composite { name, arguments }, quantity))
                    if quantity.as_const() == Some(1) =>
                {
                    (name, arguments)
                }
                Ok(_) => {
                    return Ok(Err(format!(
                        "loop binder `{binder}` requires one owned resource definition"
                    )));
                }
                Err(error) => {
                    return Ok(Err(format!(
                        "loop binder `{binder}` could not be evaluated here: {error:?}"
                    )));
                }
            };
        state = match rebind_one_loop_binder_instance(
            &state,
            identity,
            &binder,
            &name,
            &arguments,
            &mut claimed,
            assumptions,
        ) {
            Ok(state) => state,
            Err(failure) => return Ok(Err(failure)),
        };
    }
    Ok(Ok(state))
}

/// Binds the loop's names again on a state the body reached, taking each
/// binder's family and arguments from the instance it held at the loop head.
///
/// The head already decided what every binder names; a back edge only has to
/// find that resource again in whatever the body ended holding. Nothing here
/// re-reads the loop's source clauses, so the same rule serves the kernel's
/// own back edge and the surface `close_invariants` join.
pub(crate) fn c_loop_state_with_loop_binders_rebound(
    loop_head_state: &CState,
    state: &CState,
    binders: &[CLoopBinder],
    assumptions: &PureFactContext,
) -> Result<CState, String> {
    if binders.is_empty() {
        return Ok(state.clone());
    }
    let mut rebound = state.clone();
    let mut claimed: BTreeSet<Variable> = BTreeSet::new();
    for binder in binders {
        // D5: the back edge selects the instance the same way the head did,
        // with the clause's arguments re-evaluated in the current state. A
        // body that assigned `root = root->left` therefore hands the loop the
        // `tree_at(root)` at the new cursor, not the one it started from.
        let declared = binder.spec.as_ref().and_then(|spec| {
            let mut budget = ExecutionBudget::default();
            loop_binder_declared_arguments(state, spec, assumptions, &mut budget)
                .ok()
                .flatten()
        });
        let (name, arguments) = match declared {
            Some(declared) => declared,
            None => {
                let Some(head) = loop_head_state.resources().owned_instance(binder.identity) else {
                    continue;
                };
                (head.name.clone(), head.arguments.clone())
            }
        };
        rebound = rebind_one_loop_binder_instance(
            &rebound,
            binder.identity,
            &binder.name,
            &name,
            &arguments,
            &mut claimed,
            assumptions,
        )?;
    }
    Ok(rebound)
}

/// Moves one loop binder onto the instance it names in `state`.
///
/// The binder keeps the instance it already names when that instance still
/// has the right family and arguments. Otherwise exactly one owned instance
/// of that family may match, and it is renamed to the binder's identity. The
/// candidates come from the family's shape bucket, so the search costs the
/// instances of that family rather than the whole resource context.
fn rebind_one_loop_binder_instance(
    state: &CState,
    identity: Variable,
    binder: &str,
    name: &str,
    arguments: &ResourceArguments,
    claimed: &mut BTreeSet<Variable>,
    assumptions: &PureFactContext,
) -> Result<CState, String> {
    let arguments_match = |instance: &ResourceInstance| {
        instance.arguments.len() == arguments.len()
            && instance
                .arguments
                .iter()
                .zip(arguments.iter())
                .all(|(held, declared)| {
                    crate::kernel::resource_arguments_proven_equal(held, declared, assumptions)
                })
    };
    if state
        .resources()
        .owned_instance(identity)
        .is_some_and(|instance| instance.name == name && arguments_match(instance))
    {
        claimed.insert(identity);
        return Ok(state.clone());
    }
    let mut candidates = state
        .resources()
        .owned_instances_of_shape(name, arguments.len())
        .into_iter()
        .filter(|instance| !claimed.contains(&instance.identity) && arguments_match(instance))
        .cloned()
        .collect::<Vec<_>>();
    let Some(selected) = candidates.pop() else {
        return Err(format!(
            "loop binder `{binder}` has no owned `{name}` instance at its arguments here"
        ));
    };
    if !candidates.is_empty() {
        return Err(format!(
            "loop binder `{binder}` matches {} owned `{name}` instances at its arguments; a loop binder must name exactly one",
            candidates.len() + 1
        ));
    }
    claimed.insert(identity);
    let held = CResourceFact::own(CResource::Instance(selected.clone()));
    let Some(rebound) = ResourceInstance::new(
        identity,
        selected.name.clone(),
        selected.arguments.clone(),
        selected.schema.clone(),
        selected.fields.clone(),
    ) else {
        return Err(format!(
            "loop binder `{binder}` names an instance whose fields do not match its schema"
        ));
    };
    // The rename removes one exact instance fact and adds it back under the
    // binder's identity. Incremental consumption touches that fact's own
    // bucket instead of normalizing the ambient context.
    let Some(resources) = state
        .resources()
        .clone()
        .without_fact_incrementally(&held, assumptions)
    else {
        return Err(format!(
            "loop binder `{binder}` could not take the instance it names"
        ));
    };
    Ok(state.clone().with_resource_context(
        resources.unchecked_with_fact(CResourceFact::own(CResource::Instance(rebound))),
    ))
}

/// Whether a loop's structural `decreases` binder descends at this back edge,
/// and why not when it does not (D6).
///
/// The rule is the function-level one. The instance the binder ends holding
/// must be a direct contained child, in the exact resource definition, of the
/// instance it held at the loop head: the loop head's model selects one arm,
/// that arm names its children, and the back-edge instance must be one of them
/// with the submodel that child carries. A model is a finite inductive term,
/// so a strictly smaller submodel at every back edge is well-founded; no
/// counter, size function, or automatic unfolding takes part.
///
/// The evidence is the unfold that exposed the child: the arm comes from
/// [`crate::kernel::select_resource_model_arm`] over the premises this path
/// already carries, which is the one arm-selection decision in Click. Cost is
/// the selected arm's own children and the constructor's own fields; the
/// surrounding resource context is never scanned.
pub(crate) fn loop_structural_descent_failure(
    loop_head_state: &CState,
    back_edge_state: &CState,
    binders: &[CLoopBinder],
    measure: &str,
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Option<String> {
    let Some(binder) = binders.iter().find(|binder| binder.name == measure) else {
        return Some(format!(
            "loop `decreases {measure}` does not name a resource binder this loop declares"
        ));
    };
    let Some(head) = loop_head_state.resources().owned_instance(binder.identity) else {
        return Some(format!(
            "loop `decreases {measure}` has no owned instance at the loop head"
        ));
    };
    let Some(next) = back_edge_state.resources().owned_instance(binder.identity) else {
        return Some(format!(
            "loop `decreases {measure}` has no owned instance at the back edge"
        ));
    };
    let Some(definition) = definitions
        .iter()
        .find(|definition| definition.name() == head.name)
    else {
        return Some(format!(
            "resource measure `{}` has no definition",
            head.name
        ));
    };
    let Some(body) = definition.matched.as_ref() else {
        return Some(format!(
            "loop `decreases {measure}` needs a resource with a `match` body; `{}` has none",
            head.name
        ));
    };
    let Some(AlgebraicValue::Algebraic(model)) = head.fields.get(body.field_index) else {
        return Some(format!(
            "loop `decreases {measure}` names an instance whose matched field is not algebraic"
        ));
    };
    let Some(ResourceModelArmSelection::Constructor(constructor)) =
        crate::kernel::select_resource_model_arm(model, assumptions)
    else {
        return Some(format!(
            "loop `decreases {measure}` cannot name a child: the invariants do not say which `{}` constructor the instance at the loop head carries",
            head.name
        ));
    };
    let AlgebraicTermNode::Constructor { variant, fields } = &constructor.node else {
        return Some(format!(
            "loop `decreases {measure}` selected a non-constructor model"
        ));
    };
    let Some(arm) = body.arms.iter().find(|arm| &arm.variant == variant) else {
        return Some(format!(
            "loop `decreases {measure}` selected the unknown constructor `{variant}`"
        ));
    };
    for child in &arm.children {
        if child.resource != next.name {
            continue;
        }
        let Some(child_definition) = definitions
            .iter()
            .find(|definition| definition.name() == child.resource)
        else {
            continue;
        };
        let Some(child_body) = child_definition.matched.as_ref() else {
            continue;
        };
        let Some(submodel) = child
            .field_bindings
            .get(child_body.field_index)
            .and_then(|index| fields.get(*index))
        else {
            continue;
        };
        let Some(held) = next.fields.get(child_body.field_index) else {
            continue;
        };
        if crate::kernel::resource_arguments_proven_equal(held, submodel, assumptions) {
            return None;
        }
    }
    Some(format!(
        "loop `decreases {measure}` does not descend: the `{}` the binder holds at the back edge is not a direct contained child of the `{}` it held at the loop head, in the `{variant}` arm of `{}`",
        next.name, head.name, head.name
    ))
}

/// The back-edge state as the ownership join compares it: each loop binder
/// carrying the model it had at the head.
///
/// A binder's fields are what its invariants constrain, and a body is expected
/// to change them; those changes are checked as invariant preservation, not as
/// a change of ownership. The join therefore compares the binder's family and
/// arguments and sets its model aside.
pub(crate) fn c_loop_state_with_head_binder_models(
    next_state: &CState,
    head_state: &CState,
    binders: &[CLoopBinder],
) -> CState {
    let mut state = next_state.clone();
    for binder in binders {
        let identity = binder.identity;
        let Some(head) = head_state.resources().owned_instance(identity) else {
            continue;
        };
        let Some(held) = state.resources().owned_instance(identity).cloned() else {
            continue;
        };
        if held.fields == head.fields && held.arguments == head.arguments {
            continue;
        }
        let Some(compared) = ResourceInstance::new(
            identity,
            held.name.clone(),
            head.arguments.clone(),
            held.schema.clone(),
            head.fields.clone(),
        ) else {
            continue;
        };
        let Some(resources) = state.resources().clone().without_fact_incrementally(
            &CResourceFact::own(CResource::Instance(held)),
            &PureFactContext::new(),
        ) else {
            continue;
        };
        state = state.with_resource_context(
            resources.unchecked_with_fact(CResourceFact::own(CResource::Instance(compared))),
        );
    }
    state
}

/// Gives each loop binder instance fresh symbolic fields.
///
/// A loop head is an arbitrary visit, so the model a binder carries there is
/// whatever the invariants state about it, never the model it happened to
/// carry at loop entry. This is the resource-field counterpart of havocking
/// the locals the body writes.
fn havoc_loop_binder_instance_fields(
    state: &CState,
    resource_specs: &[CResourceSpec],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<CState> {
    let mut state = state.clone();
    for spec in resource_specs {
        let Some(identity) = spec.instance_identity() else {
            continue;
        };
        let Some(instance) = state.resources().owned_instance(identity).cloned() else {
            continue;
        };
        let arguments = match loop_binder_declared_arguments(&state, spec, assumptions, budget)? {
            Some((_, arguments)) => arguments,
            None => instance.arguments.clone(),
        };
        let fields =
            crate::kernel::functions::arbitrary_resource_instance_fields(&instance.schema, budget);
        let Some(havoced) = ResourceInstance::new(
            identity,
            instance.name.clone(),
            arguments,
            instance.schema.clone(),
            fields,
        ) else {
            continue;
        };
        let held = CResourceFact::own(CResource::Instance(instance));
        let Some(resources) = state
            .resources()
            .clone()
            .without_fact_incrementally(&held, &PureFactContext::new())
        else {
            continue;
        };
        state = state.with_resource_context(
            resources.unchecked_with_fact(CResourceFact::own(CResource::Instance(havoced))),
        );
    }
    Ok(state)
}

/// The family and arguments one `owns name: resource(args);` clause denotes
/// in `state`.
///
/// `None` means the clause could not be read here; the caller keeps whatever
/// the instance already carries rather than inventing arguments.
fn loop_binder_declared_arguments(
    state: &CState,
    spec: &CResourceSpec,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<(String, ResourceArguments)>> {
    let Some(inner) = spec.instance_resource_spec() else {
        return Ok(None);
    };
    Ok(
        match evaluate_function_resource_spec(state, &inner, assumptions, budget)? {
            Ok(CResourceFact::Own(CResource::Composite { name, arguments }, quantity))
                if quantity.as_const() == Some(1) =>
            {
                Some((name, arguments))
            }
            _ => None,
        },
    )
}

/// The read-only form of a resource the loop did not declare. Memory and
/// composite resources have one; an exclusive token or instance does not, so
/// the body simply does not hold it.
fn viewed_form_of_resource_fact(fact: &CResourceFact) -> Option<CResourceFact> {
    match fact {
        CResourceFact::View(_) => Some(fact.clone()),
        CResourceFact::Own(resource @ (CResource::Memory(_) | CResource::Composite { .. }), _) => {
            Some(CResourceFact::View(resource.clone()))
        }
        CResourceFact::Own(CResource::Token { .. } | CResource::Instance(_), _) => None,
    }
}

pub(super) fn collect_loop_effect_check_obligations(
    before_state: &CState,
    after_state: &CState,
    effect_checks: &[CLoopEffectCheck],
    facts: &[ExecutionPureFact],
    path_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ProofObligation>> {
    if effect_checks.is_empty() {
        return Ok(Vec::new());
    }

    let effective_assumptions = assumptions_with_path_context(assumptions, facts, path_obligations);
    let mut writes = after_state
        .memory()
        .differing_cell_pointers(before_state.memory())
        .into_iter()
        .filter(is_loop_effect_relevant_pointer)
        .filter(|pointer| {
            let has_disjoint_effect_summary = facts.iter().any(|fact| {
                matches!(
                    fact.proposition(),
                    Proposition::CMemoryEffectSummary { mutable_ranges, .. }
                        if effective_assumptions
                            .ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
                )
            });
            !has_disjoint_effect_summary
                || !explicit_atomic_equality_from_memory_derivations(
                    &Bitvector32Term::MemoryLoad(
                        before_state.memory().clone().into(),
                        Box::new(pointer.clone()),
                    ),
                    &Bitvector32Term::MemoryLoad(
                        after_state.memory().clone().into(),
                        Box::new(pointer.clone()),
                    ),
                    &effective_assumptions,
                )
        })
        .collect::<BTreeSet<_>>();
    writes.extend(
        facts
            .iter()
            .filter_map(|fact| match fact.proposition() {
                Proposition::CMemoryMutatesOnly { pointers, .. } => Some(pointers.as_slice()),
                _ => None,
            })
            .flatten()
            .cloned(),
    );
    let effect_summary_ranges = facts
        .iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::CMemoryEffectSummary { mutable_ranges, .. } => {
                Some(mutable_ranges.as_slice())
            }
            _ => None,
        })
        .flatten()
        .filter(|range| is_loop_effect_relevant_pointer(range.base()))
        .collect::<Vec<_>>();

    let mut obligations = Vec::new();
    for check in effect_checks {
        let mut segment_evaluation_failed = false;
        let segments = match check.effect() {
            CLoopEffect::Immutable => Vec::new(),
            CLoopEffect::Mutable(segments) => {
                if let Some(validated) = check.validated_ranges() {
                    validated
                        .iter()
                        .map(|range| EvaluatedMemorySegment {
                            base: range.base.clone(),
                            start: range.start.clone(),
                            end: range.end.clone(),
                            element_width: range.element_width,
                        })
                        .collect()
                } else if check.origin() == CLoopEffectOrigin::InheritedResourceDerived {
                    segment_evaluation_failed = true;
                    push_false_loop_effect_obligation(
                        &mut obligations,
                        loop_effect_failure_context(
                            check,
                            "inherited resource frame was not established from the checked entry transition".to_string(),
                        ),
                    );
                    Vec::new()
                } else {
                    let mut evaluated = Vec::new();
                    for (segment_index, segment) in segments.iter().enumerate() {
                        match evaluate_loop_effect_segment(
                            before_state,
                            segment,
                            &effective_assumptions,
                            budget,
                        )? {
                            Ok(segment) => evaluated.push(segment),
                            Err(message) => {
                                segment_evaluation_failed = true;
                                push_false_loop_effect_obligation(
                                    &mut obligations,
                                    loop_effect_failure_context(
                                        check,
                                        format!(
                                            "could not evaluate mutable segment {segment_index} in {:?}: {message}",
                                            check.effect()
                                        ),
                                    ),
                                );
                            }
                        }
                    }
                    evaluated
                }
            }
        };

        if segment_evaluation_failed {
            continue;
        }

        for pointer in &writes {
            if !segments.iter().any(|segment| {
                loop_effect_segment_contains_pointer(segment, pointer, &effective_assumptions)
            }) {
                push_false_loop_effect_obligation(
                    &mut obligations,
                    loop_effect_failure_context(
                        check,
                        format!(
                            "write to {pointer:?} is outside the mutable footprint; external writes: {writes:?}; declared effect: {:?}; evaluated segments: {segments:?}",
                            check.effect()
                        ),
                    ),
                );
            }
        }

        for range in &effect_summary_ranges {
            if !segments.iter().any(|segment| {
                loop_effect_segment_contains_range(segment, range, &effective_assumptions)
            }) {
                push_false_loop_effect_obligation(
                    &mut obligations,
                    loop_effect_failure_context(
                        check,
                        format!(
                            "effect summary range {range:?} is outside the mutable footprint; declared effect: {:?}; evaluated segments: {segments:?}",
                            check.effect()
                        ),
                    ),
                );
            }
        }
    }

    Ok(obligations)
}

pub(super) fn evaluate_loop_effect_segment(
    state: &CState,
    segment: &CMemorySegment,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<EvaluatedMemorySegment, String>> {
    let base = match evaluate_loop_effect_segment_value(
        state,
        &segment.base,
        assumptions,
        "segment base",
        budget,
    )? {
        Ok(CValue::Pointer(pointer)) => pointer.into_pointer(),
        Ok(value) => {
            return Ok(Err(format!(
                "segment base evaluated to {value:?}, not pointer"
            )));
        }
        Err(message) => return Ok(Err(message)),
    };
    let start = match evaluate_loop_effect_segment_value(
        state,
        &segment.start,
        assumptions,
        "segment start",
        budget,
    )? {
        Ok(CValue::Int32(value)) => value,
        Ok(value) => {
            return Ok(Err(format!(
                "segment start evaluated to {value:?}, not int32"
            )));
        }
        Err(message) => return Ok(Err(message)),
    };
    let end = match evaluate_loop_effect_segment_value(
        state,
        &segment.end,
        assumptions,
        "segment end",
        budget,
    )? {
        Ok(CValue::Int32(value)) => value,
        Ok(value) => {
            return Ok(Err(format!(
                "segment end evaluated to {value:?}, not int32"
            )));
        }
        Err(message) => return Ok(Err(message)),
    };
    let element_width = segment.element_width;

    Ok(Ok(EvaluatedMemorySegment {
        base,
        start,
        end,
        element_width,
    }))
}

pub(super) fn evaluate_loop_effect_segment_with_facts(
    state: &CState,
    segment: &CMemorySegment,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(EvaluatedMemorySegment, Vec<ExecutionPureFact>), String>> {
    let mut facts = Vec::new();
    let mut evaluate = |expression: &CExpression, label: &str| {
        let local_assumptions = assumptions_with_path_context(assumptions, &facts, &[]);
        let evaluated = evaluate_loop_effect_segment_value_with_facts(
            state,
            expression,
            &local_assumptions,
            label,
            budget,
        )?;
        let (value, new_facts) = match evaluated {
            Ok(evaluated) => evaluated,
            Err(message) => return Ok(Err(message)),
        };
        for fact in new_facts {
            if !facts.contains(&fact) {
                facts.push(fact);
            }
        }
        Ok(Ok(value))
    };
    let base = match evaluate(&segment.base, "segment base")? {
        Ok(CValue::Pointer(pointer)) => pointer.into_pointer(),
        Ok(value) => {
            return Ok(Err(format!(
                "segment base evaluated to {value:?}, not pointer"
            )));
        }
        Err(message) => return Ok(Err(message)),
    };
    let start = match evaluate(&segment.start, "segment start")? {
        Ok(CValue::Int32(value)) => value,
        Ok(value) => {
            return Ok(Err(format!(
                "segment start evaluated to {value:?}, not int32"
            )));
        }
        Err(message) => return Ok(Err(message)),
    };
    let end = match evaluate(&segment.end, "segment end")? {
        Ok(CValue::Int32(value)) => value,
        Ok(value) => {
            return Ok(Err(format!(
                "segment end evaluated to {value:?}, not int32"
            )));
        }
        Err(message) => return Ok(Err(message)),
    };
    let element_width = segment.element_width;
    Ok(Ok((
        EvaluatedMemorySegment {
            base,
            start,
            end,
            element_width,
        },
        facts,
    )))
}

pub(super) fn evaluate_loop_effect_segment_value(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    label: &str,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CValue, String>> {
    Ok(evaluate_loop_effect_segment_value_with_facts(
        state,
        expression,
        assumptions,
        label,
        budget,
    )?
    .map(|(value, _)| value))
}

fn evaluate_loop_effect_segment_value_with_facts(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    label: &str,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(CValue, Vec<ExecutionPureFact>), String>> {
    let paths = evaluate_c_expression_paths(state, expression, assumptions, budget)?;
    if paths.len() != 1 {
        return Ok(Err(format!(
            "{label} evaluated through {} paths, expected exactly one",
            paths.len()
        )));
    }
    let Some(path) = paths.into_iter().next() else {
        return Ok(Err(format!("{label} had no evaluation path")));
    };
    if !path.obligations.is_empty() {
        return Ok(Err(format!(
            "{label} left proof obligations: {:?}",
            path.obligations
        )));
    }
    match path.outcome {
        CExpressionOutcome::Value(value) => Ok(Ok((value, path.facts))),
        CExpressionOutcome::UndefinedBehavior(undefined_behavior) => Ok(Err(format!(
            "{label} produced undefined behavior: {undefined_behavior:?}"
        ))),
        CExpressionOutcome::RuntimeError(error) => {
            if let CRuntimeError::MissingResource { resource } = &error {
                crate::kernel::functions::record_resource_dependency(resource.clone());
            }
            Ok(Err(format!("{label} produced runtime error: {error:?}")))
        }
    }
}

pub(super) fn loop_effect_segment_contains_pointer(
    segment: &EvaluatedMemorySegment,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    let Some(index) =
        pointer.element_index_from_base_with_width(&segment.base, segment.element_width)
    else {
        return false;
    };
    condition_is_decided_true(
        assumptions,
        &ConditionTerm::signed_less_equal(segment.start.clone(), index.clone()),
    ) && condition_is_decided_true(
        assumptions,
        &ConditionTerm::signed_less_than(index, segment.end.clone()),
    )
}

pub(super) fn loop_effect_segment_contains_range(
    segment: &EvaluatedMemorySegment,
    range: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    if range.element_width() != segment.element_width {
        return false;
    }
    let Some(base_index) = range
        .base()
        .element_index_from_base_with_width(&segment.base, segment.element_width)
    else {
        return false;
    };
    let range_start = Bitvector32Term::add(base_index.clone(), range.start().clone());
    let range_end = Bitvector32Term::add(base_index, range.end().clone());
    condition_is_decided_true(
        assumptions,
        &ConditionTerm::signed_less_equal(segment.start.clone(), range_start),
    ) && condition_is_decided_true(
        assumptions,
        &ConditionTerm::signed_less_equal(range_end, segment.end.clone()),
    )
}

pub(super) fn is_loop_effect_relevant_pointer(pointer: &Pointer) -> bool {
    !pointer.block.starts_with("local:") && !pointer.block.starts_with("havoc:")
}

pub(super) fn loop_effect_failure_context(check: &CLoopEffectCheck, message: String) -> String {
    match check.context() {
        Some(context) => format!("{context}: {message}"),
        None => message,
    }
}

pub(super) fn push_false_loop_effect_obligation(
    obligations: &mut Vec<ProofObligation>,
    context: String,
) {
    obligations.push(
        ProofObligation::verification_condition(false_equals_true_proposition())
            .with_context(context),
    );
}

pub(super) fn false_equals_true_proposition() -> Proposition {
    Proposition::Equal(
        Term::Condition(ConditionTerm::Constant(false)),
        Term::Condition(ConditionTerm::Constant(true)),
    )
}

pub(super) fn assume_invariant_checks(
    state: &CState,
    loop_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &PureFactContext,
    prefix_facts: &[ExecutionPureFact],
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<(Vec<ExecutionPureFact>, Vec<ProofObligation>)>> {
    let mut contexts = vec![(prefix_facts.to_vec(), prefix_obligations.to_vec())];
    for check in invariant_checks {
        let mut next_contexts = Vec::new();
        for (facts, obligations) in contexts {
            let effective_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            for path in lower_spec_proposition_at_state_with_loop_entry(
                state,
                check.proposition(),
                Some(loop_entry_state),
                &effective_assumptions,
                budget,
            )? {
                let Some((mut facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &facts,
                    &obligations,
                    &path.facts,
                    &path.obligations,
                    assumptions,
                ) else {
                    continue;
                };
                // A loop invariant is an explicit induction hypothesis at the
                // fresh loop-top snapshot. Even when the entry assumptions can
                // derive it, retain the lowered proposition itself: the facts
                // used for that derivation may belong to an earlier snapshot
                // and are not a substitute for this loop's hypothesis after
                // havoc.
                if assumptions.proves_exact(&path.proposition) {
                    if !facts
                        .iter()
                        .any(|fact| fact.proposition() == &path.proposition)
                    {
                        facts.push(ExecutionPureFact::new(path.proposition));
                    }
                    next_contexts.push((facts, obligations));
                } else if add_path_fact(&mut facts, assumptions, path.proposition).is_some() {
                    next_contexts.push((facts, obligations));
                }
            }
        }
        contexts = next_contexts;
    }
    Ok(contexts)
}

/// What one evaluation path of a loop guard settled.
#[derive(Clone, Debug)]
pub(super) enum CConditionBranch {
    /// The guard produced a value, and its truthiness is this.
    Decided(bool),
    /// The guard produced no value at all on this path: an operand the
    /// function has no authority to read, an unresolved allocation, or
    /// undefined behavior reached while evaluating it. Such a path selects
    /// neither the iteration nor the exit, so it may never be dropped — the
    /// exit assumption would otherwise be the negation of the operands that
    /// happened to be evaluable, which is not the negation of the guard.
    Undecided(CStatementOutcome),
}

/// One way a loop guard can leave a state, with the facts and obligations
/// that path carries.
#[derive(Clone, Debug)]
pub(super) struct CConditionAssumption {
    pub(super) branch: CConditionBranch,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

impl CConditionAssumption {
    /// The statement outcome an undecided guard must be reported as, or
    /// `None` when the guard decided this path.
    pub(super) fn undecided_outcome(&self) -> Option<&CStatementOutcome> {
        match &self.branch {
            CConditionBranch::Decided(_) => None,
            CConditionBranch::Undecided(outcome) => Some(outcome),
        }
    }
}

/// Every way this guard can leave `state`: one entry per feasible value path,
/// plus one entry for each path on which the guard could not be evaluated.
pub(super) fn assume_condition_branches(
    state: &CState,
    condition: &CExpression,
    assumptions: &PureFactContext,
    prefix_facts: &[ExecutionPureFact],
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CConditionAssumption>> {
    let effective_assumptions =
        assumptions_with_path_context(assumptions, prefix_facts, prefix_obligations);
    let mut contexts = Vec::new();
    for condition_path in
        evaluate_c_expression_paths(state, condition, &effective_assumptions, budget)?
    {
        if matches!(condition_path.outcome, CExpressionOutcome::Value(_))
            && condition_path_is_ruled_out(&condition_path.facts, &effective_assumptions)
        {
            continue;
        }
        let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
            prefix_facts,
            prefix_obligations,
            &condition_path.facts,
            &condition_path.obligations,
            assumptions,
        ) else {
            continue;
        };
        let value = match condition_path.outcome {
            CExpressionOutcome::Value(value) => value,
            // The guard itself did not run to a value here. Keep the path and
            // name its outcome; every caller reports it rather than choosing
            // an arm for it.
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                contexts.push(CConditionAssumption {
                    branch: CConditionBranch::Undecided(CStatementOutcome::UndefinedBehavior(
                        undefined_behavior,
                    )),
                    facts,
                    obligations,
                });
                continue;
            }
            CExpressionOutcome::RuntimeError(error) => {
                contexts.push(CConditionAssumption {
                    branch: CConditionBranch::Undecided(CStatementOutcome::RuntimeError(error)),
                    facts,
                    obligations,
                });
                continue;
            }
        };
        for truthiness_path in c_truthiness_paths(value, facts, obligations, assumptions) {
            contexts.push(CConditionAssumption {
                branch: CConditionBranch::Decided(truthiness_path.is_true),
                facts: truthiness_path.facts,
                obligations: truthiness_path.obligations,
            });
        }
    }
    Ok(contexts)
}

/// The guard paths that select `desired_truthiness`, together with every path
/// the guard did not decide. An undecided path belongs to both requests: it
/// rules out neither the iteration nor the exit.
pub(super) fn assume_condition_truthiness(
    state: &CState,
    condition: &CExpression,
    assumptions: &PureFactContext,
    prefix_facts: &[ExecutionPureFact],
    prefix_obligations: &[ProofObligation],
    desired_truthiness: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CConditionAssumption>> {
    Ok(assume_condition_branches(
        state,
        condition,
        assumptions,
        prefix_facts,
        prefix_obligations,
        budget,
    )?
    .into_iter()
    .filter(|assumption| !matches!(assumption.branch, CConditionBranch::Decided(is_true) if is_true != desired_truthiness))
    .collect())
}

/// Names an undecided loop guard for a refusal context, without dumping the
/// guard's internal representation.
pub(super) fn undecided_loop_guard_context(outcome: &CStatementOutcome) -> String {
    let reason = match outcome {
        CStatementOutcome::UndefinedBehavior(undefined_behavior) => {
            format!("it reaches undefined behavior ({undefined_behavior:?})")
        }
        CStatementOutcome::RuntimeError(error) => {
            crate::kernel::api::describe_certification_runtime_error(error)
        }
        _ => "it produced no value".to_string(),
    };
    format!("the loop condition could not be evaluated on this path: {reason}")
}

pub(super) fn havoc_loop_modified_locals(
    state: &CState,
    body: &CStatement,
    variables: &mut KernelVariableGenerator,
    mutable_ranges: Option<&[CMemoryRange]>,
) -> CState {
    let mut state = state.clone();
    let mut names = BTreeSet::new();
    collect_loop_modified_locals(body, &mut names);
    let may_write_memory = statement_may_write_memory(&state, body);
    if may_write_memory {
        // A local whose address escapes can be written by the loop body
        // through a pointer without ever being assigned by name, so treat it
        // as loop-modified too (otherwise its stale value survives the havoc).
        names.extend(address_escaped_scalar_locals(&state, body));
    }
    for name in names {
        let Some(binding) = state.locals.binding(&name) else {
            continue;
        };
        let c_type = match binding {
            CLocalBinding::Object { c_type, .. } => *c_type,
            CLocalBinding::GlobalObject { .. } => {
                // File-scope globals and function-local statics are
                // represented only by memory. The memory havoc below
                // refreshes their modified slots; there is no local value to
                // resynchronize here.
                continue;
            }
            CLocalBinding::UninitializedObject { .. }
            | CLocalBinding::ArrayObject { .. }
            | CLocalBinding::AggregateObject { .. } => continue,
        };
        let value = match c_type {
            CType::Void => continue,
            CType::Bool => CValue::Bool(Bitvector32Term::Variable(variables.next())),
            CType::VoidPointer => {
                CValue::typed_pointer(Pointer::symbolic(variables.next()), c_type)
            }
            CType::Int16 => int16(Bitvector32Term::Variable(variables.next())),
            CType::Int32 => int32(Bitvector32Term::Variable(variables.next())),
            CType::UInt8 => uint8(Bitvector32Term::Variable(variables.next())),
            CType::UInt16 => uint16(Bitvector32Term::Variable(variables.next())),
            CType::UInt32 => uint32(Bitvector32Term::Variable(variables.next())),
            CType::Int64 => CValue::Int64(Bitvector32Term::Variable(variables.next())),
            CType::UInt64 => CValue::UInt64(Bitvector32Term::Variable(variables.next())),
            CType::Float32 => CValue::Float32(Bitvector32Term::Variable(variables.next())),
            CType::Float64 => CValue::Float64(Bitvector32Term::Variable(variables.next())),
            // A pointer local reassigned in the body (`p = p + 1`) must not
            // keep its entry value across the abstract iteration, exactly as
            // the join abstraction treats it; an invariant must relate it.
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
                CValue::typed_pointer(Pointer::symbolic(variables.next()), c_type)
            }
            CType::FunctionPointer(_) => {
                CValue::typed_pointer(Pointer::symbolic_function(variables.next()), c_type)
            }
            // Array objects are never assigned by name (C forbids it), and
            // they bind as array objects rather than scalar objects above.
            CType::Int32Array(_)
            | CType::UInt8Array(_)
            | CType::Int16Array(_)
            | CType::UInt16Array(_)
            | CType::UInt32Array(_)
            | CType::Int64Array(_)
            | CType::UInt64Array(_)
            | CType::Float32Array(_)
            | CType::Float64Array(_) => continue,
        };
        sync_stack_local(&mut state, &name, &value);
        state.locals.set_typed(name, value, c_type);
    }
    if may_write_memory {
        // Keep only scalar stack local cells (havoced above and re-synced via
        // sync_stack_local); every other concrete cell could have been
        // overwritten by the loop body through a pointer. Address-escaped
        // locals were havoced above, so their preserved cells now hold fresh
        // symbolic values rather than stale ones.
        let preserved_blocks: BTreeSet<PointerBlock> = state
            .locals
            .bindings
            .keys()
            .filter(|name| state.locals.get(name).is_some())
            .filter_map(|name| state.locals.slot(name).map(|slot| slot.block.clone()))
            .collect();
        let havoced_memory = state.memory.clone().with_loop_memory_havoc(
            variables.next(),
            &preserved_blocks,
            mutable_ranges,
        );
        state.set_memory(havoced_memory);
    }
    state
}

pub(super) fn statement_may_write_memory(state: &CState, statement: &CStatement) -> bool {
    match statement {
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_) => false,
        CStatement::Assign { name, .. } => state.locals.is_global_object(name),
        CStatement::CallAssign { .. }
        | CStatement::Call { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::CopyAggregate { .. }
        | CStatement::Update { .. } => true,
        CStatement::Seq(first, second) => {
            statement_may_write_memory(state, first) || statement_may_write_memory(state, second)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            statement_may_write_memory(state, then_branch)
                || statement_may_write_memory(state, else_branch)
        }
        CStatement::ContinueWithStep { step } => statement_may_write_memory(state, step),
        CStatement::While { body, .. } => statement_may_write_memory(state, body),
        CStatement::Switch { cases, .. } => cases
            .iter()
            .any(|case| statement_may_write_memory(state, &case.body)),
    }
}

pub(super) fn collect_loop_modified_locals(statement: &CStatement, names: &mut BTreeSet<String>) {
    match statement {
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::CopyAggregate { .. } => {}
        CStatement::Update { target, .. } => {
            if let CExpression::Variable(name) = target {
                names.insert(name.clone());
            }
        }
        CStatement::Assign { name, .. } => {
            names.insert(name.clone());
        }
        CStatement::CallAssign { target, .. } => {
            names.insert(target.clone());
        }
        CStatement::Call { .. } => {}
        CStatement::HeapAllocate { target, .. } => {
            names.insert(target.clone());
        }
        CStatement::HeapFree { .. } => {}
        CStatement::Seq(first, second) => {
            collect_loop_modified_locals(first, names);
            collect_loop_modified_locals(second, names);
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_loop_modified_locals(then_branch, names);
            collect_loop_modified_locals(else_branch, names);
        }
        CStatement::ContinueWithStep { step } => {
            collect_loop_modified_locals(step, names);
        }
        CStatement::While { body, .. } => {
            collect_loop_modified_locals(body, names);
        }
        CStatement::Switch { cases, .. } => {
            for case in cases {
                collect_loop_modified_locals(&case.body, names);
            }
        }
    }
}

/// Scalar locals the loop body could write *through a pointer* without ever
/// assigning them by name. `collect_loop_modified_locals` ignores `Store`, so
/// these would otherwise be wrongly preserved across the loop havoc. A local
/// counts as escaped if a live pointer in the pre-loop state already points at
/// its block, or if the body takes its address syntactically.
pub(super) fn address_escaped_scalar_locals(state: &CState, body: &CStatement) -> BTreeSet<String> {
    let mut escaped = BTreeSet::new();
    collect_address_taken_locals(body, &mut escaped);

    let record_pointer = |value: &CValue, escaped: &mut BTreeSet<String>| {
        if let CValue::Pointer(pointer) = value
            && let Some(name) = state.locals.name_for_slot(pointer)
        {
            escaped.insert(name.to_string());
        }
    };
    for name in state.locals.bindings.keys() {
        if let Some(value) = state.locals.get(name) {
            record_pointer(value, &mut escaped);
        }
    }
    for value in state.memory.cells.values() {
        record_pointer(value, &mut escaped);
    }
    for value in state.memory.union_cells.values() {
        record_pointer(value, &mut escaped);
    }
    escaped
}

pub(crate) fn collect_address_taken_locals(statement: &CStatement, names: &mut BTreeSet<String>) {
    match statement {
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. } => {}
        CStatement::Assign { expression, .. } => {
            collect_address_taken_in_expression(expression, names)
        }
        CStatement::CallAssign { arguments, .. } => {
            for argument in arguments {
                collect_address_taken_in_expression(argument, names);
            }
        }
        CStatement::Call { arguments, .. } => {
            for argument in arguments {
                collect_address_taken_in_expression(argument, names);
            }
        }
        CStatement::HeapAllocate { .. } => {}
        CStatement::HeapFree { pointer } => {
            collect_address_taken_in_expression(pointer, names);
        }
        CStatement::Assert { condition, .. } => {
            collect_address_taken_in_expression(condition, names)
        }
        CStatement::Return(expression) => collect_address_taken_in_expression(expression, names),
        CStatement::Store { pointer, value } => {
            collect_address_taken_in_expression(pointer, names);
            collect_address_taken_in_expression(value, names);
        }
        CStatement::TypedStore { pointer, value, .. } => {
            collect_address_taken_in_expression(pointer, names);
            collect_address_taken_in_expression(value, names);
        }
        CStatement::CopyAggregate { target, source, .. } => {
            collect_address_taken_in_expression(target, names);
            collect_address_taken_in_expression(source, names);
        }
        CStatement::Update {
            target, operand, ..
        } => {
            collect_address_taken_in_expression(target, names);
            collect_address_taken_in_expression(operand, names);
        }
        CStatement::Seq(first, second) => {
            collect_address_taken_locals(first, names);
            collect_address_taken_locals(second, names);
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_address_taken_in_expression(condition, names);
            collect_address_taken_locals(then_branch, names);
            collect_address_taken_locals(else_branch, names);
        }
        CStatement::ContinueWithStep { step } => {
            collect_address_taken_locals(step, names);
        }
        CStatement::While {
            condition, body, ..
        } => {
            collect_address_taken_in_expression(condition, names);
            collect_address_taken_locals(body, names);
        }
        CStatement::Switch { expression, cases } => {
            collect_address_taken_in_expression(expression, names);
            for case in cases {
                collect_address_taken_locals(&case.body, names);
            }
        }
    }
}

pub(super) fn collect_address_taken_in_expression(
    expression: &CExpression,
    names: &mut BTreeSet<String>,
) {
    match expression {
        // `&target`: any local reachable in the target may have its address
        // escape, so conservatively record every variable it mentions.
        CExpression::AddressOf(target) => collect_variable_names(target, names),
        CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => {}
        CExpression::Cast { expression, .. } => {
            collect_address_taken_in_expression(expression, names)
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_address_taken_in_expression(condition, names);
            collect_address_taken_in_expression(then_branch, names);
            collect_address_taken_in_expression(else_branch, names);
        }
        CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. } => {
            collect_address_taken_in_expression(expression, names)
        }
        CExpression::PointerOffsetBytes { pointer, .. } => {
            collect_address_taken_in_expression(pointer, names)
        }
        CExpression::Not(inner) | CExpression::Load(inner) => {
            collect_address_taken_in_expression(inner, names)
        }
        CExpression::TypedLoad { pointer, .. } => {
            collect_address_taken_in_expression(pointer, names)
        }
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
        | CExpression::BitwiseXor(left, right)
        | CExpression::Index(left, right) => {
            collect_address_taken_in_expression(left, names);
            collect_address_taken_in_expression(right, names);
        }
        CExpression::BitwiseNot(expression) => {
            collect_address_taken_in_expression(expression, names);
        }
    }
}

pub(super) fn collect_variable_names(expression: &CExpression, names: &mut BTreeSet<String>) {
    match expression {
        CExpression::Variable(name) => {
            names.insert(name.clone());
        }
        CExpression::Value(_) | CExpression::FunctionAddress(_) => {}
        CExpression::Cast { expression, .. } => collect_variable_names(expression, names),
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_variable_names(condition, names);
            collect_variable_names(then_branch, names);
            collect_variable_names(else_branch, names);
        }
        CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. } => {
            collect_variable_names(expression, names)
        }
        CExpression::PointerOffsetBytes { pointer, .. } => collect_variable_names(pointer, names),
        CExpression::AddressOf(inner) | CExpression::Not(inner) | CExpression::Load(inner) => {
            collect_variable_names(inner, names)
        }
        CExpression::TypedLoad { pointer, .. } => collect_variable_names(pointer, names),
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
        | CExpression::BitwiseXor(left, right)
        | CExpression::Index(left, right) => {
            collect_variable_names(left, names);
            collect_variable_names(right, names);
        }
        CExpression::BitwiseNot(expression) => {
            collect_variable_names(expression, names);
        }
    }
}
