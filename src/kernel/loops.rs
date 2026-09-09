use super::prelude::*;

#[cfg(test)]
mod pointee_const_return_tests {
    use super::*;

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
                    state.memory =
                        copy_aggregate_fields(state.memory, pointer.pointer(), &slot, layout);
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
                    } else {
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
            body,
            do_while,
        } if !invariant_checks.is_empty() || !effect_checks.is_empty() => {
            execute_c_while_verification_paths(
                state,
                condition,
                invariant,
                invariant_checks,
                effect_checks,
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
        body,
        assumptions,
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

fn condition_value_is_proven(
    assumptions: &PureFactContext,
    condition: &ConditionTerm,
    value: bool,
) -> bool {
    assumptions.proves(&Proposition::ConditionIs(condition.clone(), value))
        || (!value
            && condition_complement(condition).is_some_and(|complement| {
                assumptions.proves(&Proposition::ConditionIs(complement, true))
            }))
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
        body,
        assumptions,
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
    body: &CStatement,
    assumptions: &PureFactContext,
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

    let entry_obligations = if initialization_proven {
        Vec::new()
    } else {
        collect_invariant_check_obligations(
            state,
            state,
            invariant_checks,
            InvariantPhase::Entry,
            assumptions,
            budget,
        )?
    };
    let (top_state, whole_loop_effect_summaries) =
        prepare_loop_top_state(state, effect_checks, body, assumptions, budget, variables)?;
    let (preservation_obligations, mut final_exit_paths) =
        if let Some(environment) = preservation_environment {
            let summary = collect_loop_preservation_summary(
                state,
                &top_state,
                condition,
                invariant_checks,
                effect_checks,
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
            for (facts, obligations) in assume_condition_truthiness(
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
                    &facts,
                    &obligations,
                    assumptions,
                ) else {
                    continue;
                };
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::Normal(candidate.state().clone()),
                    facts,
                    obligations,
                });
            }
        }
    }
    let invariant_contexts = assume_invariant_checks(
        &top_state,
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
                &top_state,
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
                &top_state,
                condition,
                assumptions,
                &invariant_facts,
                &invariant_obligations,
                false,
                budget,
            )?;
            for (facts, mut obligations) in condition_contexts {
                append_required_proof_obligations(
                    &mut obligations,
                    assumptions,
                    &loop_check_obligations,
                );
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

/// The proof of one kernel-lowered invariant path. This retains the actual
/// binder identities and safety obligations, rather than a surface spelling
/// that would need to be lowered (and proved) again.
#[derive(Clone)]
pub(crate) struct CheckedInvariantLowering {
    check_index: usize,
    path: SpecPropositionPath,
    context: PureFactContext,
    required: Vec<Proposition>,
    obligation_proofs: Vec<PropositionDerivation>,
    goal_proof: PropositionDerivation,
}

impl CheckedInvariantLowering {
    /// Check only the supplied evidence, in its original path context. No
    /// derivation builder or alternate proof search belongs in this method.
    pub(crate) fn recheck(&self) -> bool {
        let required = self
            .required
            .iter()
            .collect::<std::collections::BTreeSet<_>>();
        self.path
            .obligations
            .iter()
            .all(|obligation| required.contains(obligation.proposition()))
            && self.required.len() == self.obligation_proofs.len()
            && self
                .required
                .iter()
                .zip(&self.obligation_proofs)
                .all(|(goal, proof)| proof.conclusion() == goal && proof.check(&self.context))
            && self.goal_proof.conclusion() == &self.path.proposition
            && self.goal_proof.check(&self.context)
    }
}

type VerifiedInvariantPath = (
    Vec<ExecutionPureFact>,
    Vec<ProofObligation>,
    std::sync::Arc<CheckedInvariantLowering>,
);

#[cfg(test)]
mod checked_lowering_tests {
    use super::*;

    fn predicate(name: &str) -> Proposition {
        Proposition::Predicate {
            name: name.into(),
            arguments: vec![],
        }
    }

    fn record(unrelated: usize) -> std::sync::Arc<CheckedInvariantLowering> {
        let goal = predicate("invariant");
        let safety = predicate("load_safety");
        let mut context = PureFactContext::new()
            .assume_proposition(goal.clone())
            .assume_proposition(safety.clone());
        for index in 0..unrelated {
            context = context.assume_proposition(predicate(&format!("unrelated_{index}")));
        }
        verify_lowered_invariant_path(
            0,
            &[],
            &[],
            SpecPropositionPath {
                proposition: goal,
                facts: vec![],
                obligations: vec![ProofObligation::verification_condition(safety)],
            },
            &context,
        )
        .unwrap()
        .unwrap()
        .2
    }

    #[test]
    fn checked_lowering_retains_and_checks_every_proof_slot() {
        let original = record(0);
        assert!(original.recheck());
        assert_eq!(original.path.obligations.len(), 1);
        assert_eq!(original.obligation_proofs.len(), 1);
        let mut missing = (*original).clone();
        missing.obligation_proofs.clear();
        assert!(!missing.recheck());
        missing.required.clear();
        assert!(
            !missing.recheck(),
            "dropping the target must not hide a missing proof"
        );
        let mut wrong = (*original).clone();
        wrong.obligation_proofs[0] = wrong.goal_proof.clone();
        assert!(!wrong.recheck());
        let mut wrong_goal = (*original).clone();
        wrong_goal.path.proposition = predicate("different_invariant");
        assert!(!wrong_goal.recheck());
        let mut wrong_context = (*original).clone();
        wrong_context.context = PureFactContext::new();
        assert!(!wrong_context.recheck());
    }

    #[test]
    fn checked_lowering_does_not_assume_its_own_read_safety() {
        let goal = predicate("already_proved_value");
        let safety = Proposition::CMemoryLoadable {
            memory: CMemory::new(),
            base: Pointer {
                block: "missing".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: Bitvector32Term::Constant(4),
        };
        let path = SpecPropositionPath {
            proposition: goal.clone(),
            facts: vec![],
            // The expression lowerer marks provisional read obligations as
            // assumable; record construction must not trust that flag.
            obligations: vec![ProofObligation::new(safety.clone())],
        };
        let context = PureFactContext::new().assume_proposition(goal);
        let error = verify_lowered_invariant_path(0, &[], &[], path.clone(), &context)
            .err()
            .expect("a value proof alone cannot establish read safety");
        assert!(error.contains("missing path obligation"));
        let (_, _, record) =
            verify_lowered_invariant_path(0, &[], &[], path, &context.assume_proposition(safety))
                .unwrap()
                .unwrap();
        assert_eq!(record.obligation_proofs.len(), 1);
        assert!(record.recheck());
        let mut missing = (*record).clone();
        missing.required.clear();
        missing.obligation_proofs.clear();
        assert!(!missing.recheck());
    }

    #[test]
    fn checked_lowering_recheck_does_not_scan_ambient_facts() {
        let samples = [16, 32, 64, 128].map(|size| {
            let record = record(size);
            let shared = record.clone();
            assert!(std::sync::Arc::ptr_eq(&record, &shared));
            let (valid, work) =
                crate::instrumentation::measure_deterministic_work(|| record.recheck());
            assert!(valid);
            work
        });
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0].saturating_mul(2).saturating_add(8),
                "{samples:?}"
            );
        }
    }
}

fn verify_lowered_invariant_path(
    check_index: usize,
    facts: &[ExecutionPureFact],
    obligations: &[ProofObligation],
    path: SpecPropositionPath,
    assumptions: &PureFactContext,
) -> Result<Option<VerifiedInvariantPath>, String> {
    let Some((mut merged_facts, merged_obligations)) = merge_execution_pure_facts_and_obligations(
        facts,
        obligations,
        &path.facts,
        &path.obligations,
        assumptions,
    ) else {
        return Ok(None);
    };
    // Lowering may provisionally assume read safety while constructing its
    // value. The retained proof must establish that safety independently;
    // otherwise its own obligation would become an exact premise.
    let local = assumptions_with_path_context(assumptions, &merged_facts, &[]);
    let mut required = Vec::new();
    let mut obligation_proofs = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    // Path merging may discharge an obligation from exact ambient facts.
    // Retain that proof too: the original lowered path still requires it.
    for obligation in merged_obligations.iter().chain(path.obligations.iter()) {
        let proposition = obligation.proposition();
        if !seen.insert(proposition.clone()) {
            continue;
        }
        let Some(derivation) = local
            .derive_proposition_without_premise_minimization(proposition)
            .or_else(|| local.derive_simp_proposition(proposition))
        else {
            if let Some(context) = crate::instrumentation::exceeded_verification_limit_context() {
                return Err(format!("verification budget exhausted inside {context}"));
            }
            return Err(format!(
                "invariant {check_index} is missing path obligation: {proposition:?}"
            ));
        };
        required.push(proposition.clone());
        obligation_proofs.push(derivation);
    }
    let Some(derivation) = local
        .derive_proposition_without_premise_minimization(&path.proposition)
        .or_else(|| local.derive_simp_proposition(&path.proposition))
    else {
        if let Some(context) = crate::instrumentation::exceeded_verification_limit_context() {
            return Err(format!("verification budget exhausted inside {context}"));
        }
        return Err(format!(
            "invariant {check_index} is missing path goal: {:?}",
            path.proposition
        ));
    };
    let lowering = std::sync::Arc::new(CheckedInvariantLowering {
        check_index,
        path,
        context: local,
        required,
        obligation_proofs,
        goal_proof: derivation,
    });
    if !lowering.recheck() {
        return Err(format!(
            "invariant {check_index} lowering evidence check failed"
        ));
    }
    if !merged_facts
        .iter()
        .any(|fact| fact.proposition() == &lowering.path.proposition)
    {
        merged_facts.push(ExecutionPureFact::new(lowering.path.proposition.clone()));
    }
    Ok(Some((merged_facts, merged_obligations, lowering)))
}

#[cfg(test)]
thread_local! {
    static INVARIANT_DISCOVERY_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn invariant_discovery_calls() -> usize {
    INVARIANT_DISCOVERY_CALLS.get()
}

pub(super) fn verify_invariant_checks_at_back_edge_using(
    state: &CState,
    loop_entry_state: &CState,
    checks: &[CLoopInvariantCheck],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Result<Vec<std::sync::Arc<CheckedInvariantLowering>>, String> {
    #[cfg(test)]
    INVARIANT_DISCOVERY_CALLS.set(INVARIANT_DISCOVERY_CALLS.get() + 1);
    let mut contexts = vec![(Vec::new(), Vec::new())];
    let mut lowerings = Vec::new();
    for (check_index, check) in checks.iter().enumerate() {
        let mut next_contexts = Vec::new();
        for (facts, obligations) in contexts {
            let lowering_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations)
                    .defer_non_exact_condition_reasoning()
                    .defer_non_exact_loadability_obligations();
            let paths = lower_spec_proposition_at_state_with_loop_entry(
                state,
                check.proposition(),
                Some(loop_entry_state),
                &lowering_assumptions,
                budget,
            )
            .map_err(|error| format!("could not lower invariant paths: {error:?}"))?;
            if paths.len() <= 1 {
                for path in paths {
                    if let Some(context) = verify_lowered_invariant_path(
                        check_index,
                        &facts,
                        &obligations,
                        path,
                        assumptions,
                    )? {
                        let (facts, obligations, lowering) = context;
                        next_contexts.push((facts, obligations));
                        lowerings.push(lowering);
                    }
                }
                continue;
            }
            let worker_count = std::thread::available_parallelism()
                .map(usize::from)
                .unwrap_or(1)
                .min(8)
                .min(paths.len());
            if worker_count == 1 {
                for path in paths {
                    if let Some(context) = verify_lowered_invariant_path(
                        check_index,
                        &facts,
                        &obligations,
                        path,
                        assumptions,
                    )? {
                        let (facts, obligations, lowering) = context;
                        next_contexts.push((facts, obligations));
                        lowerings.push(lowering);
                    }
                }
                continue;
            }
            let mut work = (0..worker_count).map(|_| Vec::new()).collect::<Vec<_>>();
            for (index, path) in paths.into_iter().enumerate() {
                work[index % worker_count].push((index, path));
            }
            let mut verified = std::thread::scope(|scope| {
                let handles = work
                    .into_iter()
                    .map(|worker_paths| {
                        let facts = &facts;
                        let obligations = &obligations;
                        std::thread::Builder::new()
                            .name(format!("click-invariant-{check_index}"))
                            .stack_size(8 * 1024 * 1024)
                            .spawn_scoped(scope, move || {
                                worker_paths
                                    .into_iter()
                                    .map(|(index, path)| {
                                        Ok((
                                            index,
                                            verify_lowered_invariant_path(
                                                check_index,
                                                facts,
                                                obligations,
                                                path,
                                                assumptions,
                                            )?,
                                        ))
                                    })
                                    .collect::<Result<Vec<_>, String>>()
                            })
                            .map_err(|error| format!("could not start invariant verifier: {error}"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                handles
                    .into_iter()
                    .map(|handle| {
                        handle
                            .join()
                            .map_err(|_| "invariant verifier thread panicked".to_string())?
                    })
                    .collect::<Result<Vec<_>, String>>()
            })?;
            let mut verified = verified.drain(..).flatten().collect::<Vec<_>>();
            verified.sort_by_key(|(index, _)| *index);
            for (facts, obligations, lowering) in
                verified.into_iter().filter_map(|(_, context)| context)
            {
                next_contexts.push((facts, obligations));
                lowerings.push(lowering);
            }
        }
        contexts = next_contexts;
    }
    if contexts.is_empty() {
        return Err("invariant bundle has no reachable lowering path".to_string());
    }
    debug_assert!(lowerings.iter().all(|path| path.check_index < checks.len()));
    Ok(lowerings)
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
                let proposition = wrap_path_context(path.proposition, &facts, &obligations);
                if without_search {
                    add_required_proof_obligation_without_search(
                        &mut obligations,
                        &obligation_assumptions,
                        proposition,
                        invariant_context(check, phase),
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct LoopPreservationSummary {
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) final_exit_paths: Vec<CStatementExecutionPath>,
}

pub(super) fn collect_loop_preservation_summary(
    loop_entry_state: &CState,
    top_state: &CState,
    condition: &CExpression,
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
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
    let composite_resource_definitions = environment
        .functions
        .values()
        .flat_map(|function| function.composite_resource_definitions().iter().cloned())
        .fold(Vec::new(), |mut definitions, definition| {
            if !definitions.contains(&definition) {
                definitions.push(definition);
            }
            definitions
        });
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
            vec![(invariant_facts.clone(), invariant_obligations.clone())]
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
        for (condition_facts, condition_obligations) in condition_contexts {
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
                        for (may_continue, condition_contexts) in [
                            (
                                true,
                                assume_condition_truthiness(
                                    &next_state,
                                    condition,
                                    assumptions,
                                    &body_path.facts,
                                    &body_path.obligations,
                                    true,
                                    budget,
                                )?,
                            ),
                            (
                                false,
                                assume_condition_truthiness(
                                    &next_state,
                                    condition,
                                    assumptions,
                                    &body_path.facts,
                                    &body_path.obligations,
                                    false,
                                    budget,
                                )?,
                            ),
                        ] {
                            for (condition_facts, condition_obligations) in condition_contexts {
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
                                let path_obligations = if do_while && !may_continue {
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
                                let mut state_obligations = condition_obligations.clone();
                                if may_continue
                                    && let Err(message) =
                                        c_loop_state_components_match_at_back_edge_inner(
                                            top_state,
                                            &next_state,
                                            &composite_resource_definitions,
                                            &path_assumptions,
                                        )
                                {
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
                                        outcome: CStatementOutcome::Normal(next_state.clone()),
                                        facts: final_path_facts,
                                        obligations: final_obligations,
                                    });
                                }
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
                            outcome: CStatementOutcome::Normal(next_state),
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

pub(super) fn prepare_loop_top_state(
    entry_state: &CState,
    effect_checks: &[CLoopEffectCheck],
    body: &CStatement,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<(CState, Vec<Proposition>)> {
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
    Ok((top_state, summaries))
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
    assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(segment.start.clone(), index.clone()),
        true,
    )) && assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_than(index, segment.end.clone()),
        true,
    ))
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
    assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(segment.start.clone(), range_start),
        true,
    )) && assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(range_end, segment.end.clone()),
        true,
    ))
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
                if assumptions.proves(&path.proposition) {
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

pub(super) fn assume_condition_truthiness(
    state: &CState,
    condition: &CExpression,
    assumptions: &PureFactContext,
    prefix_facts: &[ExecutionPureFact],
    prefix_obligations: &[ProofObligation],
    desired_truthiness: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<(Vec<ExecutionPureFact>, Vec<ProofObligation>)>> {
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
        let CExpressionOutcome::Value(value) = condition_path.outcome else {
            continue;
        };
        for truthiness_path in c_truthiness_paths(value, facts, obligations, assumptions) {
            if truthiness_path.is_true == desired_truthiness {
                contexts.push((truthiness_path.facts, truthiness_path.obligations));
            }
        }
    }
    Ok(contexts)
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
        state.memory = state.memory.with_loop_memory_havoc(
            variables.next(),
            &preserved_blocks,
            mutable_ranges,
        );
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
