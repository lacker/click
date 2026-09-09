use super::prelude::*;

#[cfg(test)]
mod callback_contract_tests;

#[cfg(test)]
mod pointee_const_return_tests {
    use super::*;

    fn function(constant: bool) -> CFunction {
        CFunction::new(
            CType::UInt8Pointer,
            "text",
            Vec::new(),
            c_return(c_int32_literal(0)),
        )
        .with_return_pointee_constant(constant)
    }

    fn pointer(constant: bool) -> CValue {
        CValue::typed_pointer(Pointer::symbolic(Variable(910)), CType::UInt8Pointer)
            .with_pointer_pointee_constant(constant)
    }

    #[test]
    fn pointee_const_return_coercion_enforces_declared_qualifier() {
        for source_const in [false, true] {
            for return_const in [false, true] {
                let result = coerce_function_return_value(
                    pointer(source_const),
                    &function(return_const),
                    &mut Vec::new(),
                    &PureFactContext::new(),
                );
                assert_eq!(result.is_some(), !source_const || return_const);
                if let Some(CValue::Pointer(pointer)) = result {
                    assert_eq!(pointer.pointee_constant(), return_const);
                }
            }
        }
    }

    #[test]
    fn pointee_const_return_symbolic_result_and_binding_preserve_qualifier() {
        let function = function(true);
        let value = symbolic_function_result(&function, Variable(911));
        assert!(matches!(&value, CValue::Pointer(pointer) if pointer.pointee_constant()));
        let mut state = CState::new();
        set_function_result(&mut state, &function, value);
        assert!(
            matches!(state.locals.binding("result"), Some(CLocalBinding::Object {
            value: CValue::Pointer(pointer), pointee_constant: true, ..
        }) if pointer.pointee_constant())
        );
    }

    #[test]
    fn pointee_const_return_contract_signature_checks_qualifier() {
        let mutable = function(false);
        assert!(!mutable.return_pointee_is_constant());
        let constant = function(true);
        let contract = CFunctionContract::new("text_contract", constant.clone()).unwrap();
        assert!(contract.exactly_matches(&constant));
        assert!(contract.has_compatible_signature_and_resource_vocabulary(&constant));
        assert!(!contract.exactly_matches(&mutable));
        assert!(!contract.has_compatible_signature_and_resource_vocabulary(&mutable));
    }

    #[test]
    fn pointee_const_return_function_address_cannot_convert_to_mutable_callback() {
        let target = function(true);
        let parameter = c_parameter("callback", function(false).function_pointer_type());
        let environment = CExecutionEnvironment::new().with_function(target);
        let value = type_function_address_value(
            &CExpression::FunctionAddress("text".to_string()),
            CValue::typed_pointer(
                Pointer {
                    block: PointerBlock::Function("text".to_string()),
                    offset: PointerOffsetTerm::Constant(0),
                },
                CType::FunctionPointer(CallbackSignature::UNSPECIFIED),
            ),
            Some(&environment),
        );
        assert!(coerce_c_function_argument_without_obligations(&value, &parameter).is_none());
    }

    #[test]
    fn pointee_const_return_arguments_cannot_discard_const() {
        for constant in [false, true] {
            let parameter =
                c_parameter("text", CType::UInt8Pointer).with_pointee_constant(constant);
            assert_eq!(
                coerce_c_function_argument_without_obligations(&pointer(true), &parameter)
                    .is_some(),
                constant
            );
            let callee = CFunction::new(
                CType::Void,
                "consume",
                vec![parameter],
                c_return(c_int32_literal(0)),
            );
            assert_eq!(
                coerce_c_function_arguments(
                    &callee,
                    &[pointer(true)],
                    &[],
                    &PureFactContext::new()
                )
                .is_some(),
                constant
            );
        }
    }

    #[test]
    fn pointee_const_return_string_literal_storage_is_read_only_but_type_is_mutable() {
        let function = CFunction::new(
            CType::UInt8Pointer,
            "literal_source",
            Vec::new(),
            c_return(c_variable("literal")),
        )
        .with_string_literals(vec![CStringLiteral::new("literal", b"ok\0".to_vec())]);
        let state = initialize_c_function_globals(&CState::new(), &function);
        let paths = evaluate_c_expression_paths(
            &state,
            &c_variable("literal"),
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        let CExpressionOutcome::Value(value) = &paths[0].outcome else {
            panic!("literal must evaluate")
        };
        assert!(
            matches!(value, CValue::Pointer(pointer) if !pointer.pointee_constant()
            && state.memory.is_read_only_block(&pointer.block))
        );
        assert!(
            coerce_function_return_value(
                value.clone(),
                &function,
                &mut Vec::new(),
                &PureFactContext::new()
            )
            .is_some()
        );
    }
}
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

fn canonical_memory_range(range: CMemoryRange) -> CMemoryRange {
    let base = Pointer {
        block: range.base().block.clone(),
        offset: crate::kernel::eval::canonical_offset_term(&range.base().offset),
    };
    range.with_bounds(
        base,
        crate::kernel::eval::canonical_term(range.start()),
        crate::kernel::eval::canonical_term(range.end()),
    )
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
            if let Some(parameter) = modified_by_value_aggregate_parameter_with_current_ensure(
                &callee_state,
                &body_path.outcome,
                function,
            ) {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                        format!(
                            "by-value aggregate parameter `{parameter}` is modified, but a postcondition reads its current state"
                        ),
                    )),
                    facts,
                    obligations,
                });
                continue;
            }
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
            if let Some(parameter) = modified_by_value_aggregate_parameter_with_current_ensure(
                &callee_state,
                &body_path.outcome,
                function,
            ) {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                        format!(
                            "by-value aggregate parameter `{parameter}` is modified, but a postcondition reads its current state"
                        ),
                    )),
                    facts,
                    obligations,
                });
                continue;
            }
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
    if environment.selected_call_contract.is_some() {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                "step(Contract) requires a function-pointer call".to_string(),
            )),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    }
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
    // A header-provided `static inline` or `static __always_inline` body has
    // no Click contract to apply.
    // Its checked C body is the call-site semantics, including while the
    // surrounding function is being contract-certified. All other functions
    // retain the normal verified-rule boundary.
    if !function.has_inline_body() {
        match execution_semantics.calls {
            CCallSemantics::ExecuteBodies => {}
            CCallSemantics::ApplyVerifiedRules => {
                let Some(rule) = environment.get_verified_function_rule(function.name()) else {
                    let error = if function.opaque_contract_supported() {
                        CRuntimeError::MissingVerifiedFunctionRule(function.name().to_string())
                    } else {
                        CRuntimeError::UnsupportedOpaqueFunctionContract(
                            function.name().to_string(),
                        )
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
        if function.has_inline_body() {
            // An inline body is call-site code: it runs on the caller's own
            // resources and leaves the caller whatever it did not consume.
            // There is no contract boundary to transfer across.
            let callee_state = callee_state.with_resource_context(caller_state.resources().clone());
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
                let (outcome, obligations) = function_outcome_from_body(
                    caller_state,
                    function,
                    complete_void_fallthrough(function, body_path.outcome),
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
            continue;
        }
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
    execute_verified_function_templates(
        caller_state,
        &[&rule.function],
        None,
        None,
        arguments,
        assumptions,
        environment,
        budget,
    )
}

fn execute_verified_function_templates(
    caller_state: &CState,
    functions: &[&CFunction],
    selected_contract: Option<usize>,
    resource_application: Option<&ResourceCallApplication>,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    let function = functions[0];
    if functions.iter().enumerate().any(|(index, function)| {
        !(selected_contract == Some(index) && resource_application.is_some())
            && function
                .resource_requires()
                .iter()
                .chain(function.resource_ensures())
                .any(|resource| matches!(resource, CResourceSpec::Instance { .. }))
    }) {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                "calls with named resource instances require checked binder transport, which is not supported yet".into(),
            )),
            facts: vec![],
            obligations: vec![],
        }]);
    }
    budget.consume_function_call()?;
    let existing_variables = crate::instrumentation::measure_operation(
        function.name(),
        "verified function rule application",
        "verified call variable collection",
        || {
            let mut existing_variables = BTreeSet::new();
            collect_c_state_bitvector_variables(caller_state, &mut existing_variables);
            for function in functions {
                collect_c_function_bitvector_variables(function, &mut existing_variables);
            }
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
    'arguments: for arguments_path in evaluate_c_arguments_paths(
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

        let mut applicable = Vec::new();
        let mut first_failure = None;
        let mut selected_position = None;
        for (index, function) in functions.iter().enumerate() {
            let prepared = prepare_verified_function_call(
                caller_state,
                function,
                arguments_path.clone(),
                functions.len() > 1 || selected_contract.is_some(),
                assumptions,
                environment,
                budget,
                resource_application.filter(|_| selected_contract == Some(index)),
            )?;
            match prepared {
                Ok(prepared) => {
                    if selected_contract == Some(index) {
                        selected_position = Some(applicable.len());
                    }
                    applicable.push(prepared);
                }
                Err(failure) => {
                    if selected_contract == Some(index) {
                        paths.push(failure);
                        continue 'arguments;
                    }
                    if first_failure.is_none() {
                        first_failure = Some(failure);
                    }
                }
            }
        }
        if applicable.is_empty() {
            paths.push(first_failure.expect("a nonempty set of callback contracts"));
            continue;
        }
        // Pure conjunction does not duplicate an ownership ledger. An explicit
        // selector chooses one resource transition; absent that choice, do not
        // represent alternative ownership as paths or separating ownership.
        if selected_contract.is_none()
            && applicable.len() > 1
            && applicable.iter().any(|call| {
                !call.function.resource_requires.is_empty()
                    || !call.function.resource_ensures.is_empty()
                    || !call.function.resource_constructors.is_empty()
                    || !call.mutable_ranges.is_empty()
            })
        {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                    "ambiguous callback resource transition; use step(Contract) to select one"
                        .to_string(),
                )),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        }
        // Supplementary guarantees are interpreted on the shared post-memory,
        // not an alternative output ledger. In particular, resource counts must
        // not accidentally be evaluated against that interface's input ledger.
        let independent_guarantees_only = selected_contract.is_some()
            && applicable.iter().any(|call| {
                !call.function.resource_requires.is_empty()
                    || !call.function.resource_ensures.is_empty()
            });
        let primary = applicable.remove(selected_position.unwrap_or(0));
        let PreparedVerifiedFunctionCall {
            function,
            argument_values,
            entry_state,
            entry_contract_state,
            transfer,
            mut facts,
            obligations,
            effective_assumptions,
            mutable_ranges,
        } = primary;
        let additional_calls = applicable.into_iter();
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
        let result = symbolic_function_result(function, result_identity);
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
        // Returned ownership keeps its identity, not its old field values.
        // Only the ensures below relate fresh post-fields to the entry snapshot.
        for resource in function.resource_ensures() {
            let CResourceSpec::Instance { identity, .. } = resource else {
                continue;
            };
            let Some(before) = entry_contract_state.owned_resource_instance(*identity) else {
                return Ok(vec![resource_call_failure(
                    "returned resource parameter is not owned at call entry",
                )]);
            };
            let fields = before
                .schema()
                .fields()
                .iter()
                .map(|(_, ty)| {
                    variables.next = budget.next_kernel_variable;
                    let variable = variables.next();
                    budget.next_kernel_variable = variables.next;
                    match ty {
                        ResourceFieldType::C(ty) => {
                            AlgebraicValue::C(symbolic_call_result(*ty, variable))
                        }
                        ResourceFieldType::Algebraic(ty) => {
                            AlgebraicValue::Algebraic(AlgebraicTerm {
                                algebraic_type: ty.clone(),
                                node: AlgebraicTermNode::Variable(variable),
                            })
                        }
                    }
                })
                .collect();
            let after = ResourceInstance::new(
                before.identity,
                before.name.clone(),
                before.arguments.clone(),
                before.schema.clone(),
                fields,
            )
            .expect("fresh symbolic fields have their declared types");
            post_state.resources = match post_state
                .resources
                .clone()
                .try_compose_into_valid_context_delaying_normalization(
                    [CResourceFact::own(CResource::Instance(after))],
                    &effective_assumptions,
                ) {
                Ok(resources) => resources,
                Err(error) => {
                    return Ok(vec![CFunctionPath {
                        outcome: CFunctionOutcome::RuntimeError(resource_context_runtime_error(
                            error,
                        )),
                        facts,
                        obligations,
                    }]);
                }
            };
        }
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

        // The applicable interfaces share the result and post-call memory,
        // but bind their own argument names against the original entry state.
        for additional in additional_calls {
            let mut additional_facts = additional.facts;
            let entry_fact_count = additional_facts.len();
            let mut additional_post = additional
                .entry_state
                .clone()
                .with_memory(post_state.memory.clone());
            if additional.function.return_type() != CType::Void {
                set_function_result(&mut additional_post, additional.function, result.clone());
            }
            let additional_post = with_contract_argument_views(
                &additional_post,
                additional.function,
                &additional.argument_values,
            );
            add_verified_function_ensure_facts_selected(
                &mut additional_facts,
                &additional.obligations,
                &additional_post,
                &additional.entry_contract_state,
                additional.function,
                additional
                    .function
                    .contract_ensures()
                    .iter()
                    .filter(|ensure| {
                        !independent_guarantees_only
                            || spec_proposition_is_state_independent(ensure)
                            || spec_proposition_supports_stateful_memory_refinement(ensure)
                    }),
                &additional.effective_assumptions,
                budget,
            )?;
            facts.extend(additional_facts.into_iter().skip(entry_fact_count));
        }

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

struct PreparedVerifiedFunctionCall<'a> {
    function: &'a CFunction,
    argument_values: Vec<CValue>,
    entry_state: CState,
    entry_contract_state: CState,
    transfer: CFunctionResourceTransfer,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    effective_assumptions: PureFactContext,
    mutable_ranges: Vec<CMemoryRange>,
}

fn prepare_verified_function_call<'a>(
    caller_state: &CState,
    function: &'a CFunction,
    arguments_path: CArgumentsPath,
    require_established: bool,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
    resource_application: Option<&ResourceCallApplication>,
) -> ExecutionResult<Result<PreparedVerifiedFunctionCall<'a>, CFunctionPath>> {
    let initial_obligation_count = arguments_path.obligations.len();
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
        return Ok(Err(CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                "{}",
                argument_binding_error(function, &arguments_path.values)
            ))),
            facts: arguments_path.facts,
            obligations: arguments_path.obligations,
        }));
    };
    let Some(mut entry_state) = bind_c_function_arguments(caller_state, function, &argument_values)
    else {
        return Ok(Err(CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                "{}",
                argument_binding_error(function, &argument_values)
            ))),
            facts: arguments_path.facts,
            obligations: argument_obligations,
        }));
    };
    let path_assumptions =
        assumptions_with_path_context(assumptions, &arguments_path.facts, &argument_obligations);
    if let Some(application) = resource_application {
        entry_state.resource_bindings = Some(application.bindings.clone());
        for parameter in application.parameters.iter() {
            if let Err(error) =
                evaluate_function_resource_spec(&entry_state, parameter, &path_assumptions, budget)?
            {
                return Ok(Err(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts: arguments_path.facts,
                    obligations: argument_obligations,
                }));
            }
        }
    }
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
            return Ok(Err(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(error),
                facts: arguments_path.facts,
                obligations: argument_obligations,
            }));
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
            let contract_requirement_is_proven = function_contract_requirement_is_proven(
                &requirement_path.proposition,
                environment,
                budget,
            )?;
            let requirement_is_proven = super::assumptions::capture_implicit_reasoning_provenance(
                || {
                    if contract_requirement_is_proven {
                        return true;
                    }
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
                },
            );
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

    // Applicability is determined entirely at entry. In particular, pending
    // obligations must not be assumed to authorize this interface's effects
    // or make its guarantees available to another candidate.
    if require_established && obligations.len() != initial_obligation_count {
        return Ok(Err(CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                "no callback contract has established preconditions".to_string(),
            )),
            facts,
            obligations,
        }));
    }

    let effective_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
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
                // The call derivation and its effect summary share one
                // assumption-free canonical footprint. Proof-specific
                // vocabulary belongs in an explicit derived view, not in
                // the stored identity of the call.
                mutable_ranges.push(canonical_memory_range(
                    CMemoryRange::new_with_element_width(
                        segment.base,
                        segment.start,
                        segment.end,
                        element_width,
                    ),
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
        return Ok(Err(CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                "could not evaluate mutable footprint: {message}"
            ))),
            facts,
            obligations,
        }));
    }
    // A direct store into read-only storage is rejected where it is
    // executed, but a modular call performs its writes abstractly through
    // this footprint. Without the same check, passing read-only storage to
    // a callee that declares it mutable would let the call store there:
    // string-literal bytes are the reachable case, since C0 models a
    // literal as an ordinary `uint8*` and no qualifier catches it.
    if let Some(range) = mutable_ranges
        .iter()
        .find(|range| entry_state.memory.is_read_only_block(&range.base().block))
    {
        return Ok(Err(CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                "mutable footprint covers read-only storage `{}`",
                range.base().block
            ))),
            facts,
            obligations,
        }));
    }

    Ok(Ok(PreparedVerifiedFunctionCall {
        function,
        argument_values,
        entry_state,
        entry_contract_state,
        transfer,
        facts,
        obligations,
        effective_assumptions,
        mutable_ranges,
    }))
}

pub(super) fn execute_c_function_contracts_paths(
    caller_state: &CState,
    contracts: &[&CFunctionContract],
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    let selected = environment.selected_call_contract.as_deref();
    let contracts = contracts
        .iter()
        .copied()
        .filter(|contract| {
            contract.proof_parameters.is_empty() || selected == Some(contract.name())
        })
        .collect::<Vec<_>>();
    if contracts.is_empty() {
        return Ok(vec![resource_call_failure(
            "resource contract requires explicit proof arguments",
        )]);
    }
    let selected_index = selected.and_then(|name| {
        contracts
            .iter()
            .position(|contract| contract.name() == name)
    });
    if selected.is_some() && selected_index.is_none() {
        return Ok(vec![resource_call_failure(
            "selected contract is not available at this call",
        )]);
    }
    let resource_application = if let Some(index) = selected_index {
        let contract = contracts[index];
        let arguments = environment
            .selected_call_resource_arguments
            .as_deref()
            .unwrap_or(&[]);
        if arguments.len() != contract.proof_parameters.len() {
            return Ok(vec![resource_call_failure(
                "resource contract proof argument arity mismatch",
            )]);
        }
        let mut bindings = BTreeMap::new();
        let mut actuals = BTreeSet::new();
        for (parameter, argument) in contract.proof_parameters.iter().zip(arguments) {
            let CResourceSpec::Instance { identity, .. } = parameter else {
                return Ok(vec![resource_call_failure(
                    "resource proof parameter must be an exclusive instance",
                )]);
            };
            let Some(instance) = caller_state.owned_resource_instance(*argument) else {
                return Ok(vec![resource_call_failure(
                    "resource proof argument is not owned",
                )]);
            };
            if !actuals.insert(instance.identity())
                || bindings.insert(*identity, instance.identity()).is_some()
            {
                return Ok(vec![resource_call_failure(
                    "duplicate exclusive resource proof argument",
                )]);
            }
        }
        Some(ResourceCallApplication {
            parameters: contract.proof_parameters.clone(),
            bindings: std::sync::Arc::new(bindings),
        })
    } else {
        None
    };
    let functions = contracts
        .iter()
        .map(|contract| contract.template())
        .collect::<Vec<_>>();
    execute_verified_function_templates(
        caller_state,
        &functions,
        selected_index,
        resource_application.as_ref(),
        arguments,
        assumptions,
        environment,
        budget,
    )
}

struct ResourceCallApplication {
    parameters: std::sync::Arc<[CResourceSpec]>,
    bindings: std::sync::Arc<BTreeMap<Variable, Variable>>,
}

fn resource_call_failure(message: &str) -> CFunctionPath {
    CFunctionPath {
        outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(message.into())),
        facts: vec![],
        obligations: vec![],
    }
}

fn function_contract_requirement_is_proven(
    proposition: &Proposition,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    match proposition {
        Proposition::And(left, right) => {
            Ok(
                function_contract_requirement_is_proven(left, environment, budget)?
                    && function_contract_requirement_is_proven(right, environment, budget)?,
            )
        }
        Proposition::Predicate { name, arguments } => {
            let Some(contract_name) = CFunctionContract::surface_name_from_predicate(name) else {
                return Ok(false);
            };
            let [Term::CState(_), Term::CValue(CValue::Pointer(pointer))] = arguments.as_slice()
            else {
                return Ok(false);
            };
            let Pointer {
                block: PointerBlock::Function(target),
                offset: PointerOffsetTerm::Constant(0),
            } = pointer.pointer()
            else {
                return Ok(false);
            };
            let Some(contract) = environment.get_function_contract(contract_name) else {
                return Ok(false);
            };
            if pointer.c_type() != contract.function_pointer_type() {
                return Ok(false);
            }
            if let Some(rule) = environment.get_verified_function_rule(target) {
                return function_refines_named_contract(contract, &rule.function, budget);
            }
            let Some(rule) = environment.get_external_function_rule(target) else {
                return Ok(false);
            };
            function_refines_named_contract(contract, &rule.function, budget)
        }
        _ => Ok(false),
    }
}

/// Proves behavioral callback refinement. Exact matching remains the fast
/// path. The semantic path checks framed memory, abstract-token, and folded
/// composite resource transitions and effect containment, instantiates both
/// interfaces with the same symbolic arguments, then checks preconditions
/// contravariantly and postconditions covariantly. Concrete resource needs and
/// mutable ranges may be narrower than the named contract's upper bounds.
/// Stateful refinement is deliberately limited to memory propositions backed
/// by a nonempty resource transition and unguarded named mutable footprint.
fn function_refines_named_contract(
    contract: &CFunctionContract,
    function: &CFunction,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if contract.exactly_matches(function) {
        return Ok(true);
    }
    if !contract.has_same_predicate_unfoldings(function) {
        return Ok(false);
    }
    let Some(context) = prepare_function_contract_refinement_context(contract, function, budget)
    else {
        return Ok(false);
    };
    function_refines_named_contract_in_case(&context, &[], &BTreeSet::new(), false, budget)
}

pub(super) fn prepare_function_contract_refinement_context(
    contract: &CFunctionContract,
    function: &CFunction,
    budget: &mut ExecutionBudget,
) -> Option<CFunctionContractRefinementContext> {
    if !contract.has_compatible_signature_and_resource_vocabulary(function) {
        return None;
    }
    let mut argument_values = Vec::with_capacity(function.parameters().len());
    for parameter in function.parameters() {
        let variable = Variable(budget.next_kernel_variable);
        budget.next_kernel_variable = budget.next_kernel_variable.wrapping_add(1);
        argument_values.push(symbolic_call_result(parameter.c_type(), variable));
    }
    let result_variable = Variable(budget.next_kernel_variable);
    budget.next_kernel_variable = budget.next_kernel_variable.wrapping_add(1);
    Some(CFunctionContractRefinementContext {
        contract: contract.clone(),
        function: function.clone(),
        pointer: CPointerValue::new(
            Pointer {
                block: PointerBlock::Function(function.name().to_string()),
                offset: PointerOffsetTerm::Constant(0),
            },
            contract.function_pointer_type(),
        ),
        source_contract: None,
        argument_values,
        result_variable,
        next_kernel_variable: budget.next_kernel_variable,
    })
}

pub(super) fn function_contract_refinement_entry_state(
    context: &CFunctionContractRefinementContext,
) -> CState {
    with_contract_argument_views(
        &CState::new(),
        context.contract.template(),
        &context.argument_values,
    )
}

pub(super) fn prepare_contract_refinement_obligations(
    context: &CFunctionContractRefinementContext,
) -> Option<CFunctionContractRefinementObligations> {
    let target = context.contract.template();
    let source = &context.function;
    let mut budget = ExecutionBudget::default();
    budget.next_kernel_variable = context.next_kernel_variable;
    let entry = function_contract_refinement_entry_state(context);
    let source_entry =
        with_contract_argument_views(&CState::new(), source, &context.argument_values);
    let mut assumptions = PureFactContext::new();
    if !assume_contract_propositions(
        &entry,
        &entry,
        target.contract_requires(),
        &mut assumptions,
        &mut budget,
    )
    .ok()?
    {
        return None;
    }
    // A single conservative post memory covers every possible source write.
    // This does not enumerate guard combinations or assert that a guarded
    // write happened. Resource/effect containment is checked independently.
    let ranges =
        evaluate_contract_mutable_ranges(source, &source_entry, &assumptions, &mut budget, false)
            .ok()??;
    let memory = entry.memory().clone().with_call_memory_havoc(
        Variable(budget.next_kernel_variable),
        &ranges,
        &assumptions,
    );
    budget.next_kernel_variable += 1;
    let result = symbolic_call_result(source.return_type(), context.result_variable);
    let mut post = entry.clone().with_memory(memory.clone());
    let mut source_post = source_entry.clone().with_memory(memory);
    if source.return_type() != CType::Void {
        set_function_result(&mut post, target, result.clone());
        set_function_result(&mut source_post, source, result);
    }
    if !compatible_resource_and_effect_interfaces(
        target,
        source,
        &entry,
        &source_entry,
        &post,
        &source_post,
        &assumptions,
        &mut budget,
    )
    .ok()?
    {
        return None;
    }
    fn conjunction(items: Vec<Proposition>) -> Proposition {
        items
            .into_iter()
            .reduce(|a, b| Proposition::And(Box::new(a), Box::new(b)))
            .unwrap_or(Proposition::ConditionIs(
                ConditionTerm::Constant(true),
                true,
            ))
    }
    fn lower(
        function: &CFunction,
        specs: &[SpecProposition],
        state: &CState,
        entry: &CState,
        budget: &mut ExecutionBudget,
    ) -> Option<Proposition> {
        let definitions = function
            .predicate_unfoldings()
            .iter()
            .map(|definition| (definition.body(), definition.predicate()))
            .collect::<BTreeMap<_, _>>();
        let mut propositions = Vec::new();
        for spec in specs {
            let spec = definitions.get(spec).copied().unwrap_or(spec);
            let paths = lower_spec_proposition_at_state_with_loop_entry(
                state,
                spec,
                Some(entry),
                &PureFactContext::new(),
                budget,
            )
            .ok()?;
            let [path] = paths.as_slice() else {
                return None;
            };
            // Lowering facts name reads and other definitional intermediates;
            // they are not clauses of either callback contract. Both sides
            // use the same kernel load identities in these fixed memories.
            propositions.extend(
                path.obligations
                    .iter()
                    .map(|obligation| obligation.proposition().clone()),
            );
            propositions.push(path.proposition.clone());
        }
        Some(conjunction(propositions))
    }
    let target_requires = lower(
        target,
        target.contract_requires(),
        &entry,
        &entry,
        &mut budget,
    )?;
    let source_requires = lower(
        source,
        source.contract_requires(),
        &source_entry,
        &source_entry,
        &mut budget,
    )?;
    let source_ensures = lower(
        source,
        source.contract_ensures(),
        &source_post,
        &source_entry,
        &mut budget,
    )?;
    let target_ensures = lower(
        target,
        target.contract_ensures(),
        &post,
        &entry,
        &mut budget,
    )?;
    let proposition = Proposition::Implies(
        Box::new(target_requires),
        Box::new(Proposition::And(
            Box::new(source_requires),
            Box::new(Proposition::Implies(
                Box::new(source_ensures),
                Box::new(target_ensures),
            )),
        )),
    );
    Some(CFunctionContractRefinementObligations {
        entry,
        post,
        proposition,
    })
}

fn function_refines_named_contract_in_case(
    context: &CFunctionContractRefinementContext,
    case_assumptions: &[Proposition],
    unfolded_predicates: &BTreeSet<String>,
    explicit_case: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    let contract = &context.contract;
    let function = &context.function;
    if !predicate_interfaces_are_explicitly_compatible(
        contract.template(),
        function,
        unfolded_predicates,
    ) {
        return Ok(false);
    }
    let mut propositions = contract
        .template()
        .contract_requires()
        .iter()
        .chain(contract.template().contract_ensures())
        .chain(function.contract_requires())
        .chain(function.contract_ensures());
    let state_independent = propositions
        .clone()
        .all(spec_proposition_is_state_independent);
    let supported_syntax = propositions.all(spec_proposition_supports_stateful_memory_refinement);
    let supported_stateful_memory = !state_independent
        && !contract.template().resource_requires().is_empty()
        && !contract.template().resource_ensures().is_empty()
        && !contract.template().contract_mutable().is_empty()
        && supported_syntax;
    if !state_independent && !supported_stateful_memory {
        return Ok(false);
    }

    let contract_entry = with_contract_argument_views(
        &CState::new(),
        contract.template(),
        &context.argument_values,
    );
    let function_entry =
        with_contract_argument_views(&CState::new(), function, &context.argument_values);
    let mut preconditions = PureFactContext::new();
    if !assume_contract_propositions(
        &contract_entry,
        &contract_entry,
        contract.template().contract_requires(),
        &mut preconditions,
        budget,
    )? {
        return Ok(false);
    }
    preconditions = assumptions_with_propositions(&preconditions, case_assumptions);
    if !prove_contract_propositions(
        &function_entry,
        &function_entry,
        function.contract_requires(),
        &mut preconditions,
        budget,
        supported_stateful_memory,
    )? {
        return Ok(false);
    }

    let post_memory = if state_independent {
        contract_entry.memory().clone()
    } else {
        let memory_variable = Variable(budget.next_kernel_variable);
        budget.next_kernel_variable = budget.next_kernel_variable.wrapping_add(1);
        let mutable_ranges = if explicit_case {
            let Some(ranges) = evaluate_decided_contract_mutable_ranges(
                function,
                &function_entry,
                &preconditions,
                budget,
            )?
            else {
                return Ok(false);
            };
            ranges
        } else {
            let Some(ranges) = evaluate_contract_mutable_ranges(
                contract.template(),
                &contract_entry,
                &preconditions,
                budget,
                true,
            )?
            else {
                return Ok(false);
            };
            ranges
        };
        contract_entry.memory().clone().with_call_memory_havoc(
            memory_variable,
            &mutable_ranges,
            &preconditions,
        )
    };
    let result = symbolic_function_result(function, context.result_variable);
    let mut contract_post = contract_entry.clone().with_memory(post_memory.clone());
    let mut function_post = function_entry.clone().with_memory(post_memory);
    if function.return_type() != CType::Void {
        set_function_result(&mut contract_post, contract.template(), result.clone());
        set_function_result(&mut function_post, function, result);
    }
    if !compatible_resource_and_effect_interfaces(
        contract.template(),
        function,
        &contract_entry,
        &function_entry,
        &contract_post,
        &function_post,
        &preconditions,
        budget,
    )? {
        return Ok(false);
    }
    let mut postconditions = preconditions;
    if !assume_contract_propositions(
        &function_post,
        &function_entry,
        function.contract_ensures(),
        &mut postconditions,
        budget,
    )? {
        return Ok(false);
    }
    prove_contract_propositions(
        &contract_post,
        &contract_entry,
        contract.template().contract_ensures(),
        &mut postconditions,
        budget,
        supported_stateful_memory,
    )
}

/// Predicate bodies are stored as checked, normalized contract propositions,
/// while `predicate_unfoldings` retains their opaque surface identities. Equal
/// unfolding tables need no proof action. Every entry present on only one side
/// must otherwise have its predicate name explicitly opened by the proof.
fn predicate_interfaces_are_explicitly_compatible(
    contract: &CFunction,
    function: &CFunction,
    unfolded_predicates: &BTreeSet<String>,
) -> bool {
    let contract_unfoldings = contract
        .predicate_unfoldings()
        .iter()
        .collect::<BTreeSet<_>>();
    let function_unfoldings = function
        .predicate_unfoldings()
        .iter()
        .collect::<BTreeSet<_>>();
    let permitted = |unfolding: &CPredicateUnfolding| match unfolding.predicate() {
        SpecProposition::Predicate { name, .. } => unfolded_predicates.contains(name),
        _ => false,
    };
    contract_unfoldings
        .difference(&function_unfoldings)
        .chain(function_unfoldings.difference(&contract_unfoldings))
        .all(|unfolding| permitted(unfolding))
}

fn evaluate_contract_mutable_ranges(
    contract: &CFunction,
    entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    require_unguarded: bool,
) -> ExecutionResult<Option<Vec<CMemoryRange>>> {
    let mut ranges = Vec::with_capacity(contract.contract_mutable().len());
    for segment in contract.contract_mutable() {
        if require_unguarded && segment.guard().is_some() {
            return Ok(None);
        }
        let Some(range) = evaluate_contract_mutable_range(entry, segment, assumptions, budget)?
        else {
            return Ok(None);
        };
        ranges.push(range);
    }
    Ok(Some(ranges))
}

/// Evaluates exactly the concrete ranges active in one explicit proof case.
///
/// Unlike automatic refinement, this never branches over a guard. Every guard
/// must already be decided by the named preconditions and the proof's written
/// case assumptions. A false guard contributes no possible write; a true guard
/// contributes its ordinary evaluated range.
fn evaluate_decided_contract_mutable_ranges(
    function: &CFunction,
    entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<CMemoryRange>>> {
    let mut guard_assumptions = assumptions.clone();
    let Some(guards) =
        lower_refinement_mutable_guards(function, entry, &mut guard_assumptions, budget)?
    else {
        return Ok(None);
    };
    let mut ranges = Vec::with_capacity(function.contract_mutable().len());
    for (segment, guard) in function.contract_mutable().iter().zip(guards) {
        if let Some(guard) = guard {
            if guard_assumptions.proves(&Proposition::Not(Box::new(guard.clone()))) {
                continue;
            }
            if !guard_assumptions.proves(&guard) {
                return Ok(None);
            }
        }
        let Some(range) =
            evaluate_contract_mutable_range(entry, segment, &guard_assumptions, budget)?
        else {
            return Ok(None);
        };
        ranges.push(range);
    }
    Ok(Some(ranges))
}

fn evaluate_contract_mutable_range(
    entry: &CState,
    segment: &CMemorySegment,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<CMemoryRange>> {
    let segment =
        match evaluate_loop_effect_segment_with_facts(entry, segment, assumptions, budget)? {
            Ok((segment, _)) => segment,
            Err(_) => return Ok(None),
        };
    Ok(Some(canonical_memory_range(
        CMemoryRange::new_with_element_width(
            segment.base,
            segment.start,
            segment.end,
            segment.element_width,
        ),
    )))
}

fn compatible_resource_and_effect_interfaces(
    contract: &CFunction,
    function: &CFunction,
    contract_entry: &CState,
    function_entry: &CState,
    contract_post: &CState,
    function_post: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if !resource_transition_is_compatible(
        contract,
        function,
        contract_entry,
        function_entry,
        contract_post,
        function_post,
        assumptions,
        budget,
    )? {
        return Ok(false);
    }
    mutable_footprint_is_compatible(
        contract,
        function,
        contract_entry,
        function_entry,
        assumptions,
        budget,
    )
}

#[allow(clippy::too_many_arguments)]
fn resource_transition_is_compatible(
    contract: &CFunction,
    function: &CFunction,
    contract_entry: &CState,
    function_entry: &CState,
    contract_post: &CState,
    function_post: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if exact_resource_interfaces_match(
        contract,
        function,
        contract_entry,
        function_entry,
        contract_post,
        function_post,
        assumptions,
        budget,
    )? {
        return Ok(true);
    }
    framed_resource_transition_refines(
        contract,
        function,
        contract_entry,
        function_entry,
        contract_post,
        function_post,
        assumptions,
        budget,
    )
}

#[allow(clippy::too_many_arguments)]
fn exact_resource_interfaces_match(
    contract: &CFunction,
    function: &CFunction,
    contract_entry: &CState,
    function_entry: &CState,
    contract_post: &CState,
    function_post: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if contract.resource_requires().len() != function.resource_requires().len()
        || contract.resource_ensures().len() != function.resource_ensures().len()
    {
        return Ok(false);
    }
    for (contract_resource, function_resource) in contract
        .resource_requires()
        .iter()
        .zip(function.resource_requires())
    {
        let contract_resource = match evaluate_function_resource_spec(
            contract_entry,
            contract_resource,
            assumptions,
            budget,
        )? {
            Ok(resource) => resource,
            Err(_) => return Ok(false),
        };
        let function_resource = match evaluate_function_resource_spec(
            function_entry,
            function_resource,
            assumptions,
            budget,
        )? {
            Ok(resource) => resource,
            Err(_) => return Ok(false),
        };
        if contract_resource != function_resource {
            return Ok(false);
        }
    }
    for (contract_resource, function_resource) in contract
        .resource_ensures()
        .iter()
        .zip(function.resource_ensures())
    {
        let contract_resource = match evaluate_function_resource_spec(
            contract_post,
            contract_resource,
            assumptions,
            budget,
        )? {
            Ok(resource) => resource,
            Err(_) => return Ok(false),
        };
        let function_resource = match evaluate_function_resource_spec(
            function_post,
            function_resource,
            assumptions,
            budget,
        )? {
            Ok(resource) => resource,
            Err(_) => return Ok(false),
        };
        if contract_resource != function_resource {
            return Ok(false);
        }
    }
    Ok(true)
}

fn context_contains_only_refinable_resources(resources: &ResourceContext) -> bool {
    resources.facts().iter().all(|resource| {
        matches!(
            resource,
            CResourceFact::Own(CResource::Memory(_) | CResource::Instance(_), quantity)
                if quantity.as_const() == Some(1)
        ) || matches!(
            resource,
            CResourceFact::Own(CResource::Composite { .. } | CResource::Token { .. }, _)
        ) || matches!(
            resource,
            CResourceFact::View(
                CResource::Memory(_) | CResource::Composite { .. } | CResource::Token { .. }
            )
        )
    })
}

fn resource_spec_supports_framed_refinement(resource: &CResourceSpec) -> bool {
    match resource {
        CResourceSpec::Instance { .. } => false,
        CResourceSpec::OwnMemory(_)
        | CResourceSpec::ViewMemory(_)
        | CResourceSpec::Composite { .. }
        | CResourceSpec::Token { .. } => true,
        CResourceSpec::Quantified { resource, .. } => matches!(
            resource.as_ref(),
            CResourceSpec::Composite {
                access: CResourceAccessMode::Own,
                ..
            } | CResourceSpec::Token {
                access: CResourceAccessMode::Own,
                ..
            }
        ),
    }
}

fn evaluate_refinement_resource_context(
    state: &CState,
    resources: &[CResourceSpec],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<ResourceContext>> {
    Ok(
        match evaluate_function_resource_context(state, resources, assumptions, budget)? {
            Ok(resources) => Some(resources),
            Err(_) => None,
        },
    )
}

/// Checks that the named requirements can supply the concrete requirements,
/// preserving everything the concrete transition only borrows or does not
/// need as a frame. Then requires `concrete_ensures * frame` to provide the
/// named ensures. The resource context's indexed algebras perform ownership
/// splitting, symbolic exact-resource quantity arithmetic, range containment,
/// exact token and folded-composite identity, and scoped borrowing; no project
/// functions, composite definitions, or unrelated proof state are inspected.
#[allow(clippy::too_many_arguments)]
fn framed_resource_transition_refines(
    contract: &CFunction,
    function: &CFunction,
    contract_entry: &CState,
    function_entry: &CState,
    contract_post: &CState,
    function_post: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if !contract
        .resource_requires()
        .iter()
        .chain(contract.resource_ensures())
        .chain(function.resource_requires())
        .chain(function.resource_ensures())
        .all(resource_spec_supports_framed_refinement)
    {
        return Ok(false);
    }
    let Some(contract_requires) = evaluate_refinement_resource_context(
        contract_entry,
        contract.resource_requires(),
        assumptions,
        budget,
    )?
    else {
        return Ok(false);
    };
    let Some(function_requires) = evaluate_refinement_resource_context(
        function_entry,
        function.resource_requires(),
        assumptions,
        budget,
    )?
    else {
        return Ok(false);
    };
    let Some(function_ensures) = evaluate_refinement_resource_context(
        function_post,
        function.resource_ensures(),
        assumptions,
        budget,
    )?
    else {
        return Ok(false);
    };
    let Some(contract_ensures) = evaluate_refinement_resource_context(
        contract_post,
        contract.resource_ensures(),
        assumptions,
        budget,
    )?
    else {
        return Ok(false);
    };
    if [
        &contract_requires,
        &function_requires,
        &function_ensures,
        &contract_ensures,
    ]
    .into_iter()
    .any(|resources| !context_contains_only_refinable_resources(resources))
    {
        return Ok(false);
    }

    let Some(frame) = contract_requires
        .clone()
        .without_facts(function_requires.facts(), assumptions)
    else {
        return Ok(false);
    };
    let concrete_output = match frame.try_compose_with_facts_delaying_normalization(
        function_ensures.facts().iter().cloned(),
        assumptions,
    ) {
        Ok(resources) => resources,
        Err(_) => return Ok(false),
    };
    Ok(resource_context_definitionally_contains(
        &concrete_output,
        &contract_ensures,
        &[],
        contract_post.memory(),
        assumptions,
    ))
}

fn mutable_footprint_is_compatible(
    contract: &CFunction,
    function: &CFunction,
    contract_entry: &CState,
    function_entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if function.contract_mutable().is_empty() {
        return Ok(true);
    }
    let mut guard_assumptions = assumptions.clone();
    let Some(contract_guards) =
        lower_refinement_mutable_guards(contract, contract_entry, &mut guard_assumptions, budget)?
    else {
        return Ok(false);
    };
    let Some(function_guards) =
        lower_refinement_mutable_guards(function, function_entry, &mut guard_assumptions, budget)?
    else {
        return Ok(false);
    };

    for (required_segment, required_guard) in
        function.contract_mutable().iter().zip(&function_guards)
    {
        if required_guard.as_ref().is_some_and(|guard| {
            guard_assumptions.proves(&Proposition::Not(Box::new(guard.clone())))
        }) {
            continue;
        }
        let mut active_assumptions = guard_assumptions.clone();
        if let Some(guard) = required_guard {
            active_assumptions = active_assumptions.assume_proposition(guard.clone());
        }
        let Some(required_range) = evaluate_contract_mutable_range(
            function_entry,
            required_segment,
            &active_assumptions,
            budget,
        )?
        else {
            return Ok(false);
        };

        let mut covered = false;
        for (available_segment, available_guard) in
            contract.contract_mutable().iter().zip(&contract_guards)
        {
            if let Some(guard) = available_guard {
                if !active_assumptions.proves(guard) {
                    continue;
                }
            }
            let Some(available_range) = evaluate_contract_mutable_range(
                contract_entry,
                available_segment,
                &active_assumptions,
                budget,
            )?
            else {
                continue;
            };
            if memory_range_covers(&available_range, &required_range, &active_assumptions) {
                covered = true;
                break;
            }
        }
        if !covered {
            return Ok(false);
        }
    }

    Ok(true)
}

/// Lowers each load-free entry guard once. Facts produced while evaluating a
/// guard are unconditional after its obligations have been proved, so later
/// guards and range expressions may reuse them without searching unrelated
/// functions or proof state.
fn lower_refinement_mutable_guards(
    function: &CFunction,
    entry: &CState,
    assumptions: &mut PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<Option<Proposition>>>> {
    let mut guards = Vec::with_capacity(function.contract_mutable().len());
    for segment in function.contract_mutable() {
        let Some(guard) = segment.guard() else {
            guards.push(None);
            continue;
        };
        if !spec_proposition_is_state_independent(guard) {
            return Ok(None);
        }
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            entry,
            guard,
            Some(entry),
            assumptions,
            budget,
        )?;
        let [path] = paths.as_slice() else {
            return Ok(None);
        };
        for fact in &path.facts {
            *assumptions = assumptions
                .clone()
                .assume_proposition(fact.proposition().clone());
        }
        if path
            .obligations
            .iter()
            .any(|obligation| !assumptions.proves(obligation.proposition()))
        {
            return Ok(None);
        }
        guards.push(Some(path.proposition.clone()));
    }
    Ok(Some(guards))
}

#[cfg(test)]
mod guarded_mutable_refinement_tests {
    use super::*;

    fn guard(operator: CComparisonOperator, value: u32) -> SpecProposition {
        SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("active")),
            operator,
            right: SpecExpression::CExpression(c_int32_literal(value)),
        }
    }

    fn segment(guard: Option<SpecProposition>, start: u32, end: u32) -> CMemorySegment {
        let segment = CMemorySegment::new(
            c_variable("cells"),
            c_int32_literal(start),
            c_int32_literal(end),
        );
        match guard {
            Some(guard) => segment.with_guard(guard),
            None => segment,
        }
    }

    fn function_with_segment(name: &str, segment: CMemorySegment) -> CFunction {
        c_function(CType::Void, name, Vec::new(), c_return(c_void_value())).with_contract(
            Vec::new(),
            Vec::new(),
            vec![segment],
            Vec::new(),
            true,
        )
    }

    fn entry_state() -> CState {
        CState::new()
            .with_local(
                "active",
                int32(Bitvector32Term::Variable(Variable(980_001))),
            )
            .with_local(
                "cells",
                CValue::pointer(Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Constant(0),
                }),
            )
    }

    fn compatible_with_assumptions(
        contract: &CFunction,
        function: &CFunction,
        assumptions: &PureFactContext,
    ) -> bool {
        let entry = entry_state();
        mutable_footprint_is_compatible(
            contract,
            function,
            &entry,
            &entry,
            assumptions,
            &mut ExecutionBudget::new(),
        )
        .expect("guarded mutable refinement should execute")
    }

    fn compatible(contract: &CFunction, function: &CFunction) -> bool {
        compatible_with_assumptions(contract, function, &PureFactContext::new())
    }

    #[test]
    fn stronger_concrete_guard_and_subrange_refine_named_footprint() {
        let contract = function_with_segment(
            "contract",
            segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 2),
        );
        let function = function_with_segment(
            "function",
            segment(Some(guard(CComparisonOperator::Equal, 1)), 1, 2),
        );
        assert!(compatible(&contract, &function));
    }

    #[test]
    fn guarded_concrete_effect_refines_unguarded_named_footprint() {
        let contract = function_with_segment("contract", segment(None, 0, 2));
        let function = function_with_segment(
            "function",
            segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 1),
        );
        assert!(compatible(&contract, &function));
    }

    #[test]
    fn unguarded_concrete_effect_does_not_refine_guarded_named_footprint() {
        let contract = function_with_segment(
            "contract",
            segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 2),
        );
        let function = function_with_segment("function", segment(None, 0, 1));
        assert!(!compatible(&contract, &function));
    }

    #[test]
    fn named_precondition_can_establish_guard_for_unconditional_concrete_effect() {
        let contract = function_with_segment(
            "contract",
            segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 2),
        );
        let function = function_with_segment("function", segment(None, 0, 1));
        let active = Bitvector32Term::Variable(Variable(980_001));
        let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::equal(active, Bitvector32Term::Constant(0)),
            false,
        ));
        assert!(compatible_with_assumptions(
            &contract,
            &function,
            &assumptions,
        ));
    }

    #[test]
    fn unrelated_concrete_guard_does_not_refine_named_guard() {
        let contract = function_with_segment(
            "contract",
            segment(Some(guard(CComparisonOperator::GreaterThan, 0)), 0, 2),
        );
        let function = function_with_segment(
            "function",
            segment(Some(guard(CComparisonOperator::LessThan, 0)), 0, 1),
        );
        assert!(!compatible(&contract, &function));
    }

    #[test]
    fn guard_implication_does_not_relax_range_containment() {
        let contract = function_with_segment(
            "contract",
            segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 1),
        );
        let function = function_with_segment(
            "function",
            segment(Some(guard(CComparisonOperator::Equal, 1)), 0, 2),
        );
        assert!(!compatible(&contract, &function));
    }
}

fn assume_contract_propositions(
    state: &CState,
    entry_state: &CState,
    propositions: &[SpecProposition],
    assumptions: &mut PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    for proposition in propositions {
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            state,
            proposition,
            Some(entry_state),
            assumptions,
            budget,
        )?;
        let [path] = paths.as_slice() else {
            return Ok(false);
        };
        for fact in &path.facts {
            *assumptions = assumptions
                .clone()
                .assume_proposition(fact.proposition().clone());
        }
        for obligation in &path.obligations {
            *assumptions = assumptions
                .clone()
                .assume_proposition(obligation.proposition().clone());
        }
        assume_contract_proposition(assumptions, path.proposition.clone());
    }
    Ok(true)
}

/// Adds a contract proposition and the deterministic logical consequences
/// exposed by facts already present in this local refinement context.
fn assume_contract_proposition(assumptions: &mut PureFactContext, proposition: Proposition) {
    *assumptions = assumptions.clone().assume_proposition(proposition.clone());
    match proposition {
        Proposition::Equal(Term::Sequence(left), Term::Sequence(right)) => {
            // Linear decomposition of this explicitly selected premise.
            for (left, right) in
                super::spec::sequence_elements(&left).zip(super::spec::sequence_elements(&right))
            {
                if let Some(equality) = super::spec::integer_sequence_element_equality(left, right)
                {
                    *assumptions = assumptions.clone().assume_proposition(equality);
                }
            }
        }
        Proposition::And(left, right) => {
            assume_contract_proposition(assumptions, *left);
            assume_contract_proposition(assumptions, *right);
        }
        Proposition::Implies(left, right) if assumptions.proves(&left) => {
            assume_contract_proposition(assumptions, *right);
        }
        _ => {}
    }
}

fn prove_contract_propositions(
    state: &CState,
    entry_state: &CState,
    propositions: &[SpecProposition],
    assumptions: &mut PureFactContext,
    budget: &mut ExecutionBudget,
    allow_stateful_memory: bool,
) -> ExecutionResult<bool> {
    for proposition in propositions {
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            state,
            proposition,
            Some(entry_state),
            assumptions,
            budget,
        )?;
        let [path] = paths.as_slice() else {
            return Ok(false);
        };
        for fact in &path.facts {
            *assumptions = assumptions
                .clone()
                .assume_proposition(fact.proposition().clone());
        }
        if path
            .obligations
            .iter()
            .any(|obligation| !assumptions.proves(obligation.proposition()))
            || !contract_refinement_proves(assumptions, &path.proposition, allow_stateful_memory)
        {
            return Ok(false);
        }
        for obligation in &path.obligations {
            *assumptions = assumptions
                .clone()
                .assume_proposition(obligation.proposition().clone());
        }
        *assumptions = assumptions
            .clone()
            .assume_proposition(path.proposition.clone());
    }
    Ok(true)
}

fn contract_refinement_proves(
    assumptions: &PureFactContext,
    proposition: &Proposition,
    allow_stateful_memory: bool,
) -> bool {
    if assumptions.proves(proposition) {
        return true;
    }
    if !allow_stateful_memory {
        return false;
    }
    match proposition {
        Proposition::Equal(Term::Sequence(left), Term::Sequence(right)) => {
            let mut left = super::spec::sequence_elements(left);
            let mut right = super::spec::sequence_elements(right);
            loop {
                match (left.next(), right.next()) {
                    (Some(left), Some(right)) => {
                        let Some(equality) =
                            super::spec::integer_sequence_element_equality(left, right)
                        else {
                            return false;
                        };
                        if !contract_refinement_proves(assumptions, &equality, true) {
                            return false;
                        }
                    }
                    (None, None) => return true,
                    _ => return false,
                }
            }
        }
        Proposition::Or(left, right) => {
            return contract_refinement_proves(assumptions, left, true)
                || contract_refinement_proves(assumptions, right, true);
        }
        Proposition::And(left, right) => {
            return contract_refinement_proves(assumptions, left, true)
                && contract_refinement_proves(assumptions, right, true);
        }
        Proposition::Implies(left, right) => {
            if assumptions.proves(&Proposition::Not(left.clone())) {
                return true;
            }
            let assumptions = assumptions
                .clone()
                .assume_proposition(left.as_ref().clone());
            return contract_refinement_proves(&assumptions, right, true);
        }
        _ => {}
    }
    let Proposition::ConditionIs(condition, value) = proposition else {
        return false;
    };
    let (left, right, rebuild): (
        &Bitvector32Term,
        &Bitvector32Term,
        fn(Bitvector32Term, Bitvector32Term) -> ConditionTerm,
    ) = match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            (left, right, ConditionTerm::signed_less_than)
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            (left, right, ConditionTerm::signed_less_equal)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            (left, right, ConditionTerm::signed_greater_than)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            (left, right, ConditionTerm::signed_greater_equal)
        }
        ConditionTerm::Bitvector32Equal(left, right) => (left, right, ConditionTerm::equal),
        _ => return false,
    };
    assumptions
        .recorded_equality_class(left)
        .into_iter()
        .any(|equal| {
            assumptions.proves(&Proposition::ConditionIs(
                rebuild(equal, right.clone()),
                *value,
            ))
        })
        || assumptions
            .recorded_equality_class(right)
            .into_iter()
            .any(|equal| {
                assumptions.proves(&Proposition::ConditionIs(
                    rebuild(left.clone(), equal),
                    *value,
                ))
            })
}

fn spec_proposition_is_state_independent(proposition: &SpecProposition) -> bool {
    match proposition {
        SpecProposition::Comparison { left, right, .. } => {
            spec_expression_is_state_independent(left)
                && spec_expression_is_state_independent(right)
        }
        SpecProposition::FloatClassification { expression, .. }
        | SpecProposition::Defined(expression) => spec_expression_is_state_independent(expression),
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            spec_proposition_is_state_independent(left)
                && spec_proposition_is_state_independent(right)
        }
        SpecProposition::Not(body)
        | SpecProposition::ForAllInt32 { body, .. }
        | SpecProposition::ForAllPointer { body, .. }
        | SpecProposition::ExistsInt32 { body, .. }
        | SpecProposition::ExistsPointer { body, .. } => {
            spec_proposition_is_state_independent(body)
        }
        _ => false,
    }
}

/// The first stateful refinement slice admits ordinary scalar propositions
/// whose only stateful operation is a C memory access (possibly below
/// `old`), including finite sequence comparisons and membership. Resource
/// relations, algebraic values, and explicit memory snapshots remain outside
/// this rule. The caller separately checks resource and footprint refinement.
fn spec_proposition_supports_stateful_memory_refinement(proposition: &SpecProposition) -> bool {
    match proposition {
        SpecProposition::SequenceComparison { left, right, .. } => {
            spec_sequence_supports_stateful_memory_refinement(left)
                && spec_sequence_supports_stateful_memory_refinement(right)
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            spec_expression_supports_stateful_memory_refinement(element)
                && spec_sequence_supports_stateful_memory_refinement(sequence)
        }
        SpecProposition::Comparison { left, right, .. } => {
            spec_expression_supports_stateful_memory_refinement(left)
                && spec_expression_supports_stateful_memory_refinement(right)
        }
        SpecProposition::FloatClassification { expression, .. }
        | SpecProposition::Defined(expression) => {
            spec_expression_supports_stateful_memory_refinement(expression)
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            spec_proposition_supports_stateful_memory_refinement(left)
                && spec_proposition_supports_stateful_memory_refinement(right)
        }
        SpecProposition::Not(body)
        | SpecProposition::ForAllInt32 { body, .. }
        | SpecProposition::ForAllPointer { body, .. }
        | SpecProposition::ExistsInt32 { body, .. }
        | SpecProposition::ExistsPointer { body, .. } => {
            spec_proposition_supports_stateful_memory_refinement(body)
        }
        _ => false,
    }
}

fn spec_sequence_supports_stateful_memory_refinement(sequence: &SpecSequenceExpression) -> bool {
    match sequence {
        SpecSequenceExpression::Literal(elements) => elements
            .iter()
            .all(spec_expression_supports_stateful_memory_refinement),
        SpecSequenceExpression::Concat(left, right) => {
            spec_sequence_supports_stateful_memory_refinement(left)
                && spec_sequence_supports_stateful_memory_refinement(right)
        }
    }
}

fn spec_expression_supports_stateful_memory_refinement(expression: &SpecExpression) -> bool {
    match expression {
        SpecExpression::ResourceField { .. } => false,
        SpecExpression::Value(_) => true,
        SpecExpression::CExpression(expression) => {
            c_expression_supports_stateful_memory_refinement(expression)
        }
        SpecExpression::Add(left, right)
        | SpecExpression::Subtract(left, right)
        | SpecExpression::Multiply(left, right)
        | SpecExpression::Divide(left, right)
        | SpecExpression::Remainder(left, right)
        | SpecExpression::ShiftLeft(left, right)
        | SpecExpression::ShiftRight(left, right)
        | SpecExpression::BitwiseAnd(left, right)
        | SpecExpression::BitwiseOr(left, right)
        | SpecExpression::BitwiseXor(left, right) => {
            spec_expression_supports_stateful_memory_refinement(left)
                && spec_expression_supports_stateful_memory_refinement(right)
        }
        SpecExpression::BitwiseNot(body) | SpecExpression::Cast(body, _) => {
            spec_expression_supports_stateful_memory_refinement(body)
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            spec_proposition_supports_stateful_memory_refinement(condition)
                && spec_expression_supports_stateful_memory_refinement(then_branch)
                && spec_expression_supports_stateful_memory_refinement(else_branch)
        }
        SpecExpression::Let { value, body, .. } => {
            spec_expression_supports_stateful_memory_refinement(value)
                && spec_expression_supports_stateful_memory_refinement(body)
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => arguments
            .iter()
            .all(spec_pure_function_argument_supports_stateful_memory_refinement),
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => {
            spec_expression_supports_stateful_memory_refinement(pointer)
                && spec_expression_supports_stateful_memory_refinement(elements)
        }
        SpecExpression::MemoryLoad {
            memory: SpecMemory::Current | SpecMemory::FunctionEntry,
            pointer,
            ..
        } => spec_expression_supports_stateful_memory_refinement(pointer),
        SpecExpression::AlgebraicMatch { .. }
        | SpecExpression::CountedResourceCount { .. }
        | SpecExpression::RangeFold { .. }
        | SpecExpression::LoopEntrySnapshot(_)
        | SpecExpression::MemoryLoad { .. } => false,
    }
}

fn spec_pure_function_argument_supports_stateful_memory_refinement(
    argument: &SpecPureFunctionArgument,
) -> bool {
    match argument {
        SpecPureFunctionArgument::Value(expression) => {
            spec_expression_supports_stateful_memory_refinement(expression)
        }
        // The refinement rule deliberately excludes algebraic values and
        // array snapshots until their stateful refinement laws are explicit.
        SpecPureFunctionArgument::Algebraic(_) | SpecPureFunctionArgument::ArrayRef { .. } => false,
    }
}

fn c_expression_supports_stateful_memory_refinement(expression: &CExpression) -> bool {
    match expression {
        CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => true,
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::AddressOf(expression)
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::BitwiseNot(expression)
        | CExpression::Load(expression) => {
            c_expression_supports_stateful_memory_refinement(expression)
        }
        CExpression::TypedLoad { pointer, .. } => {
            c_expression_supports_stateful_memory_refinement(pointer)
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_supports_stateful_memory_refinement(condition)
                && c_expression_supports_stateful_memory_refinement(then_branch)
                && c_expression_supports_stateful_memory_refinement(else_branch)
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
            c_expression_supports_stateful_memory_refinement(left)
                && c_expression_supports_stateful_memory_refinement(right)
        }
    }
}

fn spec_expression_is_state_independent(expression: &SpecExpression) -> bool {
    match expression {
        SpecExpression::Value(_) => true,
        SpecExpression::CExpression(expression) => c_expression_is_state_independent(expression),
        SpecExpression::Add(left, right)
        | SpecExpression::Subtract(left, right)
        | SpecExpression::Multiply(left, right)
        | SpecExpression::Divide(left, right)
        | SpecExpression::Remainder(left, right)
        | SpecExpression::ShiftLeft(left, right)
        | SpecExpression::ShiftRight(left, right)
        | SpecExpression::BitwiseAnd(left, right)
        | SpecExpression::BitwiseOr(left, right)
        | SpecExpression::BitwiseXor(left, right) => {
            spec_expression_is_state_independent(left)
                && spec_expression_is_state_independent(right)
        }
        SpecExpression::BitwiseNot(body)
        | SpecExpression::LoopEntrySnapshot(body)
        | SpecExpression::Cast(body, _) => spec_expression_is_state_independent(body),
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            spec_proposition_is_state_independent(condition)
                && spec_expression_is_state_independent(then_branch)
                && spec_expression_is_state_independent(else_branch)
        }
        SpecExpression::Let { value, body, .. } => {
            spec_expression_is_state_independent(value)
                && spec_expression_is_state_independent(body)
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => arguments
            .iter()
            .all(spec_pure_function_argument_is_state_independent),
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => {
            spec_expression_is_state_independent(pointer)
                && spec_expression_is_state_independent(elements)
        }
        _ => false,
    }
}

fn spec_pure_function_argument_is_state_independent(argument: &SpecPureFunctionArgument) -> bool {
    match argument {
        SpecPureFunctionArgument::Value(expression) => {
            spec_expression_is_state_independent(expression)
        }
        SpecPureFunctionArgument::Algebraic(expression) => {
            spec_algebraic_expression_is_state_independent(expression)
        }
        SpecPureFunctionArgument::ArrayRef { .. } => false,
    }
}

pub(super) fn spec_algebraic_expression_is_state_independent(
    expression: &SpecAlgebraicExpression,
) -> bool {
    match &expression.node {
        SpecAlgebraicExpressionNode::ResourceField(_) => false,
        SpecAlgebraicExpressionNode::Variable(_) | SpecAlgebraicExpressionNode::Binding(_) => true,
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            fields.iter().all(|field| match field {
                SpecAlgebraicValue::C(expression) => {
                    spec_expression_is_state_independent(expression)
                }
                SpecAlgebraicValue::Algebraic(expression) => {
                    spec_algebraic_expression_is_state_independent(expression)
                }
            })
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            spec_algebraic_expression_is_state_independent(scrutinee)
                && arms
                    .iter()
                    .all(|arm| spec_algebraic_expression_is_state_independent(&arm.body))
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => arguments
            .iter()
            .all(spec_pure_function_argument_is_state_independent),
    }
}

fn c_expression_is_state_independent(expression: &CExpression) -> bool {
    match expression {
        CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => true,
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::BitwiseNot(expression) => c_expression_is_state_independent(expression),
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_is_state_independent(condition)
                && c_expression_is_state_independent(then_branch)
                && c_expression_is_state_independent(else_branch)
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
        | CExpression::BitwiseXor(left, right) => {
            c_expression_is_state_independent(left) && c_expression_is_state_independent(right)
        }
        CExpression::AddressOf(_)
        | CExpression::Load(_)
        | CExpression::TypedLoad { .. }
        | CExpression::Index(_, _) => false,
    }
}

/// Whether a specification expression reads a by-value aggregate parameter
/// from the current callee state. Entry-state reads (`old(...)`) use
/// `SpecMemory::FunctionEntry` and are intentionally ignored: they describe
/// the caller's argument image, which is stable across the call.
fn spec_expression_reads_current_parameter(
    expression: &SpecExpression,
    parameter_name: &str,
) -> bool {
    match expression {
        SpecExpression::Value(_) | SpecExpression::ResourceField { .. } => false,
        SpecExpression::CExpression(expression) => {
            c_expression_mentions_variable(expression, parameter_name)
        }
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            spec_algebraic_expression_reads_current_parameter(scrutinee, parameter_name)
                || arms
                    .iter()
                    .any(|arm| spec_expression_reads_current_parameter(&arm.body, parameter_name))
        }
        SpecExpression::CountedResourceCount { arguments, .. } => arguments
            .iter()
            .flatten()
            .any(|argument| spec_expression_reads_current_parameter(argument, parameter_name)),
        SpecExpression::Add(left, right)
        | SpecExpression::Subtract(left, right)
        | SpecExpression::Multiply(left, right)
        | SpecExpression::Divide(left, right)
        | SpecExpression::Remainder(left, right)
        | SpecExpression::ShiftLeft(left, right)
        | SpecExpression::ShiftRight(left, right)
        | SpecExpression::BitwiseAnd(left, right)
        | SpecExpression::BitwiseOr(left, right)
        | SpecExpression::BitwiseXor(left, right) => {
            spec_expression_reads_current_parameter(left, parameter_name)
                || spec_expression_reads_current_parameter(right, parameter_name)
        }
        SpecExpression::BitwiseNot(body)
        | SpecExpression::Cast(body, _)
        | SpecExpression::LoopEntrySnapshot(body) => {
            spec_expression_reads_current_parameter(body, parameter_name)
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            spec_proposition_reads_current_parameter(condition, parameter_name)
                || spec_expression_reads_current_parameter(then_branch, parameter_name)
                || spec_expression_reads_current_parameter(else_branch, parameter_name)
        }
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            spec_expression_reads_current_parameter(start, parameter_name)
                || spec_expression_reads_current_parameter(end, parameter_name)
                || spec_expression_reads_current_parameter(initial, parameter_name)
                || spec_expression_reads_current_parameter(body, parameter_name)
        }
        SpecExpression::Let { value, body, .. } => {
            spec_expression_reads_current_parameter(value, parameter_name)
                || spec_expression_reads_current_parameter(body, parameter_name)
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => {
            arguments.iter().any(|argument| {
                spec_pure_function_argument_reads_current_parameter(argument, parameter_name)
            })
        }
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => {
            spec_expression_reads_current_parameter(pointer, parameter_name)
                || spec_expression_reads_current_parameter(elements, parameter_name)
        }
        SpecExpression::MemoryLoad {
            memory: SpecMemory::FunctionEntry | SpecMemory::Fixed(_),
            ..
        } => false,
        SpecExpression::MemoryLoad { pointer, .. } => {
            spec_expression_reads_current_parameter(pointer, parameter_name)
        }
    }
}

fn spec_proposition_reads_current_parameter(
    proposition: &SpecProposition,
    parameter_name: &str,
) -> bool {
    match proposition {
        SpecProposition::AlgebraicComparison { left, right, .. } => {
            spec_algebraic_expression_reads_current_parameter(left, parameter_name)
                || spec_algebraic_expression_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            spec_expression_reads_current_parameter(element, parameter_name)
                || spec_sequence_reads_current_parameter(sequence, parameter_name)
        }
        SpecProposition::SequenceComparison { left, right, .. } => {
            spec_sequence_reads_current_parameter(left, parameter_name)
                || spec_sequence_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::Comparison { left, right, .. } => {
            spec_expression_reads_current_parameter(left, parameter_name)
                || spec_expression_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::FloatClassification { expression, .. }
        | SpecProposition::Defined(expression) => {
            spec_expression_reads_current_parameter(expression, parameter_name)
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            spec_proposition_reads_current_parameter(left, parameter_name)
                || spec_proposition_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::Not(body)
        | SpecProposition::ForAllInt32 { body, .. }
        | SpecProposition::ForAllPointer { body, .. }
        | SpecProposition::ExistsInt32 { body, .. }
        | SpecProposition::ExistsPointer { body, .. } => {
            spec_proposition_reads_current_parameter(body, parameter_name)
        }
        SpecProposition::Predicate { arguments, .. } => {
            arguments.iter().any(|argument| match argument {
                SpecPredicateArgument::Value(expression) => {
                    spec_expression_reads_current_parameter(expression, parameter_name)
                }
                SpecPredicateArgument::ArrayRef { memory, pointer } => {
                    !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                        && spec_expression_reads_current_parameter(pointer, parameter_name)
                }
            })
        }
        SpecProposition::ResourceSeparate { left, right }
        | SpecProposition::ResourceContains {
            parent: left,
            child: right,
        } => {
            spec_resource_reads_current_parameter(left, parameter_name)
                || spec_resource_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            ..
        } => {
            !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                && (spec_expression_reads_current_parameter(base, parameter_name)
                    || spec_expression_reads_current_parameter(start, parameter_name)
                    || spec_expression_reads_current_parameter(end, parameter_name))
        }
    }
}

fn spec_sequence_reads_current_parameter(
    sequence: &SpecSequenceExpression,
    parameter_name: &str,
) -> bool {
    match sequence {
        SpecSequenceExpression::Literal(elements) => elements
            .iter()
            .any(|element| spec_expression_reads_current_parameter(element, parameter_name)),
        SpecSequenceExpression::Concat(left, right) => {
            spec_sequence_reads_current_parameter(left, parameter_name)
                || spec_sequence_reads_current_parameter(right, parameter_name)
        }
    }
}

fn spec_resource_reads_current_parameter(resource: &SpecResource, parameter_name: &str) -> bool {
    match resource {
        SpecResource::Memory {
            base, start, end, ..
        } => {
            spec_expression_reads_current_parameter(base, parameter_name)
                || spec_expression_reads_current_parameter(start, parameter_name)
                || spec_expression_reads_current_parameter(end, parameter_name)
        }
        SpecResource::Composite { arguments, .. } | SpecResource::Token { arguments, .. } => {
            arguments
                .iter()
                .any(|argument| spec_expression_reads_current_parameter(argument, parameter_name))
        }
    }
}

fn spec_algebraic_expression_reads_current_parameter(
    expression: &SpecAlgebraicExpression,
    parameter_name: &str,
) -> bool {
    match &expression.node {
        SpecAlgebraicExpressionNode::Variable(_)
        | SpecAlgebraicExpressionNode::Binding(_)
        | SpecAlgebraicExpressionNode::ResourceField(_) => false,
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            fields.iter().any(|field| match field {
                SpecAlgebraicValue::C(expression) => {
                    spec_expression_reads_current_parameter(expression, parameter_name)
                }
                SpecAlgebraicValue::Algebraic(expression) => {
                    spec_algebraic_expression_reads_current_parameter(expression, parameter_name)
                }
            })
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            spec_algebraic_expression_reads_current_parameter(scrutinee, parameter_name)
                || arms.iter().any(|arm| {
                    spec_algebraic_expression_reads_current_parameter(&arm.body, parameter_name)
                })
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
            arguments.iter().any(|argument| {
                spec_pure_function_argument_reads_current_parameter(argument, parameter_name)
            })
        }
    }
}

fn spec_pure_function_argument_reads_current_parameter(
    argument: &SpecPureFunctionArgument,
    parameter_name: &str,
) -> bool {
    match argument {
        SpecPureFunctionArgument::Value(expression) => {
            spec_expression_reads_current_parameter(expression, parameter_name)
        }
        SpecPureFunctionArgument::Algebraic(expression) => {
            spec_algebraic_expression_reads_current_parameter(expression, parameter_name)
        }
        SpecPureFunctionArgument::ArrayRef {
            memory, pointer, ..
        } => {
            !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                && spec_expression_reads_current_parameter(pointer, parameter_name)
        }
    }
}

fn c_expression_mentions_variable(expression: &CExpression, name: &str) -> bool {
    match expression {
        CExpression::Variable(variable) => variable == name,
        CExpression::Value(_) | CExpression::FunctionAddress(_) => false,
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::AddressOf(expression)
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::Load(expression)
        | CExpression::TypedLoad {
            pointer: expression,
            ..
        }
        | CExpression::BitwiseNot(expression) => c_expression_mentions_variable(expression, name),
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_mentions_variable(condition, name)
                || c_expression_mentions_variable(then_branch, name)
                || c_expression_mentions_variable(else_branch, name)
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
            c_expression_mentions_variable(left, name)
                || c_expression_mentions_variable(right, name)
        }
    }
}

fn c_expression_takes_address_of_variable(expression: &CExpression, name: &str) -> bool {
    match expression {
        CExpression::AddressOf(expression) => c_expression_mentions_variable(expression, name),
        CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => false,
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::Load(expression)
        | CExpression::TypedLoad {
            pointer: expression,
            ..
        }
        | CExpression::BitwiseNot(expression) => {
            c_expression_takes_address_of_variable(expression, name)
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_takes_address_of_variable(condition, name)
                || c_expression_takes_address_of_variable(then_branch, name)
                || c_expression_takes_address_of_variable(else_branch, name)
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
            c_expression_takes_address_of_variable(left, name)
                || c_expression_takes_address_of_variable(right, name)
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ParameterAccessRange {
    start: u32,
    end: u32,
}

fn parameter_access_range(start: u32, width: u32) -> Option<ParameterAccessRange> {
    (width > 0).then_some(())?;
    Some(ParameterAccessRange {
        start,
        end: start.checked_add(width)?,
    })
}

impl ParameterAccessRange {
    fn overlaps(self, other: Self) -> bool {
        self.start < other.end && other.start < self.end
    }
}

fn c_expression_parameter_offset(expression: &CExpression, parameter_name: &str) -> Option<u32> {
    match expression {
        CExpression::Variable(variable) if variable == parameter_name => Some(0),
        CExpression::PointerOffsetBytes { pointer, bytes } => {
            c_expression_parameter_offset(pointer, parameter_name)?.checked_add(*bytes)
        }
        CExpression::Cast { expression, .. } => {
            c_expression_parameter_offset(expression, parameter_name)
        }
        _ => None,
    }
}

fn spec_expression_constant(expression: &SpecExpression) -> Option<u32> {
    let SpecExpression::Value(value) = expression else {
        return None;
    };
    match value {
        CValue::Int16(term)
        | CValue::Int32(term)
        | CValue::UInt8(term)
        | CValue::UInt16(term)
        | CValue::UInt32(term)
        | CValue::Int64(term)
        | CValue::UInt64(term) => term.as_const(),
        CValue::Void | CValue::Float32(_) | CValue::Float64(_) | CValue::Pointer(_) => None,
    }
}

fn spec_expression_parameter_offset(
    expression: &SpecExpression,
    parameter_name: &str,
) -> Option<u32> {
    match expression {
        SpecExpression::CExpression(expression) => {
            c_expression_parameter_offset(expression, parameter_name)
        }
        SpecExpression::Cast(expression, _) | SpecExpression::LoopEntrySnapshot(expression) => {
            spec_expression_parameter_offset(expression, parameter_name)
        }
        SpecExpression::PointerOffset {
            pointer,
            elements,
            byte_width,
        } => spec_expression_parameter_offset(pointer, parameter_name)?
            .checked_add(spec_expression_constant(elements)?.checked_mul(*byte_width)?),
        _ => None,
    }
}

fn statement_writes_aggregate_parameter(
    statement: &CStatement,
    parameter_name: &str,
    writes: &mut Vec<ParameterAccessRange>,
    unknown_write: &mut bool,
) {
    match statement {
        CStatement::Store { pointer, .. } => {
            if c_expression_parameter_offset(pointer, parameter_name).is_some() {
                *unknown_write = true;
            } else if c_expression_mentions_variable(pointer, parameter_name) {
                *unknown_write = true;
            }
        }
        CStatement::TypedStore {
            pointer,
            value_type,
            ..
        } => {
            if let Some(offset) = c_expression_parameter_offset(pointer, parameter_name) {
                if let Some(range) = parameter_access_range(offset, value_type.byte_width()) {
                    writes.push(range);
                }
            } else if c_expression_mentions_variable(pointer, parameter_name) {
                *unknown_write = true;
            }
        }
        CStatement::CopyAggregate { target, layout, .. } => {
            if let Some(offset) = c_expression_parameter_offset(target, parameter_name) {
                if let Some(range) = parameter_access_range(offset, layout.size_bytes()) {
                    writes.push(range);
                }
            } else if c_expression_mentions_variable(target, parameter_name) {
                *unknown_write = true;
            }
        }
        CStatement::Update { target, .. } => {
            if c_expression_mentions_variable(target, parameter_name) {
                *unknown_write = true;
            }
        }
        CStatement::Call { arguments, .. } | CStatement::CallAssign { arguments, .. } => {
            if arguments
                .iter()
                .any(|argument| c_expression_takes_address_of_variable(argument, parameter_name))
            {
                *unknown_write = true;
            }
        }
        CStatement::Seq(first, second) => {
            statement_writes_aggregate_parameter(first, parameter_name, writes, unknown_write);
            statement_writes_aggregate_parameter(second, parameter_name, writes, unknown_write);
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            statement_writes_aggregate_parameter(
                then_branch,
                parameter_name,
                writes,
                unknown_write,
            );
            statement_writes_aggregate_parameter(
                else_branch,
                parameter_name,
                writes,
                unknown_write,
            );
        }
        CStatement::ContinueWithStep { step } => {
            statement_writes_aggregate_parameter(step, parameter_name, writes, unknown_write);
        }
        CStatement::While { body, .. } => {
            statement_writes_aggregate_parameter(body, parameter_name, writes, unknown_write);
        }
        CStatement::Switch { cases, .. } => {
            for case in cases {
                statement_writes_aggregate_parameter(
                    &case.body,
                    parameter_name,
                    writes,
                    unknown_write,
                );
            }
        }
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assign { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_) => {}
    }
}

fn spec_expression_current_parameter_accesses(
    expression: &SpecExpression,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match expression {
        SpecExpression::Value(_) | SpecExpression::ResourceField { .. } => {}
        SpecExpression::CExpression(expression) => {
            if c_expression_mentions_variable(expression, parameter_name) {
                *unknown_read = true;
            }
        }
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            spec_algebraic_expression_current_parameter_accesses(
                scrutinee,
                parameter_name,
                reads,
                unknown_read,
            );
            for arm in arms {
                spec_expression_current_parameter_accesses(
                    &arm.body,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
        SpecExpression::CountedResourceCount { arguments, .. } => {
            for argument in arguments.iter().flatten() {
                spec_expression_current_parameter_accesses(
                    argument,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
        SpecExpression::Add(left, right)
        | SpecExpression::Subtract(left, right)
        | SpecExpression::Multiply(left, right)
        | SpecExpression::Divide(left, right)
        | SpecExpression::Remainder(left, right)
        | SpecExpression::ShiftLeft(left, right)
        | SpecExpression::ShiftRight(left, right)
        | SpecExpression::BitwiseAnd(left, right)
        | SpecExpression::BitwiseOr(left, right)
        | SpecExpression::BitwiseXor(left, right) => {
            spec_expression_current_parameter_accesses(left, parameter_name, reads, unknown_read);
            spec_expression_current_parameter_accesses(right, parameter_name, reads, unknown_read);
        }
        SpecExpression::BitwiseNot(body)
        | SpecExpression::Cast(body, _)
        | SpecExpression::LoopEntrySnapshot(body) => {
            spec_expression_current_parameter_accesses(body, parameter_name, reads, unknown_read);
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            spec_proposition_current_parameter_accesses(
                condition,
                parameter_name,
                reads,
                unknown_read,
            );
            spec_expression_current_parameter_accesses(
                then_branch,
                parameter_name,
                reads,
                unknown_read,
            );
            spec_expression_current_parameter_accesses(
                else_branch,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            spec_expression_current_parameter_accesses(start, parameter_name, reads, unknown_read);
            spec_expression_current_parameter_accesses(end, parameter_name, reads, unknown_read);
            spec_expression_current_parameter_accesses(
                initial,
                parameter_name,
                reads,
                unknown_read,
            );
            spec_expression_current_parameter_accesses(body, parameter_name, reads, unknown_read);
        }
        SpecExpression::Let { value, body, .. } => {
            spec_expression_current_parameter_accesses(value, parameter_name, reads, unknown_read);
            spec_expression_current_parameter_accesses(body, parameter_name, reads, unknown_read);
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                spec_pure_function_argument_current_parameter_accesses(
                    argument,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => {
            spec_expression_current_parameter_accesses(
                pointer,
                parameter_name,
                reads,
                unknown_read,
            );
            spec_expression_current_parameter_accesses(
                elements,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecExpression::MemoryLoad {
            memory: SpecMemory::FunctionEntry | SpecMemory::Fixed(_),
            ..
        } => {}
        SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer,
            value_type,
        } => {
            if let Some(offset) = spec_expression_parameter_offset(pointer, parameter_name) {
                if let Some(range) = parameter_access_range(offset, value_type.byte_width()) {
                    reads.push(range);
                }
            } else if spec_expression_reads_current_parameter(pointer, parameter_name) {
                *unknown_read = true;
            }
        }
        SpecExpression::MemoryLoad {
            memory: SpecMemory::LoopEntry,
            pointer,
            ..
        } => {
            if spec_expression_reads_current_parameter(pointer, parameter_name) {
                *unknown_read = true;
            }
        }
    }
}

fn spec_proposition_current_parameter_accesses(
    proposition: &SpecProposition,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match proposition {
        SpecProposition::AlgebraicComparison { left, right, .. } => {
            spec_algebraic_expression_current_parameter_accesses(
                left,
                parameter_name,
                reads,
                unknown_read,
            );
            spec_algebraic_expression_current_parameter_accesses(
                right,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            spec_expression_current_parameter_accesses(
                element,
                parameter_name,
                reads,
                unknown_read,
            );
            spec_sequence_current_parameter_accesses(sequence, parameter_name, reads, unknown_read);
        }
        SpecProposition::SequenceComparison { left, right, .. } => {
            spec_sequence_current_parameter_accesses(left, parameter_name, reads, unknown_read);
            spec_sequence_current_parameter_accesses(right, parameter_name, reads, unknown_read);
        }
        SpecProposition::Comparison { left, right, .. } => {
            spec_expression_current_parameter_accesses(left, parameter_name, reads, unknown_read);
            spec_expression_current_parameter_accesses(right, parameter_name, reads, unknown_read);
        }
        SpecProposition::FloatClassification { expression, .. }
        | SpecProposition::Defined(expression) => {
            spec_expression_current_parameter_accesses(
                expression,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            spec_proposition_current_parameter_accesses(left, parameter_name, reads, unknown_read);
            spec_proposition_current_parameter_accesses(right, parameter_name, reads, unknown_read);
        }
        SpecProposition::Not(body)
        | SpecProposition::ForAllInt32 { body, .. }
        | SpecProposition::ForAllPointer { body, .. }
        | SpecProposition::ExistsInt32 { body, .. }
        | SpecProposition::ExistsPointer { body, .. } => {
            spec_proposition_current_parameter_accesses(body, parameter_name, reads, unknown_read);
        }
        SpecProposition::Predicate { arguments, .. } => {
            for argument in arguments {
                match argument {
                    SpecPredicateArgument::Value(expression) => {
                        spec_expression_current_parameter_accesses(
                            expression,
                            parameter_name,
                            reads,
                            unknown_read,
                        );
                    }
                    SpecPredicateArgument::ArrayRef { memory, pointer } => {
                        if !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                            && spec_expression_reads_current_parameter(pointer, parameter_name)
                        {
                            *unknown_read = true;
                        }
                    }
                }
            }
        }
        SpecProposition::ResourceSeparate { left, right }
        | SpecProposition::ResourceContains {
            parent: left,
            child: right,
        } => {
            spec_resource_current_parameter_accesses(left, parameter_name, reads, unknown_read);
            spec_resource_current_parameter_accesses(right, parameter_name, reads, unknown_read);
        }
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            ..
        } => {
            if !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                && (spec_expression_reads_current_parameter(base, parameter_name)
                    || spec_expression_reads_current_parameter(start, parameter_name)
                    || spec_expression_reads_current_parameter(end, parameter_name))
            {
                *unknown_read = true;
            }
        }
    }
}

fn spec_sequence_current_parameter_accesses(
    sequence: &SpecSequenceExpression,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match sequence {
        SpecSequenceExpression::Literal(elements) => {
            for element in elements {
                spec_expression_current_parameter_accesses(
                    element,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
        SpecSequenceExpression::Concat(left, right) => {
            spec_sequence_current_parameter_accesses(left, parameter_name, reads, unknown_read);
            spec_sequence_current_parameter_accesses(right, parameter_name, reads, unknown_read);
        }
    }
}

fn spec_resource_current_parameter_accesses(
    resource: &SpecResource,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match resource {
        SpecResource::Memory {
            base, start, end, ..
        } => {
            if spec_expression_reads_current_parameter(base, parameter_name)
                || spec_expression_reads_current_parameter(start, parameter_name)
                || spec_expression_reads_current_parameter(end, parameter_name)
            {
                *unknown_read = true;
            }
        }
        SpecResource::Composite { arguments, .. } | SpecResource::Token { arguments, .. } => {
            for argument in arguments {
                spec_expression_current_parameter_accesses(
                    argument,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
    }
}

fn spec_algebraic_expression_current_parameter_accesses(
    expression: &SpecAlgebraicExpression,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match &expression.node {
        SpecAlgebraicExpressionNode::Variable(_)
        | SpecAlgebraicExpressionNode::Binding(_)
        | SpecAlgebraicExpressionNode::ResourceField(_) => {}
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            for field in fields {
                match field {
                    SpecAlgebraicValue::C(expression) => {
                        spec_expression_current_parameter_accesses(
                            expression,
                            parameter_name,
                            reads,
                            unknown_read,
                        );
                    }
                    SpecAlgebraicValue::Algebraic(expression) => {
                        spec_algebraic_expression_current_parameter_accesses(
                            expression,
                            parameter_name,
                            reads,
                            unknown_read,
                        );
                    }
                }
            }
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            spec_algebraic_expression_current_parameter_accesses(
                scrutinee,
                parameter_name,
                reads,
                unknown_read,
            );
            for arm in arms {
                spec_algebraic_expression_current_parameter_accesses(
                    &arm.body,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                spec_pure_function_argument_current_parameter_accesses(
                    argument,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
    }
}

fn spec_pure_function_argument_current_parameter_accesses(
    argument: &SpecPureFunctionArgument,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match argument {
        SpecPureFunctionArgument::Value(expression) => {
            spec_expression_current_parameter_accesses(
                expression,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecPureFunctionArgument::Algebraic(expression) => {
            spec_algebraic_expression_current_parameter_accesses(
                expression,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecPureFunctionArgument::ArrayRef {
            memory, pointer, ..
        } => {
            if !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                && spec_expression_reads_current_parameter(pointer, parameter_name)
            {
                *unknown_read = true;
            }
        }
    }
}

/// Rejects a postcondition that would expose a modified by-value aggregate
/// parameter through the caller-side contract view. This source-level check
/// runs while the function contract is assembled, before any proof tactic can
/// publish the private copy as a caller fact.
pub(crate) fn modified_by_value_aggregate_parameter_with_current_ensure_in_source(
    function: &CFunction,
) -> Option<String> {
    function
        .parameters()
        .iter()
        .filter(|parameter| parameter.aggregate_layout().is_some())
        .find(|parameter| {
            let mut writes = Vec::new();
            let mut unknown_write = false;
            statement_writes_aggregate_parameter(
                function.source_body(),
                parameter.name(),
                &mut writes,
                &mut unknown_write,
            );
            if writes.is_empty() && !unknown_write {
                return false;
            }
            let mut reads = Vec::new();
            let mut unknown_read = false;
            for ensure in function.contract_ensures() {
                spec_proposition_current_parameter_accesses(
                    ensure,
                    parameter.name(),
                    &mut reads,
                    &mut unknown_read,
                );
            }
            (unknown_write && (unknown_read || !reads.is_empty()))
                || (unknown_read && !writes.is_empty())
                || writes
                    .iter()
                    .any(|write| reads.iter().any(|read| write.overlaps(*read)))
        })
        .map(|parameter| parameter.name().to_string())
}

fn statement_outcome_state(outcome: &CStatementOutcome) -> Option<&CState> {
    match outcome {
        CStatementOutcome::Normal(state)
        | CStatementOutcome::Break(state)
        | CStatementOutcome::Continue(state) => Some(state),
        CStatementOutcome::Return { state, .. } => Some(state),
        CStatementOutcome::VerificationDiverges
        | CStatementOutcome::UndefinedBehavior(_)
        | CStatementOutcome::RuntimeError(_) => None,
    }
}

fn aggregate_parameter_copy_changed(
    entry_state: &CState,
    outcome: &CStatementOutcome,
    parameter: &CParameter,
) -> bool {
    let Some(exit_state) = statement_outcome_state(outcome) else {
        return false;
    };
    let Some(CLocalBinding::AggregateObject { slot, layout, .. }) =
        entry_state.locals.binding(parameter.name())
    else {
        return false;
    };
    let end = i64::from(layout.size_bytes());
    entry_state
        .memory
        .differing_cell_pointers(&exit_state.memory)
        .into_iter()
        .any(|pointer| {
            pointer.block == slot.block
                && pointer
                    .offset
                    .as_const()
                    .is_some_and(|offset| offset >= 0 && offset < end)
        })
}

fn modified_by_value_aggregate_parameter_with_current_ensure(
    entry_state: &CState,
    outcome: &CStatementOutcome,
    function: &CFunction,
) -> Option<String> {
    function
        .parameters()
        .iter()
        .filter(|parameter| parameter.aggregate_layout().is_some())
        .find(|parameter| {
            aggregate_parameter_copy_changed(entry_state, outcome, parameter)
                && function.contract_ensures().iter().any(|ensure| {
                    spec_proposition_reads_current_parameter(ensure, parameter.name())
                })
        })
        .map(|parameter| parameter.name().to_string())
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
    add_verified_function_ensure_facts_selected(
        facts,
        obligations,
        post_contract_state,
        entry_contract_state,
        function,
        function.contract_ensures().iter(),
        effective_assumptions,
        budget,
    )
}

fn add_verified_function_ensure_facts_selected<'a>(
    facts: &mut Vec<ExecutionPureFact>,
    obligations: &[ProofObligation],
    post_contract_state: &CState,
    entry_contract_state: &CState,
    function: &'a CFunction,
    ensures: impl Iterator<Item = &'a SpecProposition>,
    effective_assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<()> {
    for ensure in ensures {
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
            let mut specialized_assumptions = assumptions_with_path_context(
                &ensure_assumptions,
                &ensure_path.facts,
                &ensure_path.obligations,
            );
            let mut specialized = ensure_path.proposition.clone();
            let mut specialized_any_premise = false;
            while let Proposition::Implies(premise, body) = specialized {
                if !specialized_assumptions.proves(&premise) {
                    specialized = Proposition::Implies(premise, body);
                    break;
                }
                specialized_assumptions =
                    specialized_assumptions.assume_proposition((*premise).clone());
                specialized = *body;
                specialized_any_premise = true;
            }
            if specialized_any_premise {
                facts.push(ExecutionPureFact::certified(wrap_path_context(
                    specialized,
                    &ensure_path.facts,
                    &[],
                )));
            }
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
        let value = coerce_c_function_argument_without_obligations(value, parameter)
            .expect("function arguments were type-checked before building contract views");
        let value = value
            .with_pointer_pointee_volatile(parameter.pointee_is_volatile())
            .with_pointer_pointee_constant(parameter.pointee_is_constant());
        state.locals.set_typed_with_all_qualifiers(
            parameter.name().to_string(),
            value.clone(),
            parameter.c_type(),
            parameter.is_volatile(),
            parameter.pointee_is_volatile(),
            parameter.is_constant(),
            parameter.pointee_is_constant(),
        );
        if let CValue::Pointer(pointer) = &value {
            let Some(element_width) = parameter.c_type().pointee_type().map(CType::byte_width)
            else {
                // An opaque object pointer carries identity and qualifiers,
                // but no element width. Do not manufacture a contract view
                // that would make an untyped dereference look loadable.
                continue;
            };
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
    state.locals.set_typed_with_all_qualifiers(
        "result".to_string(),
        value.with_pointer_pointee_constant(function.return_pointee_is_constant()),
        function.return_type(),
        false,
        false,
        false,
        function.return_pointee_is_constant(),
    );
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
    coerce_c_value_with_pointee_constant(
        value,
        function.return_type(),
        function.return_pointee_is_constant(),
        obligations,
        assumptions,
    )
}

pub(super) fn coerce_c_value_with_pointee_constant(
    value: CValue,
    c_type: CType,
    pointee_constant: bool,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    // This is an implicit conversion boundary. Explicit C casts have their
    // own rules; storage read-only status is independently checked on writes.
    if matches!(&value, CValue::Pointer(pointer) if pointer.pointee_constant())
        && c_type.is_pointer()
        && !pointee_constant
    {
        return None;
    }
    Some(
        coerce_c_value_to_type(value, c_type, obligations, assumptions)?
            .with_pointer_pointee_constant(pointee_constant),
    )
}

fn symbolic_function_result(function: &CFunction, variable: Variable) -> CValue {
    symbolic_call_result(function.return_type(), variable)
        .with_pointer_pointee_constant(function.return_pointee_is_constant())
}

pub(crate) fn symbolic_call_result(c_type: CType, variable: Variable) -> CValue {
    match c_type {
        CType::Void => CValue::Void,
        CType::VoidPointer => CValue::typed_pointer(Pointer::symbolic(variable), c_type),
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
            if pointer.block.is_function()
                && pointer.c_type() == CType::FunctionPointer(CallbackSignature::UNSPECIFIED) =>
        {
            // Return and parameter qualifications belong to the callback
            // signature, not to the function-pointer object's pointee view.
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
        let base =
            CMemory::string_literal_pointer(function.name(), literal.name(), literal.bytes());
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
            register_block_alignment(&slot.block, layout.alignment_bytes());
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
        let value = coerce_c_function_argument_without_obligations(value, parameter)?
            .with_pointer_pointee_volatile(parameter.pointee_is_volatile())
            .with_pointer_pointee_constant(parameter.pointee_is_constant());
        if address_taken_parameters.contains(parameter.name()) {
            let slot = CMemory::frame_local_pointer(frame, parameter.name());
            register_block_alignment(&slot.block, parameter.c_type().abi_alignment());
            callee_state.memory = callee_state
                .memory
                .with_block(slot.block.clone(), value.byte_width())
                .store(slot.clone(), value.clone());
            callee_state.locals.set_typed_qualified_with_all_qualifiers(
                parameter.name().to_string(),
                value,
                parameter.c_type(),
                slot,
                parameter.is_volatile(),
                parameter.pointee_is_volatile(),
                parameter.is_constant(),
                parameter.pointee_is_constant(),
            );
        } else {
            callee_state.locals.set_typed_with_all_qualifiers(
                parameter.name().to_string(),
                value,
                parameter.c_type(),
                parameter.is_volatile(),
                parameter.pointee_is_volatile(),
                parameter.is_constant(),
                parameter.pointee_is_constant(),
            );
        }
    }
    Some(callee_state)
}

fn coerce_c_function_argument_without_obligations(
    value: &CValue,
    parameter: &CParameter,
) -> Option<CValue> {
    let mut obligations = Vec::new();
    let value = coerce_c_value_with_pointee_constant(
        value.clone(),
        parameter.c_type(),
        parameter.pointee_is_constant(),
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
            coerced.push(coerce_c_value_with_pointee_constant(
                value.clone(),
                parameter.c_type(),
                parameter.pointee_is_constant(),
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
    initialize_c_function_globals_owned(state.clone(), function)
}

/// Constructs a fresh startup state, never an ordinary call transition.
/// Storage identities coalesce aliases before permissions are issued. No
/// incoming state is accepted, so this cannot replenish consumed resources.
pub(crate) fn initialize_c_program_storage(
    functions: impl IntoIterator<Item = CFunction>,
) -> CState {
    let mut state = CState::new();
    for function in functions {
        state = initialize_c_function_globals_owned(state, &function);
        // Private source spellings are lexical bindings, not program globals.
        state.locals = CLocalEnvironment::default();
    }
    state.resources = initial_static_resources(&state.memory, || {});
    state
}

/// Partition physical storage using its initialized cell types. Adjacent
/// cells of one width form an ordinary typed array range; padding and opaque
/// union storage remain byte ranges. No cross-width ownership rule is added.
fn initial_static_resources(memory: &CMemory, mut visit: impl FnMut()) -> ResourceContext {
    let mut cells_by_block = BTreeMap::<PointerBlock, Vec<(u32, u32)>>::new();
    for (pointer, value) in memory.cells.iter() {
        visit();
        let PointerOffsetTerm::Constant(offset) = pointer.offset else {
            unreachable!("static initializers have constant cell offsets");
        };
        cells_by_block
            .entry(pointer.block.clone())
            .or_default()
            .push((
                u32::try_from(offset).expect("static cell offset"),
                value.byte_width(),
            ));
    }
    let mut resources = ResourceContext::default();
    for (identity, block) in memory.blocks.iter() {
        visit();
        let size = block.size().as_const().expect("static block size");
        let mut ranges = Vec::<(u32, u32, u32)>::new();
        let mut cursor = 0;
        for &(offset, width) in cells_by_block.get(identity).into_iter().flatten() {
            visit();
            assert!(offset >= cursor && offset.checked_add(width).is_some_and(|end| end <= size));
            if offset > cursor {
                ranges.push((cursor, offset, 1));
            }
            if let Some((_, end, previous_width)) = ranges.last_mut()
                && *end == offset
                && *previous_width == width
            {
                *end = offset + width;
            } else {
                ranges.push((offset, offset + width, width));
            }
            cursor = offset + width;
        }
        if cursor < size {
            ranges.push((cursor, size, 1));
        }
        for (start, end, width) in ranges {
            visit();
            let range = CMemoryRange::new_with_element_width(
                Pointer {
                    block: identity.clone(),
                    offset: PointerOffsetTerm::Constant(i64::from(start)),
                },
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant((end - start) / width),
                width,
            );
            resources = resources.unchecked_with_fact(if block.is_read_only() {
                CResourceFact::view_memory(range)
            } else {
                CResourceFact::own_memory(range)
            });
        }
    }
    resources
}

#[cfg(test)]
mod program_entry_tests;

fn initialize_c_function_globals_owned(mut state: CState, function: &CFunction) -> CState {
    for literal in function.string_literals() {
        let slot =
            CMemory::string_literal_pointer(function.name(), literal.name(), literal.bytes());
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
        if !function.is_program_entry()
            && !state
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
        register_block_alignment(&slot.block, global.c_type().abi_alignment());
        if !state.memory.has_block(&slot.block) {
            state.memory = state
                .memory
                .with_block_or_read_only(
                    slot.block.clone(),
                    global.c_type().byte_width(),
                    global.is_constant(),
                )
                .store(slot.clone(), global.initial_value().clone());
        }
        state.locals.set_global_with_all_qualifiers(
            global.kernel_name().to_string(),
            global.c_type(),
            slot.clone(),
            global.is_volatile(),
            false,
            global.is_constant(),
            global.pointee_is_constant(),
        );
        if global.kernel_name() != global.name() && !state.locals.contains_name(global.name()) {
            state.locals.set_global_with_all_qualifiers(
                global.name().to_string(),
                global.c_type(),
                slot,
                global.is_volatile(),
                false,
                global.is_constant(),
                global.pointee_is_constant(),
            );
        }
    }
    for global_array in function.global_arrays() {
        let slot = CMemory::global_pointer(global_array.kernel_name());
        register_block_alignment(&slot.block, global_array.element_type().abi_alignment());
        let bytes = global_array
            .length()
            .checked_mul(global_array.element_type().byte_width())
            .expect("validated C global array size");
        if !state.memory.has_block(&slot.block) {
            state.memory = state.memory.with_block_or_read_only(
                slot.block.clone(),
                bytes,
                global_array.is_constant(),
            );
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
        state.locals.set_array_object_at_with_constant(
            global_array.kernel_name().to_string(),
            global_array.element_type(),
            global_array.length(),
            slot.clone(),
            global_array.is_constant(),
        );
        if global_array.kernel_name() != global_array.name()
            && !state.locals.contains_name(global_array.name())
        {
            state.locals.set_array_object_at_with_constant(
                global_array.name().to_string(),
                global_array.element_type(),
                global_array.length(),
                slot,
                global_array.is_constant(),
            );
        }
    }
    for global_aggregate in function.global_aggregates() {
        let slot = CMemory::global_pointer(global_aggregate.kernel_name());
        register_block_alignment(&slot.block, global_aggregate.layout().alignment_bytes());
        if !state.memory.has_block(&slot.block) {
            state.memory = state.memory.with_block_or_read_only(
                slot.block.clone(),
                global_aggregate.layout().size_bytes(),
                global_aggregate.is_constant(),
            );
            state.memory =
                zero_aggregate_fields(state.memory.clone(), &slot, global_aggregate.layout());
            state.memory = initialize_aggregate_fields(
                state.memory.clone(),
                &slot,
                global_aggregate.initializers(),
            );
        }
        state.locals.set_aggregate_object_at_with_constant(
            global_aggregate.kernel_name().to_string(),
            global_aggregate.layout().clone(),
            slot.clone(),
            global_aggregate.is_constant(),
        );
        if global_aggregate.kernel_name() != global_aggregate.source_name()
            && !state.locals.contains_name(global_aggregate.source_name())
        {
            state.locals.set_aggregate_object_at_with_constant(
                global_aggregate.source_name().to_string(),
                global_aggregate.layout().clone(),
                slot,
                global_aggregate.is_constant(),
            );
        }
    }
    for global_aggregate_array in function.global_aggregate_arrays() {
        let slot = CMemory::global_pointer(global_aggregate_array.kernel_name());
        register_block_alignment(
            &slot.block,
            global_aggregate_array.layout().alignment_bytes(),
        );
        let bytes = global_aggregate_array
            .length()
            .checked_mul(global_aggregate_array.layout().size_bytes())
            .expect("validated C global aggregate array size");
        if !state.memory.has_block(&slot.block) {
            state.memory = state.memory.with_block_or_read_only(
                slot.block.clone(),
                bytes,
                global_aggregate_array.is_constant(),
            );
            state.memory = zero_aggregate_array_fields(
                state.memory.clone(),
                &slot,
                global_aggregate_array.layout(),
                global_aggregate_array.length(),
            );
            state.memory = initialize_aggregate_fields(
                state.memory.clone(),
                &slot,
                global_aggregate_array.initializers(),
            );
        }
        state.locals.set_array_object_at_with_constant(
            global_aggregate_array.kernel_name().to_string(),
            CType::UInt8,
            bytes,
            slot.clone(),
            global_aggregate_array.is_constant(),
        );
        if global_aggregate_array.kernel_name() != global_aggregate_array.source_name()
            && !state
                .locals
                .contains_name(global_aggregate_array.source_name())
        {
            state.locals.set_array_object_at_with_constant(
                global_aggregate_array.source_name().to_string(),
                CType::UInt8,
                bytes,
                slot,
                global_aggregate_array.is_constant(),
            );
        }
    }
    for static_local in function.static_variables() {
        let slot = CMemory::static_pointer(function.name(), static_local.kernel_name());
        register_block_alignment(&slot.block, static_local.c_type().abi_alignment());
        if !state.memory.has_block(&slot.block) {
            state.memory = state.memory.with_block_or_read_only(
                slot.block.clone(),
                static_local.c_type().byte_width(),
                static_local.is_constant(),
            );
            // A qualified resource can materialize the cell before this
            // function's storage declaration is installed. Adding block
            // metadata must not overwrite that existing value.
            if state.memory.known_value(&slot).is_none() {
                state.memory = state
                    .memory
                    .store(slot.clone(), static_local.initial_value().clone());
            }
        }
        state.locals.set_global_with_all_qualifiers(
            static_local.kernel_name().to_string(),
            static_local.c_type(),
            slot.clone(),
            static_local.is_volatile(),
            false,
            static_local.is_constant(),
            static_local.pointee_is_constant(),
        );
        // Contract C fragments use the source spelling. A nested static may
        // have a kernel-only name to distinguish it from another object in a
        // sibling block; expose the spelling only when the callee has not
        // already installed a parameter or another visible binding with it.
        if static_local.kernel_name() != static_local.source_name()
            && !state.locals.contains_name(static_local.source_name())
        {
            state.locals.set_global_with_all_qualifiers(
                static_local.source_name().to_string(),
                static_local.c_type(),
                slot,
                static_local.is_volatile(),
                false,
                static_local.is_constant(),
                static_local.pointee_is_constant(),
            );
        }
    }
    for static_array in function.static_arrays() {
        let slot = CMemory::static_pointer(function.name(), static_array.kernel_name());
        register_block_alignment(&slot.block, static_array.element_type().abi_alignment());
        let bytes = static_array
            .length()
            .checked_mul(static_array.element_type().byte_width())
            .expect("validated C static local array size");
        if !state.memory.has_block(&slot.block) {
            state.memory = state.memory.with_block_or_read_only(
                slot.block.clone(),
                bytes,
                static_array.is_constant(),
            );
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
        state.locals.set_array_object_at_with_constant(
            static_array.kernel_name().to_string(),
            static_array.element_type(),
            static_array.length(),
            slot.clone(),
            static_array.is_constant(),
        );
        if static_array.kernel_name() != static_array.source_name()
            && !state.locals.contains_name(static_array.source_name())
        {
            state.locals.set_array_object_at_with_constant(
                static_array.source_name().to_string(),
                static_array.element_type(),
                static_array.length(),
                slot,
                static_array.is_constant(),
            );
        }
    }
    for static_aggregate in function.static_aggregates() {
        let slot = CMemory::static_pointer(function.name(), static_aggregate.kernel_name());
        register_block_alignment(&slot.block, static_aggregate.layout().alignment_bytes());
        if !state.memory.has_block(&slot.block) {
            state.memory = state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                static_aggregate.layout().size_bytes(),
                static_aggregate.is_constant(),
            );
            state.memory =
                zero_aggregate_fields(state.memory.clone(), &slot, static_aggregate.layout());
            state.memory = initialize_aggregate_fields(
                state.memory.clone(),
                &slot,
                static_aggregate.initializers(),
            );
        }
        state.locals.set_aggregate_object_at_with_constant(
            static_aggregate.kernel_name().to_string(),
            static_aggregate.layout().clone(),
            slot.clone(),
            static_aggregate.is_constant(),
        );
        if static_aggregate.kernel_name() != static_aggregate.source_name()
            && !state.locals.contains_name(static_aggregate.source_name())
        {
            state.locals.set_aggregate_object_at_with_constant(
                static_aggregate.source_name().to_string(),
                static_aggregate.layout().clone(),
                slot,
                static_aggregate.is_constant(),
            );
        }
    }
    for static_aggregate_array in function.static_aggregate_arrays() {
        let slot = CMemory::static_pointer(function.name(), static_aggregate_array.kernel_name());
        register_block_alignment(
            &slot.block,
            static_aggregate_array.layout().alignment_bytes(),
        );
        let bytes = static_aggregate_array
            .length()
            .checked_mul(static_aggregate_array.layout().size_bytes())
            .expect("validated C static aggregate array size");
        if !state.memory.has_block(&slot.block) {
            state.memory = state.memory.with_block_or_read_only(
                slot.block.clone(),
                bytes,
                static_aggregate_array.is_constant(),
            );
            state.memory = zero_aggregate_array_fields(
                state.memory.clone(),
                &slot,
                static_aggregate_array.layout(),
                static_aggregate_array.length(),
            );
            state.memory = initialize_aggregate_fields(
                state.memory.clone(),
                &slot,
                static_aggregate_array.initializers(),
            );
        }
        state.locals.set_array_object_at_with_constant(
            static_aggregate_array.kernel_name().to_string(),
            CType::UInt8,
            bytes,
            slot.clone(),
            static_aggregate_array.is_constant(),
        );
        if static_aggregate_array.kernel_name() != static_aggregate_array.source_name()
            && !state
                .locals
                .contains_name(static_aggregate_array.source_name())
        {
            state.locals.set_array_object_at_with_constant(
                static_aggregate_array.source_name().to_string(),
                CType::UInt8,
                bytes,
                slot,
                static_aggregate_array.is_constant(),
            );
        }
    }
    state
}

fn zero_aggregate_fields(
    mut memory: CMemory,
    base: &Pointer,
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
            | CType::Float64
            | CType::VoidPointer
            | CType::Int32Pointer
            | CType::UInt8Pointer
            | CType::Float32Pointer
            | CType::Float64Pointer
            | CType::Int32PointerPointer
            | CType::UInt8PointerPointer
            | CType::Float32PointerPointer
            | CType::Float64PointerPointer => (field.c_type(), 1),
            CType::Int32Array(length) => (CType::Int32, length),
            CType::UInt8Array(length) => (CType::UInt8, length),
            CType::Float32Array(length) => (CType::Float32, length),
            CType::Float64Array(length) => (CType::Float64, length),
            _ => continue,
        };
        let zero = match element_type {
            CType::Int16 => int16(0),
            CType::Int32 => int32(0),
            CType::UInt8 => uint8(0),
            CType::UInt16 => uint16(0),
            CType::UInt32 => uint32(0),
            CType::Int64 => CValue::Int64(Bitvector32Term::Constant(0)),
            CType::UInt64 => CValue::UInt64(Bitvector32Term::Constant(0)),
            CType::Float32 => CValue::Float32(Bitvector32Term::Constant(0)),
            CType::Float64 => CValue::Float64(Bitvector32Term::UInt64Constant(0)),
            CType::Int32Pointer
            | CType::UInt8Pointer
            | CType::Float32Pointer
            | CType::Float64Pointer
            | CType::Int32PointerPointer
            | CType::UInt8PointerPointer
            | CType::Float32PointerPointer
            | CType::Float64PointerPointer => CValue::typed_pointer(Pointer::null(), element_type),
            CType::Int16Array(_)
            | CType::Int32Array(_)
            | CType::UInt8Array(_)
            | CType::UInt16Array(_)
            | CType::UInt32Array(_)
            | CType::Int64Array(_)
            | CType::UInt64Array(_)
            | CType::Float32Array(_)
            | CType::Float64Array(_)
            | CType::Void
            | CType::VoidPointer
            | CType::FunctionPointer(_) => {
                continue;
            }
            CType::Int16Pointer
            | CType::UInt16Pointer
            | CType::UInt32Pointer
            | CType::Int64Pointer
            | CType::UInt64Pointer
            | CType::Int16PointerPointer
            | CType::UInt16PointerPointer
            | CType::UInt32PointerPointer
            | CType::Int64PointerPointer
            | CType::UInt64PointerPointer => continue,
        };
        for index in 0..element_count {
            let offset = field
                .offset_bytes()
                .checked_add(
                    index
                        .checked_mul(element_type.byte_width())
                        .expect("validated aggregate zero field offset"),
                )
                .expect("validated aggregate zero field offset");
            memory = memory.store(base.offset_by_bytes(offset), zero.clone());
        }
    }
    for union in layout.unions() {
        let union_base = base.offset_by_bytes(union.offset_bytes());
        for field in union.fields() {
            if let Some(value) = zero_union_member_value(field.c_type()) {
                memory = memory.store_union(
                    union_base.offset_by_bytes(field.offset_bytes()),
                    field.c_type(),
                    value,
                );
            }
        }
    }
    memory
}

fn zero_union_member_value(c_type: CType) -> Option<CValue> {
    Some(match c_type {
        CType::Int32 => int32(0),
        CType::UInt8 => uint8(0),
        CType::Int32Pointer
        | CType::UInt8Pointer
        | CType::Int32PointerPointer
        | CType::UInt8PointerPointer
        | CType::FunctionPointer(_) => CValue::typed_pointer(Pointer::null(), c_type),
        _ => return None,
    })
}

fn initialize_aggregate_fields(
    mut memory: CMemory,
    base: &Pointer,
    initializers: &[CAggregateInitializer],
) -> CMemory {
    for initializer in initializers {
        memory = memory.store(
            base.offset_by_bytes(initializer.offset_bytes()),
            initializer.value().clone(),
        );
    }
    memory
}

fn zero_aggregate_array_fields(
    mut memory: CMemory,
    base: &Pointer,
    layout: &CAggregateLayout,
    length: u32,
) -> CMemory {
    for index in 0..length {
        let element_base = base.offset_by_bytes(
            index
                .checked_mul(layout.size_bytes())
                .expect("validated aggregate array zero offset"),
        );
        memory = zero_aggregate_fields(memory, &element_base, layout);
    }
    memory
}

/// Copy the modeled cells of an address-backed aggregate into a distinct
/// destination block. Fixed scalar-array fields and flattened embedded-struct
/// array leaves are copied one cell at a time. Pointer fields are
/// shallow-copied: the pointer value is duplicated,
/// but the pointed-to allocation is not. Missing cells in automatic storage
/// remain missing so an uninitialized source field stays uninitialized in the
/// copy; opaque/external source cells are represented by typed symbolic loads.
/// Whether a borrowed local view names storage its block actually has.
///
/// Only a range whose bounds are constant can be placed against the block's
/// extent. One with symbolic bounds keeps the previous treatment: it is the
/// caller's own stack object either way, and tightening that case belongs
/// with the range-arithmetic work rather than here.
fn local_view_range_within_block(range: &CMemoryRange, memory: &CMemory) -> bool {
    let (Some(start), Some(end)) = (range.start().as_const(), range.end().as_const()) else {
        return true;
    };
    if end <= start {
        return true;
    }
    let Some(elements) = u32::try_from(end - start).ok() else {
        return false;
    };
    let Some(bytes) = elements.checked_mul(range.element_width()) else {
        return false;
    };
    let base = range
        .base()
        .offset_by_elements(range.start().clone(), range.element_width());
    memory.access_in_bounds(&base, bytes)
}

/// Whole-struct assignment copies every member (C11 6.5.16.1p2), but
/// `copy_aggregate_fields` skips a carried field with no source cell. Copying
/// from never-written source storage would then leave the destination's own
/// cell in place and readable. Every aggregate-copy path (direct assignment,
/// return materialization, return assignment) reports that skipped read as an
/// uninitialized read instead, matching what member-wise assignment reports
/// through the ordinary load path.
fn aggregate_copy_reads_uninitialized(
    memory: &CMemory,
    source: &Pointer,
    layout: &CAggregateLayout,
) -> bool {
    // Mirror the carried-field classification in `copy_aggregate_fields`: a
    // field type this copy cannot carry drops the destination cells instead
    // of leaving them readable, so it cannot go stale here.
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
            if uninitialized_aggregate_copy_source_cell(
                memory,
                &source.offset_by_bytes(element_offset),
                element_type,
            ) {
                return true;
            }
        }
    }
    for union in layout.unions() {
        let union_source = source.offset_by_bytes(union.offset_bytes());
        // A union with any readable member is initialized storage: the copy
        // carries the active member view and skips the rest, so no member
        // read is uninitialized. Only a wholly unread union can leave the
        // destination holding a stale cell.
        let union_initialized = union.fields().iter().any(|field| {
            let source_field = union_source.offset_by_bytes(field.offset_bytes());
            // Mirror `copy_aggregate_union_member`: a value stored through
            // any member is carried.
            memory
                .known_union_value(&source_field, field.c_type())
                .is_some()
                || memory
                    .known_value(&source_field)
                    .is_some_and(|value| field.c_type().accepts(&value))
        });
        if union_initialized {
            continue;
        }
        for field in union.fields() {
            let source_field = union_source.offset_by_bytes(field.offset_bytes());
            if uninitialized_aggregate_copy_source_cell(memory, &source_field, field.c_type()) {
                return true;
            }
        }
    }
    false
}

/// Mirrors the silent skip in `copy_aggregate_fields`: no source cell and not
/// a zeroed heap address. Reading such a cell is a read of uninitialized
/// storage when the address is a live local or an uninitialized heap cell;
/// anything else (external or symbolic memory) reads back as an unconstrained
/// symbolic load rather than stale storage.
fn uninitialized_aggregate_copy_source_cell(
    memory: &CMemory,
    source_field: &Pointer,
    element_type: CType,
) -> bool {
    if memory.known_value(source_field).is_some() {
        return false;
    }
    if memory.is_zeroed_heap_address(source_field, element_type.byte_width()) {
        return false;
    }
    memory.is_uninitialized_heap_address(source_field, element_type.byte_width())
        || (source_field.block.starts_with("local:")
            && memory.access_in_bounds(source_field, element_type.byte_width()))
}

/// Every aggregate-copy path goes through this wrapper so a copy from
/// uninitialized source storage is reported as an uninitialized read instead
/// of silently keeping the destination's old value. The raw
/// `copy_aggregate_fields` is deliberately module-private; new call sites in
/// other modules must use this checked form.
pub(super) fn copy_aggregate_fields_checked(
    memory: CMemory,
    source: &Pointer,
    destination: &Pointer,
    layout: &CAggregateLayout,
) -> Result<CMemory, CUndefinedBehavior> {
    if aggregate_copy_reads_uninitialized(&memory, source, layout) {
        return Err(CUndefinedBehavior::UninitializedRead);
    }
    Ok(copy_aggregate_fields(memory, source, destination, layout))
}

// Module-private on purpose: cross-module aggregate copies must go through
// `copy_aggregate_fields_checked` so the uninitialized-source read is always
// reported. (Aggregate argument binding below keeps the raw form for now;
// diagnosing uninitialized reads of call arguments is a separate follow-up.)
fn copy_aggregate_fields(
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
            // A field this copy cannot carry must not leave the destination's
            // previous value in place: C copies every member, so a stale cell
            // would be readable as the destination's old contents. Drop those
            // cells instead, which reads back as unknown rather than wrong.
            unsupported => {
                memory = memory.without_field_cells(destination, field.offset_bytes(), unsupported);
                continue;
            }
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
    for union in layout.unions() {
        let source_union = source.offset_by_bytes(union.offset_bytes());
        let destination_union = destination.offset_by_bytes(union.offset_bytes());
        for field in union.fields() {
            let source_field = source_union.offset_by_bytes(field.offset_bytes());
            let Some(value) = copy_aggregate_union_member(&memory, &source_field, field.c_type())
            else {
                continue;
            };
            memory = memory.store_union(
                destination_union.offset_by_bytes(field.offset_bytes()),
                field.c_type(),
                value,
            );
        }
    }
    memory
}

fn copy_aggregate_union_member(
    memory: &CMemory,
    source_field: &Pointer,
    element_type: CType,
) -> Option<CValue> {
    if let Some(value) = memory.known_union_value(source_field, element_type) {
        return Some(value);
    }
    if let Some(value) = memory.known_value(source_field)
        && element_type.accepts(&value)
    {
        return Some(value);
    }
    if memory.is_zeroed_heap_address(source_field, element_type.byte_width()) {
        return zero_union_member_value(element_type);
    }
    if memory.has_block(&source_field.block)
        && !matches!(source_field.block, PointerBlock::Symbolic(_))
        && memory.access_in_bounds(source_field, element_type.byte_width())
    {
        return None;
    }
    let load = crate::kernel::canonical_form_of_load(
        crate::kernel::intern_c_memory(memory.clone()),
        source_field.clone(),
    );
    Some(match element_type {
        CType::Int32 => CValue::Int32(load),
        CType::UInt8 => CValue::UInt8(load),
        CType::Int32Pointer
        | CType::UInt8Pointer
        | CType::Int32PointerPointer
        | CType::UInt8PointerPointer
        | CType::FunctionPointer(_) => {
            let pointer = if matches!(element_type, CType::FunctionPointer(_)) {
                match load {
                    Bitvector32Term::Variable(variable) => Pointer::symbolic_function(variable),
                    load => Pointer {
                        block: source_field.block.clone(),
                        offset: PointerOffsetTerm::scale_int32(load, 1),
                    },
                }
            } else {
                let pointee_type = element_type.pointee_type()?;
                Pointer {
                    block: source_field.block.clone(),
                    offset: PointerOffsetTerm::scale_int32(
                        load,
                        i64::from(pointee_type.byte_width()),
                    ),
                }
            };
            CValue::typed_pointer(pointer, element_type)
        }
        _ => return None,
    })
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
            CResource::Memory(_) | CResource::Instance(_) => continue,
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
        for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
            let Some(argument) = argument.as_c_value() else {
                return Ok(Err(CRuntimeError::TypeMismatch));
            };
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
    // In particular, preparing several pure callback interfaces must not
    // repeatedly enumerate the caller's unrelated resource frame.
    if function.resource_requires().is_empty() && !preserve_explicit_representation {
        return Ok(Ok(CFunctionResourceTransfer {
            callee_resources: ResourceContext::new(),
            caller_resources_after_requirements: caller_state.resources().clone(),
        }));
    }
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
        // A borrowed view of the caller's own stack object needs no resource
        // from the caller, but it still has to name storage that object has.
        // A range running past the block would otherwise let the callee read
        // whatever the caller keeps beyond it: `views a[0..3]` on an
        // `int32 b[2]` used to be discharged by the block merely existing.
        if let CResourceFact::View(CResource::Memory(range)) = resource
            && range.base().block.starts_with("local:")
            && callee_state.memory().has_block(&range.base().block)
            && local_view_range_within_block(range, callee_state.memory())
        {
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
) -> BTreeMap<(String, ResourceArguments), Bitvector32Term> {
    let mut quantities = BTreeMap::<(String, ResourceArguments), Bitvector32Term>::new();
    for fact in resources.facts() {
        let (name, arguments) = match fact.resource() {
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                (name, arguments)
            }
            CResource::Memory(_) | CResource::Instance(_) => continue,
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
        CResourceSpec::Instance { .. } => false,
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
            CResourceSpec::Instance { .. } => false,
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
    let Some(mut entry_state) = bind_c_function_arguments(caller_state, function, argument_values)
    else {
        return Ok(Err(CRuntimeError::TypeMismatch));
    };
    // Resource formals belong to this call, just like the C argument views.
    entry_state.resource_bindings = post_state.resource_bindings.clone();
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

/// Binds a composite definition's existential witnesses as locals of the
/// body-evaluation state, after its parameters. A witness related to a word
/// by a `where` fact of the shape `word == address(witness) + tag` is bound
/// to that word's recorded origin, so folding and unfolding the same body
/// agree on it; a witness with no recorded origin yet (an unfold whose facts
/// are about to introduce it) is bound to a fresh symbolic pointer chosen
/// deterministically from the variables already in use.
pub(super) fn bind_composite_witnesses(
    definition: &CCompositeResourceDefinition,
    arguments: &[AlgebraicValue],
    state: &mut CState,
    assumptions: &PureFactContext,
) -> Option<Vec<CValue>> {
    let held = state.resources.clone();
    bind_composite_witnesses_with_held(definition, arguments, state, &held, assumptions)
}

/// [`bind_composite_witnesses`] with the held resource facts supplied
/// separately, for callers whose evaluation state carries no resources.
pub(super) fn bind_composite_witnesses_with_held(
    definition: &CCompositeResourceDefinition,
    arguments: &[AlgebraicValue],
    state: &mut CState,
    held: &ResourceContext,
    assumptions: &PureFactContext,
) -> Option<Vec<CValue>> {
    if definition.witnesses().is_empty() {
        return Some(Vec::new());
    }
    let mut values = Vec::new();
    for (index, witness) in definition.witnesses().iter().enumerate() {
        let word = definition
            .facts()
            .iter()
            .find_map(|fact| witness_origin_word(fact, witness.name()))
            .and_then(|word| {
                let mut budget = ExecutionBudget::default();
                let paths = super::spec::evaluate_spec_expression_paths_with_loop_entry(
                    state,
                    word,
                    None,
                    assumptions,
                    &mut budget,
                )
                .ok()?;
                let [path] = paths.as_slice() else {
                    return None;
                };
                match &path.value {
                    CValue::UInt64(term) | CValue::Int64(term) => Some(term.clone()),
                    _ => None,
                }
            });
        let origin = word
            .as_ref()
            .and_then(|term| {
                if term.uint64_as_const() == Some(0) {
                    return Some(Pointer::null());
                }
                let mut used = super::eval::pointer_tags::UsedFacts::new();
                super::eval::pointer_tags::tagged_address_form(term, assumptions, &mut used)
                    .map(|form| form.pointer)
            })
            // A body that contains a composite resource under the witness
            // names it through the resource context: when exactly one held
            // fact of that composite exists, its argument is the witness a
            // fold consumes. This is the fold's own obligation read back,
            // not a search.
            .or_else(|| {
                held_child_witness(definition, witness.name(), arguments, held, assumptions)
            });
        // A witness with no recorded origin is named by the content of the
        // instance that introduces it: the definition, the witness position,
        // the argument values, and the word's own value term. The word term
        // survives materializing the body's cells, which store that same
        // symbolic load, and changes when the word is stored, so every site
        // that instantiates the same body at the same word names the same
        // pointer while a later store names another.
        let pointer = origin.unwrap_or_else(|| {
            use std::hash::{Hash, Hasher};
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            definition.name().hash(&mut hasher);
            index.hash(&mut hasher);
            arguments.hash(&mut hasher);
            // The canonical form names a load by its cell rather than by
            // the snapshot it was read from, so the key is the same before
            // and after the body's cells are materialized.
            word.as_ref()
                .map(super::eval::canonical_term)
                .hash(&mut hasher);
            Pointer::symbolic(Variable(4_000_000_000 + hasher.finish() % 4_000_000_000))
        });
        let value = CValue::typed_pointer(pointer, witness.c_type());
        state
            .locals
            .set_typed(witness.name().to_string(), value.clone(), witness.c_type());
        values.push(value);
    }
    Some(values)
}

/// The unique held composite fact that a `contains name(witness)` clause of
/// the body would consume, if the body has such a clause and exactly one
/// held fact of that composite exists.
fn held_child_witness(
    definition: &CCompositeResourceDefinition,
    witness: &str,
    arguments: &[AlgebraicValue],
    resources: &ResourceContext,
    assumptions: &PureFactContext,
) -> Option<Pointer> {
    // The body's own instance is never its own child.
    let own_pointers = arguments
        .iter()
        .filter_map(|argument| match argument {
            AlgebraicValue::C(CValue::Pointer(pointer)) => Some(pointer.pointer().clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let child_name = definition.contains().iter().find_map(|spec| match spec {
        CResourceSpec::Composite {
            name, arguments, ..
        } if matches!(arguments.as_slice(), [CExpression::Variable(argument)] if argument == witness) => {
            Some(name.as_str())
        }
        _ => None,
    })?;
    let mut candidates = resources
        .facts()
        .iter()
        .filter_map(|fact| match fact.resource() {
            CResource::Composite { name, arguments } if name == child_name => {
                match arguments.as_ref() {
                    [AlgebraicValue::C(CValue::Pointer(pointer))] => {
                        Some(pointer.pointer().clone())
                    }
                    _ => None,
                }
            }
            _ => None,
        })
        // A candidate in the block of one of the body's own pointers must be
        // proven a different pointer.
        .filter(|pointer| {
            own_pointers.iter().all(|own| {
                own.block != pointer.block
                    || assumptions
                        .decide(&ConditionTerm::pointer_equal(pointer.clone(), own.clone()))
                        == Some(false)
            })
        });
    let first = candidates.next()?;
    candidates.all(|other| other == first).then_some(first)
}

/// The word a `where` fact relates `witness` to: for `E == address(witness)`
/// or `E == address(witness) + t` (either operand order, under `and`), the
/// expression `E`.
fn witness_origin_word<'a>(fact: &'a SpecProposition, witness: &str) -> Option<&'a SpecExpression> {
    fn mentions_witness_address(expression: &SpecExpression, witness: &str) -> bool {
        match expression {
            SpecExpression::CExpression(CExpression::Cast {
                expression,
                target_type: CType::UInt64 | CType::Int64,
            }) => matches!(expression.as_ref(), CExpression::Variable(name) if name == witness),
            SpecExpression::Add(left, right) => {
                mentions_witness_address(left, witness) || mentions_witness_address(right, witness)
            }
            _ => false,
        }
    }
    match fact {
        SpecProposition::And(left, right) => {
            witness_origin_word(left, witness).or_else(|| witness_origin_word(right, witness))
        }
        SpecProposition::Comparison {
            left,
            operator: CComparisonOperator::Equal,
            right,
        } => {
            if mentions_witness_address(right, witness) {
                Some(left)
            } else if mentions_witness_address(left, witness) {
                Some(right)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Exchange one exclusive instance for its immediate memory body, or back.
/// Memory-only bodies need no open token, including guarded/matched bodies.
/// This compatibility entry point retains the legacy recursive-child handles.
#[cfg(test)]
pub(crate) fn rewrite_resource_instance(
    state: &CState,
    instance: &ResourceInstance,
    definition: &CCompositeResourceDefinition,
    assumptions: &PureFactContext,
    unfold: bool,
) -> Result<(CState, Vec<Proposition>), &'static str> {
    rewrite_resource_instance_selecting_children(
        state,
        instance,
        definition,
        assumptions,
        unfold,
        None,
    )
}

pub(crate) fn rewrite_resource_instance_selecting_children(
    state: &CState,
    instance: &ResourceInstance,
    definition: &CCompositeResourceDefinition,
    assumptions: &PureFactContext,
    unfold: bool,
    selected_children: Option<&[(String, Variable)]>,
) -> Result<(CState, Vec<Proposition>), &'static str> {
    if definition.name() != instance.name()
        || definition.instance_schema.as_ref() != Some(instance.schema())
        || definition.recursive
        || definition.counted_population
        || !definition.witnesses.is_empty()
        || definition.parameters.len() != instance.arguments.len()
        || instance
            .arguments
            .iter()
            .zip(&definition.parameters)
            .any(|(argument, parameter)| {
                argument
                    .as_c_value()
                    .is_none_or(|value| value.c_type() != parameter.c_type())
            })
        || definition
            .contains
            .iter()
            .any(|body| !matches!(body, CResourceSpec::OwnMemory(_)))
    {
        return Err("instance fold/unfold requires a nonrecursive, witness-free memory body");
    }
    let body_only = selected_children.is_some() || definition.has_memory_only_instance_body();
    let mut folded_instance = instance.clone();
    folded_instance.opened_children = Default::default();
    let folded = CResourceFact::own(CResource::Instance(folded_instance.clone()));
    if unfold {
        if state
            .open_instances
            .owned_instance(instance.identity)
            .is_some()
            || state.resources.owned_instance(instance.identity) != Some(instance)
        {
            return Err("instance is not exclusively owned in folded form");
        }
    } else if (!body_only
        && state.open_instances.owned_instance(instance.identity) != Some(instance))
        || state.resources.owned_instance(instance.identity).is_some()
        || (body_only
            && (state
                .open_instances
                .owned_instance(instance.identity)
                .is_some()
                || !instance.opened_children.is_empty()))
    {
        return Err(if body_only {
            "fold result identity is already in use or carries open-child metadata"
        } else {
            "instance has no matching open handle"
        });
    }
    let mut evaluation = instance_body_evaluation(state, instance, definition)?;
    let mut budget = ExecutionBudget::default();
    let mut algebraic_bindings = BTreeMap::new();
    let mut constructor_fields = Vec::new();
    let selected = if definition.matched.is_some() {
        let (arm, constructor) = selected_instance_match_arm(instance, definition, assumptions)?;
        let AlgebraicTermNode::Constructor { fields, .. } = constructor.node else {
            unreachable!()
        };
        constructor_fields = fields.clone();
        for (name, value) in arm.bindings.iter().zip(fields) {
            match value {
                AlgebraicValue::C(value) => {
                    let ty = value.c_type();
                    evaluation.locals.set_typed(name.clone(), value, ty);
                }
                AlgebraicValue::Algebraic(value) => {
                    algebraic_bindings.insert(name.clone(), value);
                }
            }
        }
        Some(arm)
    } else {
        None
    };
    let active = evaluate_composite_resource_body_condition(
        definition,
        &evaluation,
        assumptions,
        &mut budget,
    )
    .ok_or("instance fold/unfold requires a proved body guard case")?;
    let explicit_children = selected_children.map(|children| {
        children
            .iter()
            .map(|(name, identity)| (name.as_str(), *identity))
            .collect::<BTreeMap<_, _>>()
    });
    if let Some(children) = &explicit_children {
        let supplied = selected_children.unwrap();
        let expected = selected.map_or(&[][..], |arm| arm.children.as_slice());
        let identities = supplied
            .iter()
            .map(|(_, identity)| *identity)
            .collect::<BTreeSet<_>>();
        if children.len() != supplied.len()
            || identities.len() != supplied.len()
            || identities.contains(&instance.identity)
            || children.len() != expected.len()
            || expected
                .iter()
                .any(|child| !children.contains_key(child.name.as_str()))
        {
            return Err("child selection must name every selected arm child exactly once");
        }
    }
    let mut body = evaluate_function_resource_context_with_normalization(
        &evaluation,
        if active {
            selected.map_or(&definition.contains, |arm| &arm.contains)
        } else {
            &[]
        },
        assumptions,
        &mut budget,
        false,
    )
    .map_err(|_| "instance body evaluation exceeded its budget")?
    .map_err(|_| "could not evaluate instance memory body")?;
    // Only the immediate declared memory justifies child-argument loads, not
    // the ambient frame or a child that has not been constructed. On fold,
    // check and consume that memory before allowing it in this scratch view.
    let mut next = state.clone();
    if !unfold {
        for fact in body.facts() {
            next.resources = next
                .resources
                .without_fact_incrementally(fact, assumptions)
                .ok_or("fold requires ownership of the complete instance body")?;
        }
    }
    let mut child_evaluation = evaluation.clone();
    child_evaluation.resources = body.clone();
    let child_assumptions = assumptions.clone().require_owned_expression_loads();
    let mut children = Vec::new();
    let mut resource_bindings = BTreeMap::from([(Variable(u64::MAX), instance.identity)]);
    for child in selected.into_iter().flat_map(|arm| &arm.children) {
        crate::instrumentation::record_deterministic_work(1);
        let recorded = instance
            .opened_children
            .binary_search_by(|(name, _)| name.cmp(&child.name))
            .ok()
            .map(|index| &instance.opened_children[index].1);
        let arguments = child
            .arguments
            .iter()
            .zip(&definition.parameters)
            .map(|(argument, parameter)| {
                let paths = evaluate_c_expression_paths(
                    &child_evaluation,
                    argument,
                    &child_assumptions,
                    &mut budget,
                )
                .map_err(|_| "recursive child argument evaluation exceeded its budget")?;
                if paths.len() != 1
                    || paths[0]
                        .facts
                        .iter()
                        .any(|fact| !child_assumptions.proves(fact.proposition()))
                    || paths[0]
                        .obligations
                        .iter()
                        .any(|goal| !child_assumptions.proves(goal.proposition()))
                {
                    return Err("recursive child argument requires a proved, readable expression");
                }
                match &paths[0].outcome {
                    CExpressionOutcome::Value(value) => {
                        coerce_c_function_argument_without_obligations(&value, parameter)
                            .map(AlgebraicValue::C)
                            .ok_or("recursive child argument type mismatch")
                    }
                    _ => Err("could not evaluate recursive child argument"),
                }
            })
            .collect::<Result<ResourceArguments, _>>()?;
        let fields = child
            .field_bindings
            .iter()
            .map(|index| {
                constructor_fields
                    .get(*index)
                    .cloned()
                    .ok_or("invalid child field binding")
            })
            .collect::<Result<ResourceArguments, _>>()?;
        let identity = if let Some(explicit) = &explicit_children {
            let identity = explicit[child.name.as_str()];
            if unfold
                && (state.resources.owned_instance(identity).is_some()
                    || state.open_instances.owned_instance(identity).is_some())
            {
                return Err("unfold child result identity is already in use");
            }
            identity
        } else if unfold {
            loop {
                let identity = Variable(
                    u64::MAX
                        .checked_sub(next.next_resource_child)
                        .and_then(|value| value.checked_sub(1))
                        .ok_or("child identity supply exhausted")?,
                );
                next.next_resource_child = next
                    .next_resource_child
                    .checked_add(1)
                    .ok_or("child identity supply exhausted")?;
                if state.resources.owned_instance(identity).is_none()
                    && state.open_instances.owned_instance(identity).is_none()
                {
                    break identity;
                }
            }
        } else {
            recorded
                .ok_or("parent has no recorded child handle")?
                .identity
        };
        let mut child_instance = ResourceInstance::new(
            identity,
            instance.name.clone(),
            arguments,
            instance.schema.clone(),
            fields,
        )
        .ok_or("recursive child fields or arguments have invalid types")?;
        if child_instance.arguments.len() != definition.parameters.len()
            || child_instance
                .arguments
                .iter()
                .zip(&definition.parameters)
                .any(|(argument, parameter)| {
                    argument
                        .as_c_value()
                        .is_none_or(|value| value.c_type() != parameter.c_type())
                })
            || (!unfold && explicit_children.is_none() && recorded != Some(&child_instance))
        {
            return Err("recursive child does not match the parent's recorded body");
        }
        if !unfold && explicit_children.is_some() {
            let actual = state
                .resources
                .owned_instance(identity)
                .ok_or("fold requires an owned, folded child")?;
            if actual.name != child_instance.name
                || actual.schema != child_instance.schema
                || actual.arguments.len() != child_instance.arguments.len()
                || actual.fields.len() != child_instance.fields.len()
                || !actual.opened_children.is_empty()
                || !actual
                    .arguments
                    .iter()
                    .zip(child_instance.arguments.iter())
                    .chain(actual.fields.iter().zip(child_instance.fields.iter()))
                    .all(|(a, b)| crate::kernel::resource_arguments_proven_equal(a, b, assumptions))
            {
                return Err("selected child does not satisfy the proposed parent model");
            }
            child_instance = actual.clone();
        }
        resource_bindings.insert(child.binding, identity);
        body = body
            .try_compose_into_valid_context_delaying_normalization(
                [CResourceFact::own(CResource::Instance(
                    child_instance.clone(),
                ))],
                assumptions,
            )
            .map_err(|_| "child ownership is duplicated")?;
        children.push((child.name.clone(), child_instance));
    }
    if !unfold && explicit_children.is_none() && children.len() != instance.opened_children.len() {
        return Err("fold would discard a recorded child");
    }
    if unfold {
        next.resources = next
            .resources
            .without_fact_delaying_normalization(&folded, assumptions)
            .ok_or("instance ownership is missing")?
            .try_compose_into_valid_context_delaying_normalization(
                body.facts().iter().cloned(),
                assumptions,
            )
            .map_err(|_| "instance body overlaps existing ownership")?;
        if !body_only {
            let mut handle = folded_instance.clone();
            children.sort_by(|(left, _), (right, _)| left.cmp(right));
            handle.opened_children = children.into();
            next.open_instances = next
                .open_instances
                .unchecked_with_fact(CResourceFact::own(CResource::Instance(handle)));
        }
    } else {
        // Immediate memory was consumed before evaluating child arguments.
        for fact in body
            .facts()
            .iter()
            .filter(|fact| fact.memory_range().is_none())
        {
            next.resources = next
                .resources
                .without_fact_incrementally(fact, assumptions)
                .ok_or("fold requires ownership of the complete instance body")?;
        }
        next.resources = next
            .resources
            .try_compose_into_valid_context_delaying_normalization([folded.clone()], assumptions)
            .map_err(|_| "fold would duplicate instance ownership")?;
        if !body_only {
            next.open_instances = next
                .open_instances
                .without_exact_representation(&CResourceFact::own(CResource::Instance(
                    instance.clone(),
                )))
                .ok_or("open handle is missing")?;
        }
    }
    evaluation.resources = if unfold {
        next.resources.clone()
    } else {
        state.resources.clone()
    };
    evaluation.open_instances = if unfold {
        next.open_instances.clone()
    } else {
        state.open_instances.clone()
    };
    evaluation.resource_bindings = Some(std::sync::Arc::new(resource_bindings));
    if body_only {
        // Local field interpretation only. This scratch view never escapes
        // into proof state and supplies no additional memory ownership.
        evaluation.open_instances = evaluation
            .open_instances
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(folded_instance)));
    }
    let mut facts = body.observable_facts_assuming_valid(assumptions);
    for fact in body.facts() {
        let Some(range) = fact.memory_range() else {
            continue;
        };
        let width = range.element_width();
        facts.push(Proposition::CMemoryLoadable {
            memory: state.memory.clone(),
            base: range
                .base()
                .offset_by_elements(range.start().clone(), width),
            bytes: Bitvector32Term::multiply(
                Bitvector32Term::subtract(range.end().clone(), range.start().clone()),
                Bitvector32Term::Constant(width),
            ),
        });
    }
    facts.push(Proposition::CResourceComposition(body));
    let mut body_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    for fact in &facts {
        body_assumptions = body_assumptions.assume_proposition(fact.clone());
    }
    for fact in selected
        .map_or(&definition.facts, |arm| &arm.facts)
        .iter()
        .filter(|_| active)
    {
        let paths = crate::kernel::spec::lower_spec_proposition_at_state_with_algebraic_bindings(
            &evaluation,
            fact,
            None,
            &body_assumptions,
            &algebraic_bindings,
            &mut budget,
        )
        .map_err(|_| "could not evaluate instance body fact")?;
        if paths.len() != 1
            || paths[0]
                .facts
                .iter()
                .any(|fact| !body_assumptions.proves(fact.proposition()))
            || paths[0]
                .obligations
                .iter()
                .any(|goal| !body_assumptions.proves(goal.proposition()))
        {
            return Err("instance body fact needs an unsupported conditional proof");
        }
        let proposition = paths[0].proposition.clone();
        if !unfold && !assumptions.proves(&proposition) {
            return Err("fold requires the instance body facts for the proposed fields");
        }
        facts.push(proposition);
    }
    Ok((next, if unfold { facts } else { vec![] }))
}

pub(in crate::kernel) fn selected_instance_match_arm<'a>(
    instance: &ResourceInstance,
    definition: &'a CCompositeResourceDefinition,
    assumptions: &PureFactContext,
) -> Result<(&'a CResourceMatchArm, AlgebraicTerm), &'static str> {
    let body = definition
        .matched
        .as_ref()
        .ok_or("missing resource match body")?;
    if definition.condition.is_some()
        || !definition.contains.is_empty()
        || !definition.facts.is_empty()
        || !body.algebraic_type.has_consistent_root_schema()
        || body.algebraic_type.rigid
        || instance
            .schema()
            .fields()
            .get(body.field_index)
            .map(|(_, ty)| ty)
            != Some(&ResourceFieldType::Algebraic(body.algebraic_type.clone()))
        || body.arms.len() != body.algebraic_type.variants.len()
    {
        return Err("invalid resource match schema");
    }
    let mut variants = BTreeSet::new();
    let schema_variants = body
        .algebraic_type
        .variants
        .iter()
        .map(|variant| (variant.name.as_str(), &variant.fields))
        .collect::<BTreeMap<_, _>>();
    let reserved = definition
        .parameters
        .iter()
        .map(|parameter| parameter.name())
        .chain(
            instance
                .schema()
                .fields()
                .iter()
                .map(|(name, _)| name.as_str()),
        )
        .collect::<BTreeSet<_>>();
    for arm in &body.arms {
        let mut names = BTreeSet::new();
        if !variants.insert(&arm.variant)
            || schema_variants
                .get(arm.variant.as_str())
                .is_none_or(|fields| {
                    **fields != arm.binding_types || fields.len() != arm.bindings.len()
                })
            || arm.bindings.iter().any(|name| {
                name.is_empty() || !names.insert(name) || reserved.contains(name.as_str())
            })
            || arm
                .contains
                .iter()
                .any(|resource| !matches!(resource, CResourceSpec::OwnMemory(_)))
        {
            return Err("invalid resource match arm");
        }
        let mut child_names = BTreeSet::new();
        let mut child_bindings = BTreeSet::new();
        for child in &arm.children {
            if child.name.is_empty()
                || reserved.contains(child.name.as_str())
                || names.contains(&child.name)
                || !child_names.insert(&child.name)
                || child.binding == Variable(u64::MAX)
                || !child_bindings.insert(child.binding)
                || child.arguments.len() != definition.parameters.len()
                || child.field_bindings.len() != instance.schema.fields().len()
            {
                return Err("invalid recursive child schema");
            }
            for ((_, field_type), index) in
                instance.schema.fields().iter().zip(&child.field_bindings)
            {
                let expected = match field_type {
                    ResourceFieldType::C(ty) => AlgebraicValueType::C(*ty),
                    ResourceFieldType::Algebraic(ty) => ty.value_type(),
                };
                if arm.binding_types.get(*index) != Some(&expected) {
                    return Err(
                        "recursive child fields must be immediate constructor bindings of the declared type",
                    );
                }
            }
            // In particular, the parent's matched field is bound to a field
            // of this constructor, never to the whole parent model.
            if arm
                .binding_types
                .get(child.field_bindings[body.field_index])
                != Some(&body.algebraic_type.value_type())
            {
                return Err("recursive child model must be a proper submodel");
            }
        }
    }
    let Some(AlgebraicValue::Algebraic(model)) = instance.fields().get(body.field_index) else {
        return Err("resource match field is not algebraic");
    };
    let constructor = assumptions
        .known_algebraic_constructor(model)
        .ok_or("resource match requires constructor evidence for the instance field")?;
    let AlgebraicTermNode::Constructor { variant, .. } = &constructor.node else {
        unreachable!()
    };
    let arm = body
        .arms
        .iter()
        .find(|arm| &arm.variant == variant)
        .ok_or("unknown resource match constructor")?;
    Ok((arm, constructor))
}

fn instance_body_evaluation(
    state: &CState,
    instance: &ResourceInstance,
    definition: &CCompositeResourceDefinition,
) -> Result<CState, &'static str> {
    let mut evaluation = state.clone();
    if definition.has_memory_only_instance_body() {
        // A local interpretation of proposed fields, never ownership or a
        // persistent open handle. Guards may refer to these fields as well.
        evaluation.open_instances = evaluation
            .open_instances
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(instance.clone())));
    }
    if definition.matched.is_some() {
        // An arm's C names are lexical parameters and constructor bindings,
        // never incidental locals of the function currently opening it.
        evaluation.locals = CLocalEnvironment::default();
    }
    evaluation.resource_bindings = Some(std::sync::Arc::new(BTreeMap::from([(
        Variable(u64::MAX),
        instance.identity,
    )])));
    for (parameter, value) in definition.parameters.iter().zip(instance.arguments.iter()) {
        let value = value
            .as_c_value()
            .ok_or("resource argument is not a C value")?;
        if value.c_type() != parameter.c_type() {
            return Err("resource argument type mismatch");
        }
        evaluation.locals.set_typed(
            parameter.name().to_owned(),
            value.clone(),
            parameter.c_type(),
        );
    }
    Ok(evaluation)
}

pub(in crate::kernel) fn instance_body_guard_case(
    state: &CState,
    instance: &ResourceInstance,
    definition: &CCompositeResourceDefinition,
    assumptions: &PureFactContext,
) -> Option<bool> {
    let evaluation = instance_body_evaluation(state, instance, definition).ok()?;
    evaluate_composite_resource_body_condition(
        definition,
        &evaluation,
        assumptions,
        &mut ExecutionBudget::default(),
    )
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
    if definition.instance_schema.is_some() || definition.matched.is_some() {
        return None;
    }
    if definition.parameters().len() != arguments.len() {
        return None;
    }
    let expansion_base = context.clone().without_exact_representation(composite)?;
    let mut state = CState::new()
        .with_memory(memory.clone())
        .with_resource_context(expansion_base.clone());
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let argument = argument.as_c_value()?;
        if parameter.c_type() != argument.c_type() {
            return None;
        }
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.c_type(),
        );
    }
    bind_composite_witnesses(definition, arguments, &mut state, assumptions)?;
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
        let AlgebraicValue::C(CValue::Pointer(argument)) = argument else {
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
    let mut populations = BTreeMap::<(String, ResourceArguments), Bitvector32Term>::new();
    for fact in context.facts() {
        let (name, arguments) = match fact.resource() {
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                (name, arguments)
            }
            CResource::Memory(_) | CResource::Instance(_) => continue,
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
                for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
                    let argument = argument.as_c_value()?;
                    if parameter.c_type() != argument.c_type() {
                        return None;
                    }
                    population_state.locals.set_typed(
                        parameter.name().to_string(),
                        argument.clone(),
                        parameter.c_type(),
                    );
                }
                bind_composite_witnesses(
                    definition,
                    &arguments,
                    &mut population_state,
                    assumptions,
                )?;
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
                for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
                    let argument = argument.as_c_value()?;
                    if parameter.c_type() != argument.c_type() {
                        return None;
                    }
                    population_state.locals.set_typed(
                        parameter.name().to_string(),
                        argument.clone(),
                        parameter.c_type(),
                    );
                }
                bind_composite_witnesses(
                    definition,
                    &arguments,
                    &mut population_state,
                    assumptions,
                )?;
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
        for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
            let argument = argument.as_c_value()?;
            if parameter.c_type() != argument.c_type() {
                return None;
            }
            population_state.locals.set_typed(
                parameter.name().to_string(),
                argument.clone(),
                parameter.c_type(),
            );
        }
        bind_composite_witnesses(definition, &arguments, &mut population_state, assumptions)?;
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
                // Resource-definition loadability facts are symbolic summaries;
                // their owning range supplies the concrete validity check when
                // the resource is used. Do not turn an unconstrained summary
                // endpoint into a failed definition during population setup.
                let Ok(paths) = lower_spec_proposition_at_state_without_range_guards(
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
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let argument = argument.as_c_value()?;
        if parameter.c_type() != argument.c_type() {
            return None;
        }
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.c_type(),
        );
    }
    bind_composite_witnesses(definition, arguments, &mut state, assumptions)?;
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
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let argument = argument.as_c_value()?;
        if parameter.c_type() != argument.c_type() {
            return None;
        }
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.c_type(),
        );
    }
    bind_composite_witnesses(definition, arguments, &mut state, assumptions)?;
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
            CResourceSpec::Instance { .. } => continue,
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
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let argument = argument.as_c_value()?;
        if parameter.c_type() != argument.c_type() {
            return None;
        }
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.c_type(),
        );
    }
    bind_composite_witnesses(definition, arguments, &mut state, assumptions)?;
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
            // Resource-definition loadability facts are symbolic summaries;
            // their owning range supplies the concrete validity check when
            // the resource is used. Do not turn an unconstrained summary
            // endpoint into a failed definition during population setup.
            let Ok(paths) = lower_spec_proposition_at_state_without_range_guards(
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
    evaluate_function_resource_context_with_normalization(
        state,
        resources,
        assumptions,
        budget,
        true,
    )
}

fn evaluate_function_resource_context_with_normalization(
    state: &CState,
    resources: &[CResourceSpec],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    normalize: bool,
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
        // Instance rewrites retain the declared memory pieces so folding does
        // not need to normalize an ambient block just to consume those pieces.
        let composed = if normalize {
            context.try_compose_with_fact(resource, assumptions)
        } else {
            context.try_compose_into_valid_context_delaying_normalization([resource], assumptions)
        };
        context = match composed {
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
        ResourceContextValidityError::InvalidInstanceAccess(_) => CRuntimeError::FunctionContract(
            "field-bearing resource instances require exclusive ownership with quantity one".into(),
        ),
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
        CResourceSpec::Instance {
            identity,
            schema,
            resource,
        } => {
            let required =
                match evaluate_function_resource_spec(state, resource, assumptions, budget)? {
                    Ok(resource) => resource,
                    Err(error) => return Ok(Err(error)),
                };
            let Some(instance) = state.owned_resource_instance(*identity) else {
                return Ok(Err(CRuntimeError::FunctionContract(
                    "named resource instance is not owned".into(),
                )));
            };
            let CResourceFact::Own(CResource::Composite { name, arguments }, quantity) = required
            else {
                return Ok(Err(CRuntimeError::FunctionContract(
                    "named instance requires an owned resource definition".into(),
                )));
            };
            if quantity.as_const() != Some(1)
                || instance.name() != name
                || instance.schema() != schema
                || instance.arguments().len() != arguments.len()
                || !instance
                    .arguments()
                    .iter()
                    .zip(arguments.iter())
                    .all(|(a, b)| crate::kernel::resource_arguments_proven_equal(a, b, assumptions))
            {
                return Ok(Err(CRuntimeError::FunctionContract(
                    "named resource instance does not match its contract".into(),
                )));
            }
            Ok(Ok(CResourceFact::own(CResource::Instance(
                instance.clone(),
            ))))
        }
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
            arguments: values.into_iter().map(AlgebraicValue::C).collect(),
        },
        ResourceFamily::Token => CResource::Token {
            name: name.to_string(),
            arguments: values.into_iter().map(AlgebraicValue::C).collect(),
        },
        ResourceFamily::Memory | ResourceFamily::Instance => {
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
        CResourceFact::Own(
            CResource::Composite { .. } | CResource::Token { .. } | CResource::Instance(_),
            _,
        ) => 2,
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

/// Returns the caller-visible memory after a function returns.
pub(in crate::kernel) fn function_exit_memory(
    caller_state: &CState,
    callee_state: &CState,
    value: &CValue,
    function: &CFunction,
) -> CMemory {
    if function.return_aggregate_layout().is_some() {
        return callee_state.memory.clone();
    }
    match value {
        CValue::Pointer(pointer)
            if pointer.pointer().block.starts_with("local:")
                && !caller_state.memory.has_block(&pointer.pointer().block) =>
        {
            callee_state
                .memory
                .without_local_block(&pointer.pointer().block)
        }
        _ => callee_state.memory.clone(),
    }
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
            let value = if let Some(layout) = function.return_aggregate_layout() {
                // The return materializer copies the callee's aggregate into
                // a caller-visible slot. Reading an unwritten field there is
                // an uninitialized read, not a contract violation, so check
                // the source before materializing.
                if let CValue::Pointer(pointer) = &value
                    && !pointer.is_null()
                    && aggregate_copy_reads_uninitialized(&state.memory, pointer.pointer(), layout)
                {
                    return (
                        CFunctionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead),
                        obligations,
                    );
                }
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
            if return_resources.is_none() {
                caller_state.open_instances = state.open_instances;
            }
            caller_state.resources = return_resources.cloned().unwrap_or(state.resources);
            caller_state.counted_populations = state.counted_populations;
            caller_state.next_local_frame = state.next_local_frame;
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
