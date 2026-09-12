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

// Resource-clause evaluation reports the exact checked resource that a
// failed expression tried to read.  The section worklist below captures that
// fact while each clause runs, allowing only clauses that depend on a newly
// supplied fact to be retried.
thread_local! {
    static RESOURCE_DEPENDENCY_CAPTURE: std::cell::RefCell<Option<Vec<CResourceFact>>> =
        const { std::cell::RefCell::new(None) };
    #[cfg(test)]
    static RESOURCE_CLAUSE_ATTEMPTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

pub(crate) fn record_resource_dependency(resource: CResourceFact) {
    RESOURCE_DEPENDENCY_CAPTURE.with(|capture| {
        let mut captured = capture.borrow_mut();
        let Some(dependencies) = captured.as_mut() else {
            return;
        };
        if !dependencies.contains(&resource) {
            dependencies.push(resource);
        }
    });
}

fn capture_resource_dependencies<T>(operation: impl FnOnce() -> T) -> (T, Vec<CResourceFact>) {
    RESOURCE_DEPENDENCY_CAPTURE.with(|capture| {
        let previous = capture.replace(Some(Vec::new()));
        let result = operation();
        let captured = capture.replace(previous).unwrap_or_default();
        // Resource expression evaluation can call another checked contract
        // boundary.  Preserve nested missing-resource observations in the
        // enclosing clause's capture instead of dropping them when the inner
        // capture is restored.
        if let Some(active) = capture.borrow_mut().as_mut() {
            for dependency in &captured {
                if !active.contains(dependency) {
                    active.push(dependency.clone());
                }
            }
        }
        (result, captured)
    })
}

#[cfg(test)]
pub(crate) fn measure_resource_clause_attempts<T>(operation: impl FnOnce() -> T) -> (T, usize) {
    RESOURCE_CLAUSE_ATTEMPTS.with(|attempts| {
        let previous = attempts.replace(0);
        let result = operation();
        let measured = attempts.replace(previous);
        (result, measured)
    })
}

#[cfg(test)]
fn record_resource_clause_attempt() {
    RESOURCE_CLAUSE_ATTEMPTS.with(|attempts| attempts.set(attempts.get() + 1));
}
#[derive(Clone, Debug, Eq, PartialEq)]
struct CFunctionResourceTransfer {
    /// The complete checked entry transition.  The two partitions are kept
    /// explicitly so callers cannot accidentally treat a borrowed view as a
    /// consumed capability when reconstructing the caller successor.
    borrowed_inputs: Vec<CCheckedResourceFact>,
    consumed_inputs: Vec<CCheckedResourceFact>,
    callee_resources: ResourceContext,
    /// Resources left in the caller after the entry requirements have been
    /// consumed; this is the caller frame for the remainder of the call.
    caller_resources_after_requirements: ResourceContext,
    /// Filled by the verified-application preparer once entry guards and
    /// dependent addresses have been checked.  It is the sole memory-effect
    /// projection used by modular call havoc and its effect fact.
    memory_effects: Vec<CMemoryRange>,
    post_outputs: Option<ResourceContext>,
}

/// One normalized resource clause after its address/argument loads have been
/// checked.  The fact alone is deliberately not enough for a transition:
/// an owned fact can be borrowed at the contract boundary, and an instance
/// can retain entry identity while its fields are checked at post state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CCheckedResourceFact {
    pub(crate) fact: CResourceFact,
    pub(crate) role: CResourceTransferRole,
    pub(crate) snapshot: CResourceSnapshot,
    pub(crate) clause_position: Option<(usize, usize)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CFunctionMemoryEffectProjection {
    ranges: Vec<CMemoryRange>,
    evidence_facts: Vec<ExecutionPureFact>,
}

impl CFunctionMemoryEffectProjection {
    pub(crate) fn ranges(&self) -> &[CMemoryRange] {
        &self.ranges
    }
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
    if arguments.len() != function.parameters().len() {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::WrongArity {
                expected: function.parameters().len(),
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
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                    argument_binding_error(function, &arguments_path.values).to_string(),
                )),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        };
        let Some(callee_state) = bind_c_function_arguments(state, function, &argument_values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                    argument_binding_error(function, &argument_values).to_string(),
                )),
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
    if arguments.len() != function.parameters().len() {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::WrongArity {
                expected: function.parameters().len(),
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
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                    argument_binding_error(function, &arguments_path.values).to_string(),
                )),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        };
        let Some(callee_state) = bind_c_function_arguments(state, function, &argument_values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                    argument_binding_error(function, &argument_values).to_string(),
                )),
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
        // External summaries use the same body-independent application
        // interface as verified rules, but remain an assumption: do not
        // repackage one as `CVerifiedFunctionRule`, whose type carries body
        // safety evidence. Applying the shared rule engine does not execute,
        // inspect, or certify the external body's storage.
        let binder_application = selected_call_binder_application(
            rule.function.name(),
            rule.function.contract_interface(),
            environment,
        );
        return execute_verified_function_applications(
            caller_state,
            &[CFunctionContractApplication {
                name: rule.function.name(),
                interface_name: rule.function.name(),
                interface: rule.function.contract_interface(),
                evidence: None,
            }],
            None,
            binder_application
                .as_ref()
                .map(|application| (0, application)),
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
    if arguments.len() != function.parameters().len() {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::WrongArity {
                expected: function.parameters().len(),
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
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                    argument_binding_error(function, &arguments_path.values).to_string(),
                )),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        };
        let Some(callee_state) =
            bind_c_function_arguments(caller_state, function, &argument_values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                    argument_binding_error(function, &argument_values).to_string(),
                )),
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
    // A `step(callee(...), { binder: instance })` names exactly this call.
    // The map is the whole binding: every instance binder the callee declares
    // is looked up once, and nothing else is consulted.
    let binder_application = selected_call_binder_application(
        rule.function.name(),
        rule.function.contract_interface(),
        environment,
    );
    execute_verified_function_applications(
        caller_state,
        &[CFunctionContractApplication {
            name: rule.function.name(),
            interface_name: rule.function.name(),
            interface: rule.function.contract_interface(),
            evidence: Some(&rule.function),
        }],
        None,
        binder_application
            .as_ref()
            .map(|application| (0, application)),
        arguments,
        assumptions,
        environment,
        budget,
    )
}

/// The binder transport the proof selected for a call to `function`, if the
/// step named this callee. The transported instances are exactly the
/// function's own `owns`, `consumes`, and `produces` binders.
fn selected_call_binder_application(
    function_name: &str,
    interface: &CFunctionContractInterface,
    environment: &CExecutionEnvironment,
) -> Option<ResourceCallApplication> {
    let transport = environment.selected_call_binders.as_ref()?;
    if transport.function.as_ref() != function_name {
        return None;
    }
    // Only the binders required at entry are checked here; a `produces`
    // binder has no instance to check until the call returns.
    let parameters = interface
        .resource_requires()
        .iter()
        .filter(|resource| resource.is_instance())
        .cloned()
        .collect::<Vec<_>>();
    Some(ResourceCallApplication {
        parameters: parameters.into(),
        bindings: transport.bindings.clone(),
    })
}

/// One candidate contract application. The interface is the complete input
/// to callback preparation; optional concrete evidence is consulted only by
/// verified direct calls for body-specific safety checks and loadable literal
/// facts. Named callbacks and external assumptions carry no `CFunction` here,
/// so arbitrary template bodies/storage cannot affect their behavior.
#[derive(Clone, Copy)]
struct CFunctionContractApplication<'a> {
    /// Concrete callee name used for diagnostics and call provenance.
    name: &'a str,
    /// Nominal interface name used to distinguish candidates and their source
    /// requirement metadata.
    interface_name: &'a str,
    interface: &'a CFunctionContractInterface,
    evidence: Option<&'a CFunction>,
}

fn execute_verified_function_applications(
    caller_state: &CState,
    applications: &[CFunctionContractApplication<'_>],
    selected_contract: Option<usize>,
    resource_application: Option<(usize, &ResourceCallApplication)>,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    if applications.is_empty() {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                "call requires at least one contract application".to_string(),
            )),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    }
    let application = applications[0];
    // Every named instance the callee declares must be bound by the selected
    // application. The check is one map lookup per declared binder, so an
    // unbound binder is refused here rather than transported silently.
    if let Some(unbound) = applications
        .iter()
        .enumerate()
        .find_map(|(index, application)| {
            let bindings = resource_application
                .filter(|(selected, _)| *selected == index)
                .map(|(_, application)| &application.bindings);
            application
                .interface
                .resource_requires()
                .iter()
                .chain(application.interface.resource_ensures())
                .find(|resource| {
                    resource.instance_identity().is_some_and(|identity| {
                        !bindings.is_some_and(|bindings| bindings.contains_key(&identity))
                    })
                })
                .map(|_| application.name.to_string())
        })
    {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                "calls with named resource instances require checked binder transport: `{unbound}` has an unbound instance binder"
            ))),
            facts: vec![],
            obligations: vec![],
        }]);
    }
    budget.consume_function_call()?;
    let existing_variables = crate::instrumentation::measure_operation(
        application.name,
        "verified function rule application",
        "verified call variable collection",
        || {
            let mut existing_variables = BTreeSet::new();
            collect_c_state_bitvector_variables(caller_state, &mut existing_variables);
            for application in applications {
                collect_c_function_contract_interface_bitvector_variables(
                    application.interface,
                    &mut existing_variables,
                );
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
        for (index, application) in applications.iter().enumerate() {
            let prepared = prepare_verified_function_call(
                caller_state,
                *application,
                index,
                arguments,
                arguments_path.clone(),
                applications.len() > 1 || selected_contract.is_some(),
                assumptions,
                environment,
                budget,
                resource_application
                    .filter(|(selected, _)| *selected == index)
                    .map(|(_, application)| application),
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
                !call.interface.resource_requires().is_empty()
                    || !call.interface.resource_ensures().is_empty()
                    || !call.interface.resource_constructors().is_empty()
                    || !call.transfer.memory_effects.is_empty()
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
                !call.interface.resource_requires().is_empty()
                    || !call.interface.resource_ensures().is_empty()
            });
        let primary = applicable.remove(selected_position.unwrap_or(0));
        let PreparedVerifiedFunctionCall {
            name,
            interface_name: _interface_name,
            evidence,
            interface,
            argument_values,
            entry_state,
            entry_contract_state,
            mut transfer,
            mut facts,
            obligations,
            effective_assumptions,
            bindings: selected_bindings,
        } = primary;
        let additional_calls = applicable.into_iter();
        let memory = if transfer.memory_effects.is_empty() {
            entry_state.memory.clone()
        } else {
            entry_state.memory.clone().with_call_memory_havoc(
                memory_identity,
                &transfer.memory_effects,
                &effective_assumptions,
            )
        };
        if !transfer.memory_effects.is_empty() {
            facts.push(
                ExecutionPureFact::internal(Proposition::CMemoryEffectSummary {
                    before: entry_state.memory.clone(),
                    after: memory.clone(),
                    mutable_ranges: transfer.memory_effects.clone(),
                })
                .into_certified(),
            );
        }
        let result = symbolic_contract_result(interface, result_identity);
        let mut post_state = entry_state.clone().with_memory(memory);
        if interface.return_type() != CType::Void {
            set_contract_result(&mut post_state, interface, result.clone());
        }
        // A `produces` binder owns nothing at entry: the call creates the
        // instance under the identity the caller's `let` introduced. It is
        // built once, here, so the population transition and the returned
        // resources agree on its fresh fields.
        let mut produced_instances = BTreeMap::new();
        for resource in interface.resource_ensures() {
            let Some(identity) = resource.instance_identity() else {
                continue;
            };
            let Some(schema) = resource.instance_schema() else {
                continue;
            };
            if resource.role() == CResourceTransferRole::Borrow
                || entry_contract_state
                    .owned_resource_instance(identity)
                    .is_some()
            {
                continue;
            }
            let Some(produced) = selected_bindings
                .as_ref()
                .and_then(|bindings| bindings.get(&identity).copied())
            else {
                continue;
            };
            let Some(instance_resource) = resource.instance_resource_spec() else {
                continue;
            };
            let (name, arguments) = match evaluate_function_resource_spec(
                &post_state,
                &instance_resource,
                &effective_assumptions,
                budget,
            )? {
                Ok(CResourceFact::Own(CResource::Composite { name, arguments }, quantity))
                    if quantity.as_const() == Some(1) =>
                {
                    (name, arguments)
                }
                Ok(_) => {
                    return Ok(vec![resource_call_failure(
                        "a produced resource instance requires an owned resource definition",
                    )]);
                }
                Err(error) => {
                    return Ok(vec![CFunctionPath {
                        outcome: CFunctionOutcome::RuntimeError(error),
                        facts,
                        obligations,
                    }]);
                }
            };
            let fields = schema
                .fields()
                .iter()
                .map(|(_, ty)| {
                    variables.next = budget.next_kernel_variable;
                    let variable = variables.next();
                    budget.next_kernel_variable = variables.next;
                    match ty {
                        ResourceFieldType::Integer => {
                            AlgebraicValue::Integer(IntegerTerm::Variable(variable))
                        }
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
            produced_instances.insert(
                identity,
                ResourceInstance::new(produced, name, arguments, schema.clone(), fields)
                    .expect("fresh symbolic fields have their declared types"),
            );
        }
        let callee_resources = if produced_instances.is_empty() {
            transfer.callee_resources.clone()
        } else {
            transfer.callee_resources.clone().unchecked_with_facts(
                produced_instances
                    .values()
                    .map(|instance| CResourceFact::own(CResource::Instance(instance.clone()))),
            )
        };
        let mut transition_state = post_state.clone().with_resource_context(callee_resources);
        let population_timing = crate::instrumentation::OperationTiming::new(
            name,
            "verified function rule application",
            "verified call population transition",
        );
        let population_transition = match apply_counted_population_transitions_with_interface(
            caller_state,
            &mut transition_state,
            evidence,
            interface,
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
        for resource in interface.resource_ensures() {
            let Some(identity) = resource.instance_identity() else {
                continue;
            };
            let after = if let Some(produced) = produced_instances.get(&identity) {
                produced.clone()
            } else {
                let Some(before) = entry_contract_state.owned_resource_instance(identity) else {
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
                            ResourceFieldType::Integer => {
                                AlgebraicValue::Integer(IntegerTerm::Variable(variable))
                            }
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
                ResourceInstance::new(
                    before.identity,
                    before.name.clone(),
                    before.arguments.clone(),
                    before.schema.clone(),
                    fields,
                )
                .expect("fresh symbolic fields have their declared types")
            };
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
            with_contract_interface_argument_views(&post_state, interface, &argument_values);
        let entry_resource_state =
            with_contract_interface_argument_views(&entry_state, interface, &argument_values);

        let return_resource_timing = crate::instrumentation::OperationTiming::new(
            name,
            "verified function rule application",
            "verified call return resource evaluation",
        );
        let return_resources = match evaluate_contract_return_resources(
            &caller_resources_after_requirements,
            &entry_resource_state,
            &output_resource_state,
            name,
            interface,
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
        transfer.post_outputs = Some(return_resources);
        let return_resources = transfer
            .post_outputs
            .as_ref()
            .expect("the checked transition records post outputs")
            .clone();

        // Lower the ensures before reconciling allocation ownership so the
        // transition can prove exact continuity when the contract states it.
        // An undecided continuity relation remains symbolic in this one call
        // successor; it is not an execution-path split.
        post_state.resources = return_resources.clone();
        let provisional_post_contract_state =
            with_contract_interface_argument_views(&post_state, interface, &argument_values);
        let mut provisional_facts = facts.clone();
        let provisional_ensure_timing = crate::instrumentation::OperationTiming::new(
            name,
            "verified function rule application",
            "verified call provisional ensure lowering",
        );
        add_verified_function_ensure_facts_selected_with_interface(
            &mut provisional_facts,
            &obligations,
            &provisional_post_contract_state,
            &entry_contract_state,
            interface,
            interface.contract_ensures().iter(),
            &effective_assumptions,
            budget,
        )?;
        drop(provisional_ensure_timing);

        let allocation_delta_timing = crate::instrumentation::OperationTiming::new(
            name,
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
            interface,
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
            with_contract_interface_argument_views(&post_state, interface, &argument_values);

        let ensure_timing = crate::instrumentation::OperationTiming::new(
            name,
            "verified function rule application",
            "verified call ensure lowering",
        );
        add_verified_function_ensure_facts_selected_with_interface(
            &mut facts,
            &obligations,
            &post_contract_state,
            &entry_contract_state,
            interface,
            interface.contract_ensures().iter(),
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
            if additional.interface.return_type() != CType::Void {
                set_contract_result(&mut additional_post, additional.interface, result.clone());
            }
            let additional_post = with_contract_interface_argument_views(
                &additional_post,
                additional.interface,
                &additional.argument_values,
            );
            add_verified_function_ensure_facts_selected_with_interface(
                &mut additional_facts,
                &additional.obligations,
                &additional_post,
                &additional.entry_contract_state,
                additional.interface,
                additional
                    .interface
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
        return_state.next_local_lifetime = post_state.next_local_lifetime;
        let outcome = CFunctionOutcome::Return {
            value: result,
            state: return_state,
        };
        if let Some(function) = evidence {
            append_string_literal_loadable_facts(function, &outcome, &mut facts);
        }
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
    /// The nominal callee name used for diagnostics and provenance. It is not
    /// a source-body handle for named callbacks.
    name: &'a str,
    interface_name: &'a str,
    /// Concrete evidence is present only for a verified direct rule. Named
    /// contracts and external assumptions deliberately carry none.
    evidence: Option<&'a CFunction>,
    /// The body-independent interface used to prepare this application. It is
    /// explicit even when it is the concrete function's own interface, so
    /// callback and ordinary calls cannot silently grow separate evaluators.
    interface: &'a CFunctionContractInterface,
    argument_values: Vec<CValue>,
    entry_state: CState,
    entry_contract_state: CState,
    transfer: CFunctionResourceTransfer,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    effective_assumptions: PureFactContext,
    /// The binder map this interface was selected with, if any. A `produces`
    /// binder reads its caller-side identity from exactly this map.
    bindings: Option<std::sync::Arc<BTreeMap<Variable, Variable>>>,
}

/// Finds the exact source snapshot carried by a lowered pure requirement.
/// This is deliberately narrower than the general recursive variable walker:
/// only the logical/condition/bitvector shapes admitted by the source-backed
/// classifier are visited, with the same finite structural budget.
fn source_load_snapshot_for_proposition(
    proposition: &Proposition,
) -> ExecutionResult<Option<CMemorySnapshotIdentity>> {
    const MAX_NODES: usize = 4096;
    enum Work<'a> {
        Proposition(&'a Proposition),
        Condition(&'a ConditionTerm),
        Bitvector(&'a Bitvector32Term),
    }
    let mut work = vec![Work::Proposition(proposition)];
    let mut visited = 0usize;
    let mut snapshot = None;
    while let Some(item) = work.pop() {
        visited = visited.saturating_add(1);
        crate::instrumentation::record_deterministic_work(1);
        if visited > MAX_NODES {
            return Err(ExecutionLimit::ExpressionSteps);
        }
        if crate::kernel::assumptions::reasoning_interrupted() {
            return Err(ExecutionLimit::Deadline);
        }
        match item {
            Work::Proposition(Proposition::ConditionIs(condition, _)) => {
                work.push(Work::Condition(condition));
            }
            Work::Proposition(Proposition::And(left, right))
            | Work::Proposition(Proposition::Or(left, right))
            | Work::Proposition(Proposition::Implies(left, right)) => {
                work.push(Work::Proposition(right));
                work.push(Work::Proposition(left));
            }
            Work::Proposition(Proposition::Not(body))
            | Work::Proposition(Proposition::ForAll { body, .. })
            | Work::Proposition(Proposition::Exists { body, .. }) => {
                work.push(Work::Proposition(body));
            }
            Work::Proposition(_) => return Ok(None),
            Work::Condition(
                ConditionTerm::Bitvector32SignedLessThan(left, right)
                | ConditionTerm::Bitvector32SignedLessEqual(left, right)
                | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
                | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
                | ConditionTerm::Bitvector32Equal(left, right)
                | ConditionTerm::Bitvector64SignedLessThan(left, right)
                | ConditionTerm::Bitvector64SignedLessEqual(left, right)
                | ConditionTerm::Bitvector64SignedGreaterThan(left, right)
                | ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
                | ConditionTerm::Bitvector64UnsignedLessThan(left, right)
                | ConditionTerm::Bitvector64UnsignedLessEqual(left, right)
                | ConditionTerm::Bitvector64UnsignedGreaterThan(left, right)
                | ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right)
                | ConditionTerm::Bitvector64Equal(left, right)
                | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
                | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
                | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
                | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
                | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right)
                | ConditionTerm::Bitvector64SignedAddOverflows(left, right)
                | ConditionTerm::Bitvector64SignedSubtractOverflows(left, right)
                | ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right)
                | ConditionTerm::Bitvector64SignedDivideOverflows(left, right)
                | ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right),
            ) => {
                work.push(Work::Bitvector(right));
                work.push(Work::Bitvector(left));
            }
            Work::Condition(ConditionTerm::Constant(_))
            | Work::Condition(ConditionTerm::Variable(_)) => {}
            Work::Condition(_) => return Ok(None),
            Work::Bitvector(Bitvector32Term::Constant(_))
            | Work::Bitvector(Bitvector32Term::Int64Constant(_))
            | Work::Bitvector(Bitvector32Term::UInt64Constant(_)) => {}
            Work::Bitvector(Bitvector32Term::Variable(variable)) => {
                if crate::kernel::is_load_variable(variable) {
                    let Some((origin, _)) =
                        crate::kernel::registered_load_origin_for_variable(variable)
                    else {
                        return Ok(None);
                    };
                    let identity = CMemorySnapshotIdentity::of(origin.memory());
                    if snapshot.is_some_and(|known| known != identity) {
                        return Ok(None);
                    }
                    snapshot = Some(identity);
                }
            }
            Work::Bitvector(Bitvector32Term::MemoryLoad(memory, _)) => {
                let identity = CMemorySnapshotIdentity::of(memory.memory());
                if snapshot.is_some_and(|known| known != identity) {
                    return Ok(None);
                }
                snapshot = Some(identity);
            }
            Work::Bitvector(
                Bitvector32Term::Add(left, right)
                | Bitvector32Term::Subtract(left, right)
                | Bitvector32Term::Multiply(left, right)
                | Bitvector32Term::Divide(left, right)
                | Bitvector32Term::UnsignedDivide(left, right)
                | Bitvector32Term::Remainder(left, right)
                | Bitvector32Term::UnsignedRemainder(left, right)
                | Bitvector32Term::ShiftLeft(left, right)
                | Bitvector32Term::ArithmeticShiftRight(left, right)
                | Bitvector32Term::LogicalShiftRight(left, right)
                | Bitvector32Term::BitwiseAnd(left, right)
                | Bitvector32Term::BitwiseOr(left, right)
                | Bitvector32Term::BitwiseXor(left, right),
            ) => {
                work.push(Work::Bitvector(right));
                work.push(Work::Bitvector(left));
            }
            Work::Bitvector(Bitvector32Term::BitwiseNot(body)) => {
                work.push(Work::Bitvector(body));
            }
            Work::Bitvector(_) => return Ok(None),
        }
    }
    Ok(snapshot)
}

fn prepare_verified_function_call<'a>(
    caller_state: &CState,
    application: CFunctionContractApplication<'a>,
    candidate_ordinal: usize,
    source_arguments: &[CExpression],
    arguments_path: CArgumentsPath,
    require_established: bool,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
    resource_application: Option<&ResourceCallApplication>,
) -> ExecutionResult<Result<PreparedVerifiedFunctionCall<'a>, CFunctionPath>> {
    let contract_interface = application.interface;
    if contract_interface.contract_requirement_sources().len()
        != contract_interface.contract_requires().len()
    {
        return Ok(Err(CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                "call requirement source map does not match the selected contract".to_string(),
            )),
            facts: arguments_path.facts,
            obligations: arguments_path.obligations,
        }));
    }
    let mut call_requirement_site = None;
    let initial_obligation_count = arguments_path.obligations.len();
    let path_assumptions = assumptions_with_path_context(
        assumptions,
        &arguments_path.facts,
        &arguments_path.obligations,
    );
    let Some((argument_values, argument_obligations)) = coerce_c_contract_arguments(
        contract_interface,
        &arguments_path.values,
        &arguments_path.obligations,
        &path_assumptions,
    ) else {
        return Ok(Err(CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                contract_argument_binding_error(
                    contract_interface,
                    application.name,
                    &arguments_path.values,
                ),
            )),
            facts: arguments_path.facts,
            obligations: arguments_path.obligations,
        }));
    };
    let Some(mut entry_state) = application
        .evidence
        .map(|function| bind_c_function_arguments(caller_state, function, &argument_values))
        .unwrap_or_else(|| {
            bind_c_contract_arguments(caller_state, contract_interface, &argument_values)
        })
    else {
        return Ok(Err(CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                contract_argument_binding_error(
                    contract_interface,
                    application.name,
                    &argument_values,
                ),
            )),
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
        application.name,
        "verified function rule application",
        "verified call resource transfer preparation",
        || {
            prepare_contract_resource_transfer(
                caller_state,
                &entry_state,
                application.name,
                contract_interface,
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
        with_contract_interface_argument_views(&entry_state, contract_interface, &argument_values);

    let mut obligations = argument_obligations;
    let mut facts = arguments_path.facts;
    let mut established_requirements = Vec::new();
    let requirement_timing = crate::instrumentation::OperationTiming::new(
        application.name,
        "verified function rule application",
        "verified call requirement checking",
    );
    for (requirement_ordinal, requirement) in
        contract_interface.contract_requires().iter().enumerate()
    {
        let requirement_assumptions =
            assumptions_with_path_context(&path_assumptions, &facts, &obligations);
        let requirement_assumptions =
            assumptions_with_propositions(&requirement_assumptions, &established_requirements);
        let lowering_assumptions = requirement_assumptions
            .clone()
            .allow_symbolic_contract_loads();
        let mut requirement_source: Option<std::sync::Arc<CallRequirementSource>> = None;
        let source_load_snapshot = std::cell::Cell::new(None);
        let mut source_for_requirement = || {
            if let Some(source) = &requirement_source {
                return source.clone();
            }
            let site = call_requirement_site
                .get_or_insert_with(|| {
                    std::sync::Arc::new(CallRequirementSite::for_requirement(
                        application.name,
                        application.interface_name,
                        candidate_ordinal,
                        source_arguments,
                        &caller_state.memory,
                    ))
                })
                .clone();
            let source = std::sync::Arc::new(CallRequirementSource::new(
                site,
                requirement_ordinal,
                contract_interface
                    .contract_requirement_source(requirement_ordinal)
                    .unwrap_or(None),
                // The interface carries the checked source-map capability;
                // using it keeps this metadata body-independent for named
                // callbacks while matching concrete direct-call metadata.
                contract_interface
                    .contract_requirement_source(requirement_ordinal)
                    .is_some_and(|source_requirement_ordinal| {
                        source_requirement_ordinal.is_some()
                            && spec_proposition_is_state_independent(requirement)
                    }),
                source_load_snapshot.get(),
            ));
            requirement_source = Some(source.clone());
            source
        };
        let requirement_paths = lower_spec_proposition_at_state_with_loop_entry(
            &entry_contract_state,
            requirement,
            Some(&entry_contract_state),
            &lowering_assumptions,
            budget,
        )?;
        let mut load_snapshot = None;
        let mut load_snapshot_consistent = true;
        for requirement_path in &requirement_paths {
            let Some(identity) =
                source_load_snapshot_for_proposition(&requirement_path.proposition)?
            else {
                continue;
            };
            if load_snapshot.is_some_and(|known| known != identity) {
                load_snapshot_consistent = false;
            } else {
                load_snapshot = Some(identity);
            }
        }
        if load_snapshot_consistent {
            source_load_snapshot.set(load_snapshot);
        }
        if requirement_paths.is_empty() {
            obligations.push(
                ProofObligation::verification_condition(false_equals_true_proposition())
                    .with_call_requirement_site(source_for_requirement())
                    .with_context(format!("{} precondition", application.name)),
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
                // The guards this wrap inserts are the obligation's complete
                // recorded head chain: the path obligation under them is a
                // kernel load or overflow condition, which no written
                // connective introduced.
                let (guarded, guard_introductions) = wrap_path_context_with_introductions(
                    path_obligation.proposition().clone(),
                    &requirement_path.facts,
                    &[],
                );
                // Discharge is an exact route or an emitted obligation. A
                // guard the exact routes do not cover is emitted as a
                // required verification condition at the call step,
                // carrying the head chain recorded for it, for the proof
                // side to discharge. The kernel searches for no proof of it.
                if required_obligation_is_exactly_discharged(&requirement_assumptions, &guarded) {
                    super::assumptions::record_reasoning_provenance(
                        &requirement_assumptions,
                        &guarded,
                    );
                } else {
                    let call_requirement_site = source_for_requirement();
                    obligations.push(
                        ProofObligation::verification_condition(guarded.clone())
                            .with_introductions(guard_introductions)
                            .with_call_requirement_site(call_requirement_site.clone())
                            .with_context(format!("{} precondition", application.name)),
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
            // The guards this wrap inserts, then the head chain the
            // requirement's own lowering recorded. The record comes from the
            // lowering that produced the obligation, so an introduction on
            // it reaches a hidden guard exactly as on a lowered goal.
            let requirement_introductions = requirement_path.introductions;
            let (guarded_requirement, guards) = wrap_path_context_with_introductions(
                requirement_path.proposition,
                &requirement_path.facts,
                &requirement_path.obligations,
            );
            let mut introductions = guards;
            introductions.extend(requirement_introductions);
            if !requirement_is_proven {
                // Same rule as the guard above: exact routes, then an
                // emitted required verification condition. The general
                // prover decides no precondition.
                if required_obligation_is_exactly_discharged(
                    &requirement_assumptions,
                    &guarded_requirement,
                ) {
                    super::assumptions::record_reasoning_provenance(
                        &requirement_assumptions,
                        &guarded_requirement,
                    );
                } else {
                    let call_requirement_site = source_for_requirement();
                    obligations.push(
                        ProofObligation::verification_condition(guarded_requirement.clone())
                            .with_introductions(introductions)
                            .with_call_requirement_site(call_requirement_site.clone())
                            .with_context(format!("{} precondition", application.name)),
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

    let call_entry_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
    let effective_assumptions =
        assumptions_with_propositions(&call_entry_assumptions, &established_requirements)
            .transport_memory_load_condition_facts();

    if let Some(function) = application.evidence
        && let Some(undefined_behavior) = verified_call_uninitialized_read(
            &entry_contract_state,
            function,
            &call_entry_assumptions.transport_memory_load_condition_facts(),
            budget,
        )?
    {
        return Ok(Err(CFunctionPath {
            outcome: CFunctionOutcome::UndefinedBehavior(undefined_behavior),
            facts,
            obligations,
        }));
    }

    let footprint_state = entry_contract_state.clone();
    let footprint_timing = crate::instrumentation::OperationTiming::new(
        application.name,
        "verified function rule application",
        "verified call mutable footprint lowering",
    );
    // Reassemble the transition in source order from its role partitions.
    // This keeps the effect projection tied to the checked role-bearing
    // inputs rather than to a normalized context that erased provenance.
    let mut checked_transition_inputs = transfer.borrowed_inputs.clone();
    checked_transition_inputs.extend(transfer.consumed_inputs.clone());
    checked_transition_inputs.sort_by_key(|checked| checked.clause_position);
    let projection = match project_contract_memory_effects(
        &footprint_state,
        contract_interface,
        Some(&checked_transition_inputs),
        &effective_assumptions,
        budget,
    )? {
        Ok(projection) => projection,
        Err(message) => {
            return Ok(Err(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "could not evaluate mutable footprint: {message}"
                ))),
                facts,
                obligations,
            }));
        }
    };
    let mutable_ranges = projection.ranges;
    for fact in projection.evidence_facts {
        if !facts.contains(&fact) {
            facts.push(fact);
        }
    }
    drop(footprint_timing);
    // The projection above is also retained on the transition record below;
    // no later call path reconstructs the footprint from source clauses.
    let mut transfer = transfer;
    transfer.memory_effects = mutable_ranges.clone();
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
        name: application.name,
        interface_name: application.interface_name,
        evidence: application.evidence,
        interface: contract_interface,
        argument_values,
        entry_state,
        entry_contract_state,
        transfer,
        facts,
        obligations,
        effective_assumptions,
        bindings: resource_application.map(|application| application.bindings.clone()),
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
            contract.proof_parameters().is_empty() || selected == Some(contract.name())
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
        if arguments.len() != contract.proof_parameters().len() {
            return Ok(vec![resource_call_failure(
                "resource contract proof argument arity mismatch",
            )]);
        }
        let mut bindings = BTreeMap::new();
        let mut actuals = BTreeSet::new();
        for (parameter, argument) in contract.proof_parameters().iter().zip(arguments) {
            let Some(identity) = parameter.instance_identity() else {
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
                || bindings.insert(identity, instance.identity()).is_some()
            {
                return Ok(vec![resource_call_failure(
                    "duplicate exclusive resource proof argument",
                )]);
            }
        }
        Some(ResourceCallApplication {
            parameters: contract.proof_parameters().to_vec().into(),
            bindings: std::sync::Arc::new(bindings),
        })
    } else {
        None
    };
    let applications = contracts
        .iter()
        .map(|contract| CFunctionContractApplication {
            name: contract.callee_name(),
            interface_name: contract.name(),
            interface: contract.interface(),
            evidence: None,
        })
        .collect::<Vec<_>>();
    execute_verified_function_applications(
        caller_state,
        &applications,
        selected_index,
        selected_index.zip(resource_application.as_ref()),
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

/// Prints the explicit refinement theorem that automatic formation could not
/// replace, with every slot filled from the two declarations the check read.
///
/// The skeleton is the expand affordance of the automatic route. It is built
/// from the same `CFunctionContract` and `CFunction` interfaces the check
/// uses — the target's proof parameters, the implementation's binders, and
/// the implementation's C parameter list — so the printed obligation cannot
/// drift from the one that was refused. A target with no proof parameters
/// gets the `unfold(Name)` form, which is the route that already exists.
///
/// `declared_parameter_spellings` carries, per parameter position, the C
/// spelling the caller's source declaration uses where this interface cannot
/// reconstruct it: an aggregate pointer is a layout here, not a struct tag,
/// so `struct node*` would print as the pointer type it is modeled by. The
/// caller supplies the tag rather than the kernel storing one; a position
/// without a supplied spelling keeps this interface's own.
pub(super) fn named_contract_refinement_theorem_skeleton(
    contract: &CFunctionContract,
    function: &CFunction,
    declared_parameter_spellings: &[Option<String>],
) -> String {
    let theorem = format!(
        "{}_is_{}",
        function.name(),
        snake_case_contract_name(contract.name())
    );
    let parameters = function
        .parameters()
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            let spelling = declared_parameter_spellings
                .get(index)
                .and_then(Option::as_deref)
                .map(str::to_string)
                .unwrap_or_else(|| c_parameter_type_spelling(parameter));
            format!("{spelling} {}", parameter.name())
        })
        .collect::<Vec<_>>()
        .join(", ");
    let target_binders = declared_instance_binder_names(&[contract.proof_parameters()]);
    if target_binders.is_empty() {
        return format!(
            "theorem {theorem}() {{\n    \
             ensures {contract}(&{function}) by {{\n        \
             unfold({contract});\n        \
             simp();\n    \
             }}\n\
             }}",
            contract = contract.name(),
            function = function.name(),
        );
    }
    let implementation_binders = declared_instance_binder_names(&[
        function.resource_requires(),
        function.resource_ensures(),
    ]);
    let introduced =
        introduced_instance_names(target_binders.len().max(implementation_binders.len()));
    let map = |binders: &[String]| {
        binders
            .iter()
            .zip(&introduced)
            .map(|(binder, name)| format!("{binder}: {name}"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let arguments = function
        .parameters()
        .iter()
        .map(|parameter| parameter.name().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "theorem {theorem}() executes {function}({parameters}) {{\n    \
         ensures {contract}(&{function}) as {{ {target} }} by {{\n        \
         step({function}({arguments}), {{ {implementation} }});\n        \
         simp();\n    \
         }}\n\
         }}",
        contract = contract.name(),
        function = function.name(),
        target = map(&target_binders),
        implementation = map(&implementation_binders),
    )
}

/// The binder spellings a declaration introduces, in declaration order, once
/// per identity.
fn declared_instance_binder_names(specs: &[&[CResourceSpec]]) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut names = Vec::new();
    for spec in specs.iter().flat_map(|specs| specs.iter()) {
        let Some(identity) = spec.instance_identity() else {
            continue;
        };
        if seen.insert(identity) {
            names.push(spec.instance_binder().unwrap_or_default().to_string());
        }
    }
    names
}

/// Fresh names for the instances the theorem introduces. One instance is
/// `r`; several are numbered so the two maps can name the same instance.
fn introduced_instance_names(count: usize) -> Vec<String> {
    if count == 1 {
        return vec!["r".to_string()];
    }
    (1..=count).map(|index| format!("r{index}")).collect()
}

fn snake_case_contract_name(name: &str) -> String {
    let mut snake = String::with_capacity(name.len() + 4);
    for (index, character) in name.char_indices() {
        if character.is_uppercase() && index != 0 {
            snake.push('_');
        }
        snake.extend(character.to_lowercase());
    }
    snake
}

/// The C0 spelling of a parameter's declared type.
///
/// Struct tags are not part of the kernel interface: an aggregate parameter
/// keeps its layout, not the tag its source wrote, so a pointer to one is
/// spelled by its pointer type. The skeleton is source the user edits, and
/// this is the one slot they may have to correct.
fn c_parameter_type_spelling(parameter: &CParameter) -> String {
    let base = match parameter.c_type() {
        CType::Void => "void",
        CType::Bool => "bool",
        CType::VoidPointer => "void*",
        CType::Int16 => "int16",
        CType::Int32 => "int32",
        CType::UInt8 => "uint8",
        CType::UInt16 => "uint16",
        CType::UInt32 => "uint32",
        CType::Int64 => "int64",
        CType::UInt64 => "uint64",
        CType::Float32 => "float32",
        CType::Float64 => "float64",
        CType::Int16Pointer => "int16*",
        CType::UInt16Pointer => "uint16*",
        CType::Int32Pointer => "int32*",
        CType::UInt8Pointer => "uint8*",
        CType::UInt32Pointer => "uint32*",
        CType::Int64Pointer => "int64*",
        CType::UInt64Pointer => "uint64*",
        CType::Float32Pointer => "float32*",
        CType::Float64Pointer => "float64*",
        CType::Int16PointerPointer => "int16**",
        CType::UInt16PointerPointer => "uint16**",
        CType::Int32PointerPointer => "int32**",
        CType::UInt8PointerPointer => "uint8**",
        CType::UInt32PointerPointer => "uint32**",
        CType::Int64PointerPointer => "int64**",
        CType::UInt64PointerPointer => "uint64**",
        CType::Float32PointerPointer => "float32**",
        CType::Float64PointerPointer => "float64**",
        CType::FunctionPointer(_) => "void (*)()",
        CType::Int16Array(_) => "int16*",
        CType::Int32Array(_) => "int32*",
        CType::UInt8Array(_) => "uint8*",
        CType::UInt16Array(_) => "uint16*",
        CType::UInt32Array(_) => "uint32*",
        CType::Int64Array(_) => "int64*",
        CType::UInt64Array(_) => "uint64*",
        CType::Float32Array(_) => "float32*",
        CType::Float64Array(_) => "float64*",
    };
    if parameter.pointee_is_constant() {
        format!("const {base}")
    } else {
        base.to_string()
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
    let Some(context) = prepare_automatic_contract_refinement_context(contract, function, budget)
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
    contract_refinement_context_for_checked_interfaces(contract, function, budget)
}

/// The concrete-pointer formation route's context.
///
/// It differs from the explicit route only in admitting a target that
/// declares proof parameters. The instances those parameters stand for are
/// introduced by [`function_refines_named_contract_in_case`], and only when
/// the binding between the two declarations is forced.
fn prepare_automatic_contract_refinement_context(
    contract: &CFunctionContract,
    function: &CFunction,
    budget: &mut ExecutionBudget,
) -> Option<CFunctionContractRefinementContext> {
    if !contract.has_compatible_signature_and_composite_vocabulary(function) {
        return None;
    }
    contract_refinement_context_for_checked_interfaces(contract, function, budget)
}

fn contract_refinement_context_for_checked_interfaces(
    contract: &CFunctionContract,
    function: &CFunction,
    budget: &mut ExecutionBudget,
) -> Option<CFunctionContractRefinementContext> {
    contract_refinement_context_for_interface(
        contract,
        function.name(),
        function.contract_interface(),
        budget,
    )
}

pub(super) fn contract_refinement_context_for_interface(
    contract: &CFunctionContract,
    function_name: &str,
    function_interface: &CFunctionContractInterface,
    budget: &mut ExecutionBudget,
) -> Option<CFunctionContractRefinementContext> {
    let mut argument_values = Vec::with_capacity(function_interface.parameters().len());
    for parameter in function_interface.parameters() {
        let variable = Variable(budget.next_kernel_variable);
        budget.next_kernel_variable = budget.next_kernel_variable.wrapping_add(1);
        argument_values.push(symbolic_call_result(parameter.c_type(), variable));
    }
    let result_variable = Variable(budget.next_kernel_variable);
    budget.next_kernel_variable = budget.next_kernel_variable.wrapping_add(1);
    Some(CFunctionContractRefinementContext {
        contract: contract.clone(),
        function_interface: function_interface.clone(),
        function_name: function_name.to_string(),
        pointer: CPointerValue::new(
            Pointer {
                block: PointerBlock::Function(function_name.to_string()),
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
    with_contract_interface_argument_views(
        &CState::new(),
        &context.contract.interface,
        &context.argument_values,
    )
}

pub(super) fn prepare_contract_refinement_obligations(
    context: &CFunctionContractRefinementContext,
) -> Option<CFunctionContractRefinementObligations> {
    let target = context.contract.interface();
    let source = &context.function_interface;
    let mut budget = ExecutionBudget {
        next_kernel_variable: context.next_kernel_variable,
        ..ExecutionBudget::default()
    };
    let entry = function_contract_refinement_entry_state(context);
    let source_entry =
        with_contract_interface_argument_views(&CState::new(), source, &context.argument_values);
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
    let ranges = evaluate_contract_mutable_ranges_for_interface(
        source,
        &source_entry,
        &assumptions,
        &mut budget,
        false,
    )
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
        set_contract_result(&mut post, target, result.clone());
        set_contract_result(&mut source_post, source, result);
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
        interface: &CFunctionContractInterface,
        specs: &[SpecProposition],
        state: &CState,
        entry: &CState,
        budget: &mut ExecutionBudget,
    ) -> Option<Proposition> {
        let definitions = interface
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

/// One forced pair of resource declarations: a target contract proof
/// parameter and the implementation binder that must stand for it. Both sides
/// read the same instance identity, so `root.model` on the named side and
/// `t.model` on the implementation side lower to the same term.
struct RefinementInstanceBinding {
    target_identity: Variable,
    implementation_identity: Variable,
    entry: ResourceInstance,
    post: ResourceInstance,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum RefinementSide {
    Target,
    Implementation,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum RefinementPhase {
    Entry,
    Post,
}

/// One declared instance binder, with its family evaluated at the state that
/// declares it.
struct DeclaredResourceInstance {
    identity: Variable,
    family: String,
    schema: ResourceFieldSchema,
    arguments: ResourceArguments,
}

/// Collects the instance binders a declaration names, in declaration order,
/// once per identity. `owns` states the same binder in `requires` and
/// `ensures`; the pair is one binder, not two.
fn evaluate_declared_resource_instances(
    specs: &[&[CResourceSpec]],
    state: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<DeclaredResourceInstance>>> {
    let mut seen = BTreeSet::new();
    let mut declared = Vec::new();
    for spec in specs.iter().flat_map(|specs| specs.iter()) {
        let Some(identity) = spec.instance_identity() else {
            continue;
        };
        if !seen.insert(identity) {
            continue;
        }
        let Some(schema) = spec.instance_schema() else {
            continue;
        };
        let Some(resource) = spec.instance_resource_spec() else {
            continue;
        };
        let instance = match evaluate_function_resource_spec(state, &resource, assumptions, budget)?
        {
            Ok(CResourceFact::Own(CResource::Composite { name, arguments }, quantity))
                if quantity.as_const() == Some(1) =>
            {
                DeclaredResourceInstance {
                    identity,
                    family: name,
                    schema: schema.clone(),
                    arguments,
                }
            }
            Ok(_) | Err(_) => return Ok(None),
        };
        declared.push(instance);
    }
    Ok(Some(declared))
}

/// Indexes declared binders by resource family. A family that appears twice
/// on one side leaves the binding unforced, so its entry is poisoned rather
/// than ranked.
fn index_declared_instances_by_family(
    declared: &[DeclaredResourceInstance],
) -> Option<BTreeMap<&str, &DeclaredResourceInstance>> {
    let mut index = BTreeMap::new();
    for instance in declared {
        if index.insert(instance.family.as_str(), instance).is_some() {
            return None;
        }
    }
    Some(index)
}

/// Pairs the target contract's proof parameters with the implementation's
/// binders when exactly one pairing is possible, and instantiates one shared
/// instance per pair.
///
/// The pairing is a map lookup per binder: each side is indexed by resource
/// family once, a repeated family on either side refuses, and the two indexes
/// must have the same keys. No candidate is searched, scored, or preferred.
///
/// Each pair gets one entry instance with arbitrary fields, shared by both
/// entry states, and one post instance with fresh arbitrary fields, shared by
/// both post states. Fresh post fields are the same rule an ordinary call
/// applies to returned ownership: the identity survives, the field values do
/// not, and only the implementation's guarantees relate the two.
fn forced_refinement_instance_bindings(
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
    contract_entry: &CState,
    function_entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<RefinementInstanceBinding>>> {
    let Some(target) = evaluate_declared_resource_instances(
        &[contract.proof_parameters()],
        contract_entry,
        assumptions,
        budget,
    )?
    else {
        return Ok(None);
    };
    let Some(implementation) = evaluate_declared_resource_instances(
        &[function.resource_requires(), function.resource_ensures()],
        function_entry,
        assumptions,
        budget,
    )?
    else {
        return Ok(None);
    };
    if target.is_empty() && implementation.is_empty() {
        return Ok(Some(Vec::new()));
    }
    let (Some(target_index), Some(implementation_index)) = (
        index_declared_instances_by_family(&target),
        index_declared_instances_by_family(&implementation),
    ) else {
        return Ok(None);
    };
    if target_index.len() != implementation_index.len() {
        return Ok(None);
    }
    let mut bindings = Vec::with_capacity(target_index.len());
    for (family, target) in &target_index {
        let Some(implementation) = implementation_index.get(family) else {
            return Ok(None);
        };
        if target.schema != implementation.schema
            || target.arguments.len() != implementation.arguments.len()
            || !target
                .arguments
                .iter()
                .zip(implementation.arguments.iter())
                .all(|(left, right)| {
                    crate::kernel::resource_arguments_proven_equal(left, right, assumptions)
                })
        {
            return Ok(None);
        }
        let identity = Variable(budget.next_kernel_variable);
        budget.next_kernel_variable = budget.next_kernel_variable.wrapping_add(1);
        let instance = |budget: &mut ExecutionBudget| {
            let fields = arbitrary_resource_instance_fields(&target.schema, budget);
            ResourceInstance::new(
                identity,
                target.family.clone(),
                target.arguments.clone(),
                target.schema.clone(),
                fields,
            )
            .expect("arbitrary fields have their declared types")
        };
        bindings.push(RefinementInstanceBinding {
            target_identity: target.identity,
            implementation_identity: implementation.identity,
            entry: instance(budget),
            post: instance(budget),
        });
    }
    Ok(Some(bindings))
}

pub(super) fn arbitrary_resource_instance_fields(
    schema: &ResourceFieldSchema,
    budget: &mut ExecutionBudget,
) -> ResourceArguments {
    schema
        .fields()
        .iter()
        .map(|(_, field_type)| {
            let variable = Variable(budget.next_kernel_variable);
            budget.next_kernel_variable = budget.next_kernel_variable.wrapping_add(1);
            match field_type {
                ResourceFieldType::Integer => {
                    AlgebraicValue::Integer(IntegerTerm::Variable(variable))
                }
                ResourceFieldType::C(c_type) => {
                    AlgebraicValue::C(symbolic_call_result(*c_type, variable))
                }
                ResourceFieldType::Algebraic(algebraic_type) => {
                    AlgebraicValue::Algebraic(AlgebraicTerm {
                        algebraic_type: algebraic_type.clone(),
                        node: AlgebraicTermNode::Variable(variable),
                    })
                }
            }
        })
        .collect()
}

/// Installs the shared instances one side reads, under the identities that
/// side's declaration wrote.
fn state_with_refinement_instances(
    state: &CState,
    bindings: &[RefinementInstanceBinding],
    side: RefinementSide,
    phase: RefinementPhase,
    assumptions: &PureFactContext,
) -> Option<CState> {
    if bindings.is_empty() {
        return Some(state.clone());
    }
    let mut state = state.clone();
    let mut names = BTreeMap::new();
    let mut facts = Vec::with_capacity(bindings.len());
    for binding in bindings {
        let declared = match side {
            RefinementSide::Target => binding.target_identity,
            RefinementSide::Implementation => binding.implementation_identity,
        };
        let instance = match phase {
            RefinementPhase::Entry => &binding.entry,
            RefinementPhase::Post => &binding.post,
        };
        names.insert(declared, instance.identity());
        facts.push(CResourceFact::own(CResource::Instance(instance.clone())));
    }
    state.resource_bindings = Some(std::sync::Arc::new(names));
    state.resources = state
        .resources
        .clone()
        .try_compose_into_valid_context_delaying_normalization(facts, assumptions)
        .ok()?;
    Some(state)
}

fn function_refines_named_contract_in_case(
    context: &CFunctionContractRefinementContext,
    case_assumptions: &[Proposition],
    unfolded_predicates: &BTreeSet<String>,
    explicit_case: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    let contract = &context.contract;
    let function_interface = &context.function_interface;
    let contract_interface = contract.interface();
    if !predicate_interfaces_are_explicitly_compatible(
        contract_interface,
        function_interface,
        unfolded_predicates,
    ) {
        return Ok(false);
    }
    let mut propositions = contract_interface
        .contract_requires()
        .iter()
        .chain(contract_interface.contract_ensures())
        .chain(function_interface.contract_requires())
        .chain(function_interface.contract_ensures());
    let state_independent = propositions
        .clone()
        .all(spec_proposition_is_state_independent);
    let supported_syntax = propositions.all(spec_proposition_supports_stateful_memory_refinement);
    let supported_stateful_memory = !state_independent
        && !contract_interface.resource_requires().is_empty()
        && !contract_interface.resource_ensures().is_empty()
        && (!contract_interface.contract_mutable().is_empty()
            || contract_interface.resource_derived_mutable_frame())
        && supported_syntax;
    if !state_independent && !supported_stateful_memory {
        return Ok(false);
    }

    let contract_frame = with_contract_interface_argument_views(
        &CState::new(),
        contract_interface,
        &context.argument_values,
    );
    let function_frame = with_contract_interface_argument_views(
        &CState::new(),
        function_interface,
        &context.argument_values,
    );
    // Resource arguments are written over the two parameter lists, which the
    // views above already bind, so the pairing is decided before either
    // contract's own requirements are assumed.
    let Some(instances) = forced_refinement_instance_bindings(
        contract_interface,
        function_interface,
        &contract_frame,
        &function_frame,
        &PureFactContext::new(),
        budget,
    )?
    else {
        return Ok(false);
    };
    let install = |state: &CState, side, phase| {
        state_with_refinement_instances(state, &instances, side, phase, &PureFactContext::new())
    };
    let (Some(contract_entry), Some(function_entry)) = (
        install(
            &contract_frame,
            RefinementSide::Target,
            RefinementPhase::Entry,
        ),
        install(
            &function_frame,
            RefinementSide::Implementation,
            RefinementPhase::Entry,
        ),
    ) else {
        return Ok(false);
    };
    let mut preconditions = PureFactContext::new();
    if !assume_contract_propositions(
        &contract_entry,
        &contract_entry,
        contract_interface.contract_requires(),
        &mut preconditions,
        budget,
    )? {
        return Ok(false);
    }
    preconditions = assumptions_with_propositions(&preconditions, case_assumptions);
    if !prove_contract_propositions(
        &function_entry,
        &function_entry,
        function_interface.contract_requires(),
        &mut preconditions,
        budget,
    )? {
        return Ok(false);
    }

    let post_memory = if state_independent {
        contract_entry.memory().clone()
    } else {
        let memory_variable = Variable(budget.next_kernel_variable);
        budget.next_kernel_variable = budget.next_kernel_variable.wrapping_add(1);
        let mutable_ranges = if explicit_case {
            let Some(ranges) = evaluate_decided_contract_mutable_ranges_for_interface(
                function_interface,
                &function_entry,
                &preconditions,
                budget,
            )?
            else {
                return Ok(false);
            };
            ranges
        } else {
            let Some(ranges) = evaluate_contract_mutable_ranges_for_interface(
                contract_interface,
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
    let result = symbolic_contract_result(function_interface, context.result_variable);
    // The post states carry the post instances, so a guarantee written over
    // `t.model` reads the fields the call produced while `old(t.model)` still
    // reads the entry fields through the entry state passed alongside.
    let (Some(mut contract_post), Some(mut function_post)) = (
        install(
            &contract_frame.clone().with_memory(post_memory.clone()),
            RefinementSide::Target,
            RefinementPhase::Post,
        ),
        install(
            &function_frame.clone().with_memory(post_memory),
            RefinementSide::Implementation,
            RefinementPhase::Post,
        ),
    ) else {
        return Ok(false);
    };
    if function_interface.return_type() != CType::Void {
        set_contract_result(&mut contract_post, contract_interface, result.clone());
        set_contract_result(&mut function_post, function_interface, result);
    }
    if !compatible_resource_and_effect_interfaces(
        contract_interface,
        function_interface,
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
        function_interface.contract_ensures(),
        &mut postconditions,
        budget,
    )? {
        return Ok(false);
    }
    prove_contract_propositions(
        &contract_post,
        &contract_entry,
        contract_interface.contract_ensures(),
        &mut postconditions,
        budget,
    )
}

/// Predicate bodies are stored as checked, normalized contract propositions,
/// while `predicate_unfoldings` retains their opaque surface identities. Equal
/// unfolding tables need no proof action. Every entry present on only one side
/// must otherwise have its predicate name explicitly opened by the proof.
fn predicate_interfaces_are_explicitly_compatible(
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
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

/// Writes to file-scope or static storage that a checked path performs outside
/// the contract's owned footprint, described for diagnostics. The caller may
/// pass the checked resource facts from certification; this keeps the storage
/// decision on the same transition artifact as modular effects. `None` is
/// retained for explicit-effect callers. Caller memory reached through a
/// pointer is checked by the resource transition at each store; storage is
/// not external memory, so a contract that declares resources but no effect
/// clause is framed here instead: its storage writes must lie inside the owned
/// ranges (startup resources, owned raw ranges, and composite bodies).
pub(crate) fn storage_writes_outside_owned_footprint(
    contract: &CFunction,
    entry: &CState,
    facts: &[ExecutionPureFact],
    assumptions: &PureFactContext,
    transition_resources: Option<&[CCheckedResourceFact]>,
) -> ExecutionResult<Option<Vec<String>>> {
    let is_storage = |pointer: &Pointer| {
        pointer.block.starts_with("global:") || pointer.block.starts_with("static:")
    };
    let storage_writes: Vec<Pointer> =
        crate::kernel::reasoning::memory_effect_write_pointers(facts)
            .into_iter()
            .filter(is_storage)
            .collect();
    let storage_summaries: Vec<&CMemoryRange> = facts
        .iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::CMemoryEffectSummary { mutable_ranges, .. } => Some(mutable_ranges),
            _ => None,
        })
        .flatten()
        .filter(|range| is_storage(range.base()))
        .collect();
    // Most contracts never touch storage; do not evaluate their owned
    // footprint at all.
    if storage_writes.is_empty() && storage_summaries.is_empty() {
        return Ok(Some(Vec::new()));
    }
    let mut budget = ExecutionBudget::default();
    let owned = match project_contract_memory_effects(
        entry,
        contract.contract_interface(),
        transition_resources,
        assumptions,
        &mut budget,
    )? {
        Ok(projection) => projection.ranges().to_vec(),
        Err(_) => return Ok(None),
    };
    let mut outside = Vec::new();
    for pointer in &storage_writes {
        let covered = owned.iter().any(|range| {
            super::assumptions::pointer_in_memory_range_shallow(pointer, range)
                || assumptions.pointer_in_range_by_shallow_fact_graph_with_width(
                    pointer,
                    range.base(),
                    range.start(),
                    range.end(),
                    range.element_width(),
                )
        });
        if !covered {
            outside.push(format!("{pointer:?}"));
        }
    }
    for range in storage_summaries {
        if !owned
            .iter()
            .any(|parent| super::assumptions::memory_range_shallowly_contained(range, parent))
        {
            outside.push(format!("{range:?}"));
        }
    }
    Ok(Some(outside))
}

/// Project the checked resource transition's memory effects.  This is the
/// only kernel derivation of a contract write footprint: callers consume the
/// ranges and the checked load facts together, while the surface summary is
/// only source metadata used to construct the interface.
pub(crate) fn project_contract_memory_effects(
    entry: &CState,
    interface: &CFunctionContractInterface,
    transition_resources: Option<&[CCheckedResourceFact]>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CFunctionMemoryEffectProjection, String>> {
    project_contract_memory_effects_with_guard_policy(
        entry,
        interface,
        transition_resources,
        assumptions,
        budget,
        false,
    )
}

/// Evaluate explicit effect segments once for both call projection and
/// refinement containment.  Refinement may require guards to be decided;
/// ordinary call projection keeps an undecided guard conservatively active.
fn project_explicit_memory_segments(
    entry: &CState,
    segments: &[CMemorySegment],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    require_decided_guards: bool,
) -> ExecutionResult<Result<(Vec<CMemoryRange>, Vec<ExecutionPureFact>), String>> {
    let mut projection_assumptions = assumptions.clone();
    let mut ranges = Vec::new();
    let mut evidence_facts = Vec::new();
    for segment in segments {
        if let Some(guard) = segment.guard() {
            match evaluate_guarded_contract_condition(guard, entry, &projection_assumptions, budget)
            {
                Some(true) => {}
                Some(false) => continue,
                None if require_decided_guards => {
                    return Ok(Err("mutable footprint guard is undecided".to_string()));
                }
                None => {}
            }
        }
        match evaluate_loop_effect_segment_with_facts(
            entry,
            segment,
            &projection_assumptions,
            budget,
        )? {
            Ok((segment, facts)) => {
                projection_assumptions =
                    assumptions_with_path_context(&projection_assumptions, &facts, &[]);
                evidence_facts.extend(facts);
                let range = canonical_memory_range(CMemoryRange::new_with_element_width(
                    segment.base,
                    segment.start,
                    segment.end,
                    segment.element_width,
                ));
                if !ranges.contains(&range) {
                    ranges.push(range);
                }
            }
            Err(message) => return Ok(Err(message)),
        }
    }
    Ok(Ok((ranges, evidence_facts)))
}

pub(crate) fn project_contract_memory_effects_with_guard_policy(
    entry: &CState,
    interface: &CFunctionContractInterface,
    transition_resources: Option<&[CCheckedResourceFact]>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    require_decided_guards: bool,
) -> ExecutionResult<Result<CFunctionMemoryEffectProjection, String>> {
    if interface.resource_derived_mutable_frame() && interface.resource_derived_frame_mixed() {
        return Ok(Err(
            "resource-derived mutable frame mixes explicit effect segments".to_string(),
        ));
    }
    let evaluated_transition;
    let transition_resources = if interface.resource_derived_mutable_frame() {
        match transition_resources {
            Some(resources) => Some(resources),
            None => {
                evaluated_transition = match evaluate_function_resource_context_with_metadata(
                    entry,
                    interface.resource_requires(),
                    interface.composite_resource_definitions(),
                    assumptions,
                    budget,
                )? {
                    Ok((_, checked)) => checked,
                    Err(error) => {
                        return Ok(Err(format!(
                            "could not evaluate resource transition: {error:?}"
                        )));
                    }
                };
                Some(evaluated_transition.as_slice())
            }
        }
    } else {
        None
    };
    if transition_resources.is_some_and(|resources| {
        resources.iter().any(|checked| {
            checked.role == CResourceTransferRole::Produce
                || checked.snapshot == CResourceSnapshot::Post
                || (checked.fact.is_view() && checked.role != CResourceTransferRole::Borrow)
        })
    }) {
        return Ok(Err(
            "resource transition contains an inconsistent transfer role".to_string(),
        ));
    }
    let mut ranges = Vec::with_capacity(
        interface.contract_mutable().len()
            + transition_resources.map_or(0, <[CCheckedResourceFact]>::len),
    );
    let mut evidence_facts = Vec::new();
    if interface.resource_derived_mutable_frame()
        && let Some(resources) = transition_resources
    {
        for checked in resources {
            // Borrowing is a boundary role, not an access-mode rewrite:
            // `requires owns p` paired with `ensures borrowed p` still gives
            // the body write authority for the entry-selected range.
            if !checked.fact.is_own() {
                continue;
            }
            let singleton = ResourceContext::new().unchecked_with_fact(checked.fact.clone());
            let Some(expanded) = expand_all_composite_resource_facts(
                &singleton,
                interface.composite_resource_definitions(),
                entry.memory(),
                assumptions,
            ) else {
                return Ok(Err(
                    "could not expand the checked resource transition".to_string()
                ));
            };
            for range in expanded.facts().iter().filter_map(|fact| {
                let range = fact.memory_own_range()?;
                Some(canonical_memory_range(range.clone()))
            }) {
                if !ranges.contains(&range) {
                    ranges.push(range);
                }
            }
        }
    }
    // Resource-derived contracts get their memory authority exclusively from
    // the checked transition above.  The surface `contract_mutable` list is
    // a body-proof/read-only diagnostic projection and must not be another
    // modular-call source.  Functions without resource clauses retain their
    // explicit effect segments here.
    let explicit_segments = if !interface.resource_derived_mutable_frame() {
        interface.contract_mutable()
    } else {
        &[]
    };
    let (explicit_ranges, explicit_evidence) = match project_explicit_memory_segments(
        entry,
        explicit_segments,
        assumptions,
        budget,
        require_decided_guards,
    )? {
        Ok(result) => result,
        Err(message) => return Ok(Err(message)),
    };
    ranges.extend(explicit_ranges);
    evidence_facts.extend(explicit_evidence);
    Ok(Ok(CFunctionMemoryEffectProjection {
        ranges,
        evidence_facts,
    }))
}

/// Check that retained inherited loop-frame metadata is exactly the checked
/// resource-derived effect. The loop lowering keeps source expressions because
/// it must re-evaluate dependent addresses at each back edge; this gate makes
/// that metadata a checked view of the same entry transition rather than an
/// independent source of memory authority.
pub(crate) fn validate_resource_derived_loop_frames(
    function: &CFunction,
    entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(), String>> {
    fn has_inherited_loop_frame(statement: &CStatement) -> bool {
        match statement {
            CStatement::Seq(first, second) => {
                has_inherited_loop_frame(first) || has_inherited_loop_frame(second)
            }
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => has_inherited_loop_frame(then_branch) || has_inherited_loop_frame(else_branch),
            CStatement::While {
                effect_checks,
                body,
                ..
            } => {
                effect_checks.iter().any(|check| {
                    check
                        .context()
                        .is_some_and(|context| context.contains("inherited owned resource frame"))
                }) || has_inherited_loop_frame(body)
            }
            CStatement::Switch { cases, .. } => cases
                .iter()
                .any(|case| has_inherited_loop_frame(&case.body)),
            CStatement::ContinueWithStep { step } => has_inherited_loop_frame(step),
            _ => false,
        }
    }
    if !function.resource_derived_mutable_frame() || !has_inherited_loop_frame(function.body()) {
        return Ok(Ok(()));
    }
    let projection = match project_contract_memory_effects(
        entry,
        function.contract_interface(),
        None,
        assumptions,
        budget,
    )? {
        Ok(projection) => projection,
        Err(message) => return Ok(Err(message)),
    };
    fn check_statement(
        statement: &CStatement,
        entry: &CState,
        assumptions: &PureFactContext,
        budget: &mut ExecutionBudget,
        expected: &[CMemoryRange],
    ) -> ExecutionResult<Result<(), String>> {
        let mut check = |checks: &[CLoopEffectCheck]| -> ExecutionResult<Result<(), String>> {
            for effect_check in checks {
                if !effect_check
                    .context()
                    .is_some_and(|context| context.contains("inherited owned resource frame"))
                {
                    continue;
                }
                let CLoopEffect::Mutable(segments) = effect_check.effect() else {
                    return Ok(Err(
                        "resource-derived loop frame lost its mutable metadata".to_string()
                    ));
                };
                let Ok((actual, _)) =
                    project_explicit_memory_segments(entry, segments, assumptions, budget, false)?
                else {
                    return Ok(Err(
                        "could not evaluate inherited resource-derived loop frame".to_string(),
                    ));
                };
                // Resource definitions may split one logical range across
                // adjacent members while the source-oriented collector keeps
                // those members separate. Coalesce only adjacent ranges with
                // the same base and element width before checking equality;
                // this is a derived normalization, not another authority.
                let coalesce = |mut ranges: Vec<CMemoryRange>| {
                    ranges.sort_by(|left, right| {
                        left.base
                            .cmp(&right.base)
                            .then_with(|| left.start.cmp(&right.start))
                            .then_with(|| left.end.cmp(&right.end))
                    });
                    let mut merged: Vec<CMemoryRange> = Vec::with_capacity(ranges.len());
                    for range in ranges {
                        if let Some(previous) = merged.last_mut()
                            && previous.base == range.base
                            && previous.element_width == range.element_width
                            && previous.end == range.start
                        {
                            previous.end = range.end;
                        } else {
                            merged.push(range);
                        }
                    }
                    merged
                };
                let actual = coalesce(actual);
                let expected = coalesce(expected.to_vec());
                let equivalent = |left: &[CMemoryRange], right: &[CMemoryRange]| {
                    left.iter().all(|range| {
                        right
                            .iter()
                            .any(|candidate| memory_range_covers(candidate, range, assumptions))
                    })
                };
                if !equivalent(&actual, &expected) || !equivalent(&expected, &actual) {
                    return Ok(Err(
                        "inherited loop frame disagrees with checked resource effect".to_string(),
                    ));
                }
            }
            Ok(Ok(()))
        };
        match statement {
            CStatement::Seq(first, second) => {
                if let Err(error) = check_statement(first, entry, assumptions, budget, expected)? {
                    return Ok(Err(error));
                }
                check_statement(second, entry, assumptions, budget, expected)
            }
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                if let Err(error) =
                    check_statement(then_branch, entry, assumptions, budget, expected)?
                {
                    return Ok(Err(error));
                }
                check_statement(else_branch, entry, assumptions, budget, expected)
            }
            CStatement::While {
                effect_checks,
                body,
                ..
            } => {
                if let Err(error) = check(effect_checks)? {
                    return Ok(Err(error));
                }
                check_statement(body, entry, assumptions, budget, expected)
            }
            CStatement::Switch { cases, .. } => {
                for case in cases {
                    if let Err(error) =
                        check_statement(&case.body, entry, assumptions, budget, expected)?
                    {
                        return Ok(Err(error));
                    }
                }
                Ok(Ok(()))
            }
            CStatement::ContinueWithStep { step } => {
                check_statement(step, entry, assumptions, budget, expected)
            }
            _ => Ok(Ok(())),
        }
    }
    check_statement(
        function.body(),
        entry,
        assumptions,
        budget,
        projection.ranges(),
    )
}

fn evaluate_contract_mutable_ranges_for_interface(
    interface: &CFunctionContractInterface,
    entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    require_unguarded: bool,
) -> ExecutionResult<Option<Vec<CMemoryRange>>> {
    if require_unguarded
        && interface
            .contract_mutable()
            .iter()
            .any(|s| s.guard().is_some())
    {
        return Ok(None);
    }
    Ok(
        match project_contract_memory_effects(entry, interface, None, assumptions, budget)? {
            Ok(projection) => Some(projection.ranges),
            Err(_) => None,
        },
    )
}

/// Evaluates exactly the concrete ranges active in one explicit proof case.
///
/// Unlike automatic refinement, this never branches over a guard. Every guard
/// must already be decided by the named preconditions and the proof's written
/// case assumptions. A false guard contributes no possible write; a true guard
/// contributes its ordinary evaluated range.
/// No reaching fixture exists, and none can be written today: the only
/// caller is `function_refines_named_contract_in_case`'s `explicit_case`
/// branch, and its one call site passes `explicit_case: false`. The guard
/// decision below is route-restricted with the rest of package 10(b) so the
/// branch cannot come back carrying a proof search, but its behaviour is
/// unobserved by both fixture harnesses.
fn evaluate_decided_contract_mutable_ranges_for_interface(
    interface: &CFunctionContractInterface,
    entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<CMemoryRange>>> {
    let mut guard_assumptions = assumptions.clone();
    let Some(guards) = lower_refinement_mutable_guards_for_interface(
        interface,
        entry,
        &mut guard_assumptions,
        budget,
    )?
    else {
        return Ok(None);
    };
    let mut ranges = Vec::with_capacity(interface.contract_mutable().len());
    for (segment, guard) in interface.contract_mutable().iter().zip(guards) {
        if let Some(guard) = guard {
            // A refined mutable segment is included, dropped, or leaves the
            // whole footprint undecided. The decision uses the exact routes
            // only; an undecided guard refuses the refinement rather than
            // being settled by a proof search over the ambient context.
            match guard_value_by_exact_routes(&guard_assumptions, &guard) {
                Some(false) => continue,
                Some(true) => {}
                None => return Ok(None),
            }
        }
        let Ok((mut projected, _)) = project_explicit_memory_segments(
            entry,
            std::slice::from_ref(segment),
            &guard_assumptions,
            budget,
            true,
        )?
        else {
            return Ok(None);
        };
        let Some(range) = projected.pop() else {
            return Ok(None);
        };
        ranges.push(range);
    }
    Ok(Some(ranges))
}

fn compatible_resource_and_effect_interfaces(
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
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
    mutable_footprint_is_compatible_for_interfaces(
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
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
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
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
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
        let contract_state = match contract_resource.snapshot() {
            CResourceSnapshot::Entry => contract_entry,
            CResourceSnapshot::Current | CResourceSnapshot::Post => contract_post,
        };
        let contract_resource = match evaluate_function_resource_spec(
            contract_state,
            contract_resource,
            assumptions,
            budget,
        )? {
            Ok(resource) => resource,
            Err(_) => return Ok(false),
        };
        let function_state = match function_resource.snapshot() {
            CResourceSnapshot::Entry => function_entry,
            CResourceSnapshot::Current | CResourceSnapshot::Post => function_post,
        };
        let function_resource = match evaluate_function_resource_spec(
            function_state,
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
    if resource.is_instance() {
        return resource
            .instance_resource_spec()
            .is_some_and(|inner| resource_spec_supports_framed_refinement(&inner));
    }
    matches!(
        resource.family(),
        ResourceFamily::Memory | ResourceFamily::Composite | ResourceFamily::Token
    )
}

fn evaluate_refinement_resource_context(
    state: &CState,
    resources: &[CResourceSpec],
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<ResourceContext>> {
    Ok(
        (evaluate_function_resource_context(state, resources, definitions, assumptions, budget)?)
            .ok(),
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
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
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
        contract.composite_resource_definitions(),
        assumptions,
        budget,
    )?
    else {
        return Ok(false);
    };
    let Some(function_requires) = evaluate_refinement_resource_context(
        function_entry,
        function.resource_requires(),
        function.composite_resource_definitions(),
        assumptions,
        budget,
    )?
    else {
        return Ok(false);
    };
    let Some(function_ensures) = evaluate_refinement_resource_context(
        function_post,
        function.resource_ensures(),
        function.composite_resource_definitions(),
        assumptions,
        budget,
    )?
    else {
        return Ok(false);
    };
    let Some(contract_ensures) = evaluate_refinement_resource_context(
        contract_post,
        contract.resource_ensures(),
        contract.composite_resource_definitions(),
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

/// Checks that every range the implementation may write lies inside the
/// target's checked effect projection. Both projections are built from the
/// same transition/effect evaluator: resource-derived interfaces evaluate
/// their entry resource clauses into role-bearing facts, while explicit
/// interfaces evaluate their guarded segments. Surface `contract_mutable`
/// metadata is never walked as the semantic comparison itself.
///
/// Both guard questions are decided by [`refinement_route_proves`]: exact
/// membership in the refinement assumptions, or the frozen condition checker
/// on a bare condition. A guard this cannot settle is treated as unsettled,
/// which refuses the refinement rather than widening the checked footprint.
/// There is no proof site here to receive an obligation instead: this is a
/// boolean gate on a kernel-formed contract fact, so refusing is the
/// conservative equivalent of emitting one.
///
/// The walk over the contract's declared segments is not a selection. Its only
/// result is whether some declared segment covers the required range; no later
/// check consults which one, and a corpus probe (both fixture harnesses, plus
/// `c_named_contract_refinement_selects_guarded_segment`) found exactly one
/// covering segment at every reached site. So this is a discharge, and a
/// finite disjunction over the declared segments would spell a choice that
/// nothing consumes.
fn mutable_footprint_is_compatible_for_interfaces(
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
    contract_entry: &CState,
    function_entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if !contract.resource_derived_mutable_frame()
        && !function.resource_derived_mutable_frame()
        && (contract
            .contract_mutable()
            .iter()
            .any(|segment| segment.guard().is_some())
            || function
                .contract_mutable()
                .iter()
                .any(|segment| segment.guard().is_some()))
    {
        return explicit_refinement_effects_are_compatible(
            contract,
            function,
            contract_entry,
            function_entry,
            assumptions,
            budget,
        );
    }
    let contract_projection =
        project_refinement_effects(contract, contract_entry, assumptions, budget)?;
    let function_projection =
        project_refinement_effects(function, function_entry, assumptions, budget)?;
    let (Ok(contract_projection), Ok(function_projection)) =
        (contract_projection, function_projection)
    else {
        return Ok(false);
    };
    Ok(function_projection.ranges().iter().all(|required_range| {
        contract_projection.ranges().iter().any(|available_range| {
            memory_range_covers(available_range, required_range, assumptions)
        })
    }))
}

/// Guarded explicit effects need one projection per implementation guard: the
/// implementation's guard is the active path assumption, while a target guard
/// must already be established on that path. Range lowering itself still goes
/// through the shared projection evaluator.
fn explicit_refinement_effects_are_compatible(
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
    contract_entry: &CState,
    function_entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    let mut guard_assumptions = assumptions.clone();
    let Some(contract_guards) = lower_refinement_mutable_guards_for_interface(
        contract,
        contract_entry,
        &mut guard_assumptions,
        budget,
    )?
    else {
        return Ok(false);
    };
    let Some(function_guards) = lower_refinement_mutable_guards_for_interface(
        function,
        function_entry,
        &mut guard_assumptions,
        budget,
    )?
    else {
        return Ok(false);
    };
    for (required_segment, required_guard) in
        function.contract_mutable().iter().zip(function_guards)
    {
        if required_guard.as_ref().is_some_and(|guard| {
            refinement_route_proves(
                &guard_assumptions,
                &Proposition::Not(Box::new(guard.clone())),
            )
        }) {
            continue;
        }
        let mut active_assumptions = guard_assumptions.clone();
        if let Some(guard) = required_guard {
            active_assumptions = active_assumptions.assume_proposition(guard);
        }
        let Ok((required_ranges, _)) = project_explicit_memory_segments(
            function_entry,
            std::slice::from_ref(required_segment),
            &active_assumptions,
            budget,
            true,
        )?
        else {
            return Ok(false);
        };
        let Some(required_range) = required_ranges.first() else {
            return Ok(false);
        };
        let mut covered = false;
        for (available_segment, available_guard) in
            contract.contract_mutable().iter().zip(&contract_guards)
        {
            if let Some(guard) = available_guard
                && !refinement_route_proves(&active_assumptions, guard)
            {
                continue;
            }
            let mut available_segment = available_segment.clone();
            available_segment.guard = None;
            let Ok((available_ranges, _)) = project_explicit_memory_segments(
                contract_entry,
                std::slice::from_ref(&available_segment),
                &active_assumptions,
                budget,
                true,
            )?
            else {
                continue;
            };
            if available_ranges.iter().any(|available_range| {
                memory_range_covers(available_range, required_range, &active_assumptions)
            }) {
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

fn project_refinement_effects(
    interface: &CFunctionContractInterface,
    entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CFunctionMemoryEffectProjection, String>> {
    let mut projection_assumptions = assumptions.clone();
    // Explicit guards retain refinement's exact-route refusal semantics. The
    // resource-derived projection has no independent surface guard list and
    // therefore goes directly through the checked transition evaluator.
    if !interface.resource_derived_mutable_frame() {
        let Some(guards) = lower_refinement_mutable_guards_for_interface(
            interface,
            entry,
            &mut projection_assumptions,
            budget,
        )?
        else {
            return Ok(Err("mutable footprint guard is undecided".to_string()));
        };
        let mut ranges = Vec::new();
        let mut evidence_facts = Vec::new();
        for (segment, guard) in interface.contract_mutable().iter().zip(guards) {
            let mut active_assumptions = projection_assumptions.clone();
            if let Some(guard) = guard {
                if refinement_route_proves(
                    &active_assumptions,
                    &Proposition::Not(Box::new(guard.clone())),
                ) {
                    continue;
                }
                active_assumptions = active_assumptions.assume_proposition(guard.clone());
                if !refinement_route_proves(&active_assumptions, &guard) {
                    return Ok(Err("mutable footprint guard is undecided".to_string()));
                }
            }
            // Guard resolution above is the refinement-specific route. Feed
            // the now unconditional segment to the shared evaluator so range
            // lowering itself remains identical to call/certification paths.
            let mut segment = segment.clone();
            segment.guard = None;
            let Ok((segment_ranges, segment_evidence)) = project_explicit_memory_segments(
                entry,
                std::slice::from_ref(&segment),
                &active_assumptions,
                budget,
                true,
            )?
            else {
                return Ok(Err("could not evaluate mutable footprint".to_string()));
            };
            ranges.extend(segment_ranges);
            evidence_facts.extend(segment_evidence);
        }
        return Ok(Ok(CFunctionMemoryEffectProjection {
            ranges,
            evidence_facts,
        }));
    }
    project_contract_memory_effects_with_guard_policy(
        entry,
        interface,
        None,
        &projection_assumptions,
        budget,
        true,
    )
}

#[cfg(test)]
fn mutable_footprint_is_compatible(
    contract: &CFunction,
    function: &CFunction,
    contract_entry: &CState,
    function_entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    mutable_footprint_is_compatible_for_interfaces(
        contract.contract_interface(),
        function.contract_interface(),
        contract_entry,
        function_entry,
        assumptions,
        budget,
    )
}

fn lower_refinement_mutable_guards_for_interface(
    interface: &CFunctionContractInterface,
    entry: &CState,
    assumptions: &mut PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<Option<Proposition>>>> {
    let mut guards = Vec::with_capacity(interface.contract_mutable().len());
    for segment in interface.contract_mutable() {
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
        if path.obligations.iter().any(|obligation| {
            !required_obligation_is_exactly_discharged(assumptions, obligation.proposition())
        }) {
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

    fn active_is_zero(value: bool) -> PureFactContext {
        PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(980_001)),
                Bitvector32Term::Constant(0),
            ),
            value,
        ))
    }

    /// An available guard that only logical search could discharge is treated
    /// as unsettled, so its segment is not available. The same footprint with
    /// the guard spelled as the exactly available condition is accepted, so
    /// the difference is the route rather than the content.
    #[test]
    fn disjunctive_available_guard_is_not_discharged_by_search() {
        let exact = function_with_segment(
            "contract",
            segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 2),
        );
        let disjunctive = function_with_segment(
            "contract",
            segment(
                Some(SpecProposition::Or(
                    Box::new(guard(CComparisonOperator::NotEqual, 0)),
                    Box::new(guard(CComparisonOperator::Equal, 5)),
                )),
                0,
                2,
            ),
        );
        let function = function_with_segment("function", segment(None, 0, 1));
        let assumptions = active_is_zero(false);
        assert!(compatible_with_assumptions(&exact, &function, &assumptions));
        assert!(!compatible_with_assumptions(
            &disjunctive,
            &function,
            &assumptions
        ));
    }

    /// A required segment whose guard is exactly refuted contributes no write,
    /// so nothing has to cover it. Without that refutation the same footprint
    /// is wider than the contract's and is rejected.
    #[test]
    fn exactly_refuted_required_guard_needs_no_cover() {
        let contract = function_with_segment(
            "contract",
            segment(Some(guard(CComparisonOperator::Equal, 1)), 0, 1),
        );
        let function = function_with_segment(
            "function",
            segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 2),
        );
        assert!(compatible_with_assumptions(
            &contract,
            &function,
            &active_is_zero(true)
        ));
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
        // Modus ponens on an explicitly assumed contract premise, with the
        // antecedent established by the exact routes only. An antecedent
        // those do not decide leaves the implication assumed as written;
        // the consequent then needs an explicit proof step.
        Proposition::Implies(left, right)
            if required_obligation_is_exactly_discharged(assumptions, &left) =>
        {
            assume_contract_proposition(assumptions, *right);
        }
        _ => {}
    }
}

/// The obligation check below is route-restricted with the rest of package
/// 10(b) but has no reaching fixture: a refined requirement's lowered path
/// carries an obligation only when the surrounding refinement context cannot
/// already see the access, and in that case no route — exact or otherwise —
/// discharges it. Attempts through an owned field and through an explicit
/// `requires loadable(...)` both produced obligation-free paths.
fn prove_contract_propositions(
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
        if path.obligations.iter().any(|obligation| {
            !required_obligation_is_exactly_discharged(assumptions, obligation.proposition())
        }) || !contract_refinement_proves(assumptions, &path.proposition)
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

/// The exact routes a refinement check may use on one leaf proposition:
/// builtin propositions, indexed exact membership in the assumed facts, and
/// the frozen condition decision procedure on a bare condition. It performs
/// no logical search — it never assumes an antecedent, enumerates ambient
/// candidates, or recursively constructs a derivation. `Not` of a bare
/// condition is the same bare condition with the opposite value, which is how
/// `contains_assumed_exact` and `evaluate_guarded_contract_condition` already
/// read it.
fn refinement_route_proves(assumptions: &PureFactContext, proposition: &Proposition) -> bool {
    if assumptions.proves_exact(proposition) {
        return true;
    }
    match proposition {
        Proposition::ConditionIs(condition, value) => assumptions.decide(condition) == Some(*value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => {
                assumptions.decide(condition) == Some(!*value)
            }
            _ => false,
        },
        _ => false,
    }
}

/// Checks one lowered contract clause against the refinement assumptions.
///
/// This is the exact leaf route and nothing else. The logical descent this
/// used to perform — sequence-element alignment, `and` split, `or` arm
/// choice, `implies` with a refuted antecedent, and a search over recorded
/// equality-class rewrites of a comparison's operands — was kernel proof
/// planning: it chose an index alignment, an arm, and a rewrite
/// representative, and issued refinement authority from that choice with no
/// record of it. Those choices now belong to the refinement theorem's proof,
/// where `both`, `left`/`right`, `intro`, `extract`, and `rewrite` spell them
/// and `click expand` prints them. See `prepare_contract_refinement_obligations`,
/// which emits the refinement implication, and
/// `api.rs::prove_c_function_contract_refinement`, which issues authority only
/// from a closed proof of exactly that implication.
fn contract_refinement_proves(assumptions: &PureFactContext, proposition: &Proposition) -> bool {
    refinement_route_proves(assumptions, proposition)
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
        | SpecProposition::ForAllInteger { body, .. }
        | SpecProposition::ForAllPointer { body, .. }
        | SpecProposition::ExistsInt32 { body, .. }
        | SpecProposition::ExistsInteger { body, .. }
        | SpecProposition::ExistsPointer { body, .. } => {
            spec_proposition_is_state_independent(body)
        }
        _ => false,
    }
}

/// The stateful refinement rule admits ordinary scalar propositions whose only
/// stateful operation is a C memory access (possibly below `old`), including
/// finite sequence comparisons and membership, plus resource-field reads and
/// the algebraic values those fields carry. Explicit memory snapshots,
/// `at(...)`, counted-resource populations, and range folds stay outside it:
/// their stateful refinement laws are not written down, so they need an
/// explicit refinement theorem. Mathematical `Integer` comparisons stay
/// outside it for the same reason. The caller separately checks resource and
/// footprint refinement.
///
/// Every variant is listed. A new specification form is excluded until its
/// refinement behaviour has been considered, which a wildcard would silently
/// reverse.
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
        SpecProposition::AlgebraicComparison { left, right, .. } => {
            spec_algebraic_expression_supports_stateful_memory_refinement(left)
                && spec_algebraic_expression_supports_stateful_memory_refinement(right)
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
        | SpecProposition::ForAllInteger { body, .. }
        | SpecProposition::ForAllPointer { body, .. }
        | SpecProposition::ExistsInt32 { body, .. }
        | SpecProposition::ExistsInteger { body, .. }
        | SpecProposition::ExistsPointer { body, .. } => {
            spec_proposition_supports_stateful_memory_refinement(body)
        }
        SpecProposition::IntegerComparison { .. }
        | SpecProposition::Predicate { .. }
        | SpecProposition::ResourceSeparate { .. }
        | SpecProposition::ResourceContains { .. }
        | SpecProposition::MemoryLoadable { .. } => false,
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
        // A field read names an instance the two interfaces share. Both the
        // current and the entry projection lower through
        // `resource_instance_at_path` against the state the caller supplies;
        // a projection the state cannot answer refuses the refinement there.
        SpecExpression::ResourceField { .. } => true,
        SpecExpression::Value(_) => true,
        SpecExpression::IntegerToMachine { .. } => false,
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
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            spec_algebraic_expression_supports_stateful_memory_refinement(scrutinee)
                && arms
                    .iter()
                    .all(|arm| spec_expression_supports_stateful_memory_refinement(&arm.body))
        }
        SpecExpression::CountedResourceCount { .. }
        | SpecExpression::RangeFold { .. }
        | SpecExpression::LoopEntrySnapshot(_)
        | SpecExpression::MemoryLoad { .. } => false,
    }
}

/// Algebraic values are ordinary terms over instance fields, constructors,
/// match arms, and opaque pure functions. None of them reads memory except
/// through the `SpecExpression` nodes below, which are filtered by the same
/// rule, so an algebraic clause is admitted exactly when its scalar leaves
/// are.
fn spec_algebraic_expression_supports_stateful_memory_refinement(
    expression: &SpecAlgebraicExpression,
) -> bool {
    match &expression.node {
        SpecAlgebraicExpressionNode::Variable(_)
        | SpecAlgebraicExpressionNode::Binding(_)
        | SpecAlgebraicExpressionNode::ResourceField(_) => true,
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => fields
            .iter()
            .all(spec_algebraic_value_supports_stateful_memory_refinement),
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            spec_algebraic_expression_supports_stateful_memory_refinement(scrutinee)
                && arms.iter().all(|arm| {
                    spec_algebraic_expression_supports_stateful_memory_refinement(&arm.body)
                })
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => arguments
            .iter()
            .all(spec_pure_function_argument_supports_stateful_memory_refinement),
    }
}

fn spec_algebraic_value_supports_stateful_memory_refinement(value: &SpecAlgebraicValue) -> bool {
    match value {
        SpecAlgebraicValue::C(expression) => {
            spec_expression_supports_stateful_memory_refinement(expression)
        }
        // Mathematical `Integer` values keep the exclusion that
        // `SpecPureFunctionArgument::Integer` already states.
        SpecAlgebraicValue::Integer(_) => false,
        SpecAlgebraicValue::Algebraic(expression) => {
            spec_algebraic_expression_supports_stateful_memory_refinement(expression)
        }
    }
}

fn spec_pure_function_argument_supports_stateful_memory_refinement(
    argument: &SpecPureFunctionArgument,
) -> bool {
    match argument {
        SpecPureFunctionArgument::Value(expression) => {
            spec_expression_supports_stateful_memory_refinement(expression)
        }
        SpecPureFunctionArgument::Integer(_) => false,
        SpecPureFunctionArgument::Algebraic(expression) => {
            spec_algebraic_expression_supports_stateful_memory_refinement(expression)
        }
        // An array snapshot is an explicit memory image; its stateful
        // refinement law is not written down.
        SpecPureFunctionArgument::ArrayRef { .. } => false,
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
        SpecPureFunctionArgument::Integer(_) => true,
        SpecPureFunctionArgument::Algebraic(expression) => {
            spec_algebraic_expression_is_state_independent(expression)
        }
        SpecPureFunctionArgument::ArrayRef { .. } => false,
    }
}

/// The datatype reflexivity shortcut may skip evaluation only for expressions
/// that cannot emit a guard or obligation. State independence alone does not
/// imply totality: a mathematical conversion may have a required domain.
pub(super) fn spec_algebraic_expression_is_obligation_free(
    expression: &SpecAlgebraicExpression,
) -> bool {
    match &expression.node {
        SpecAlgebraicExpressionNode::Variable(_) | SpecAlgebraicExpressionNode::Binding(_) => true,
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            fields.iter().all(|field| match field {
                SpecAlgebraicValue::C(value) => spec_value_is_obligation_free(value),
                SpecAlgebraicValue::Integer(value) => spec_integer_is_obligation_free(value),
                SpecAlgebraicValue::Algebraic(value) => {
                    spec_algebraic_expression_is_obligation_free(value)
                }
            })
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { name, arguments } => {
            name != "to_nat" && arguments.iter().all(spec_argument_is_obligation_free)
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            if !spec_algebraic_expression_is_obligation_free(scrutinee)
                || arms.len() != scrutinee.algebraic_type.variants.len()
            {
                return false;
            }
            let variants = scrutinee
                .algebraic_type
                .variants
                .iter()
                .map(|variant| (variant.name.as_str(), variant.fields.len()))
                .collect::<BTreeMap<_, _>>();
            let mut seen = BTreeSet::new();
            arms.iter().all(|arm| {
                seen.insert(arm.variant.as_str())
                    && variants.get(arm.variant.as_str()) == Some(&arm.bindings.len())
                    && spec_algebraic_expression_is_obligation_free(&arm.body)
            })
        }
        SpecAlgebraicExpressionNode::ResourceField(_) => false,
    }
}

fn spec_argument_is_obligation_free(argument: &SpecPureFunctionArgument) -> bool {
    match argument {
        SpecPureFunctionArgument::Value(value) => spec_value_is_obligation_free(value),
        SpecPureFunctionArgument::Integer(value) => spec_integer_is_obligation_free(value),
        SpecPureFunctionArgument::Algebraic(value) => {
            spec_algebraic_expression_is_obligation_free(value)
        }
        SpecPureFunctionArgument::ArrayRef { .. } => false,
    }
}

fn spec_value_is_obligation_free(value: &SpecExpression) -> bool {
    matches!(
        value,
        SpecExpression::Value(_)
            | SpecExpression::CExpression(
                CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_)
            )
    )
}

fn spec_integer_is_obligation_free(value: &SpecIntegerExpression) -> bool {
    match value {
        SpecIntegerExpression::Term(_) => true,
        SpecIntegerExpression::Negate(inner) => spec_integer_is_obligation_free(inner),
        SpecIntegerExpression::Add(left, right)
        | SpecIntegerExpression::Subtract(left, right)
        | SpecIntegerExpression::Multiply(left, right) => {
            spec_integer_is_obligation_free(left) && spec_integer_is_obligation_free(right)
        }
        SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
            arguments.iter().all(spec_argument_is_obligation_free)
        }
        SpecIntegerExpression::AlgebraicMatch { .. } => false,
        SpecIntegerExpression::FromMachine(_) | SpecIntegerExpression::ResourceField(_) => false,
        SpecIntegerExpression::RangeFold { .. } => false,
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
                SpecAlgebraicValue::Integer(_) => true,
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
        SpecExpression::IntegerToMachine { value, .. } => {
            spec_integer_expression_reads_current_parameter(value, parameter_name)
        }
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

fn spec_integer_expression_reads_current_parameter(
    expression: &SpecIntegerExpression,
    parameter_name: &str,
) -> bool {
    match expression {
        SpecIntegerExpression::Term(_) | SpecIntegerExpression::ResourceField(_) => false,
        SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
            arguments.iter().any(|argument| {
                spec_pure_function_argument_reads_current_parameter(argument, parameter_name)
            })
        }
        SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
            spec_algebraic_expression_reads_current_parameter(scrutinee, parameter_name)
                || arms.iter().any(|arm| {
                    spec_integer_expression_reads_current_parameter(&arm.body, parameter_name)
                })
        }
        SpecIntegerExpression::FromMachine(machine) => {
            spec_expression_reads_current_parameter(machine, parameter_name)
        }
        SpecIntegerExpression::Negate(inner) => {
            spec_integer_expression_reads_current_parameter(inner, parameter_name)
        }
        SpecIntegerExpression::Add(left, right)
        | SpecIntegerExpression::Subtract(left, right)
        | SpecIntegerExpression::Multiply(left, right) => {
            spec_integer_expression_reads_current_parameter(left, parameter_name)
                || spec_integer_expression_reads_current_parameter(right, parameter_name)
        }
        SpecIntegerExpression::RangeFold {
            index,
            initial,
            body,
            ..
        } => {
            let index_reads = match index {
                SpecIntegerRangeFoldIndex::Int32 { start, end } => {
                    spec_expression_reads_current_parameter(start, parameter_name)
                        || spec_expression_reads_current_parameter(end, parameter_name)
                }
                SpecIntegerRangeFoldIndex::Integer { start, end } => {
                    spec_integer_expression_reads_current_parameter(start, parameter_name)
                        || spec_integer_expression_reads_current_parameter(end, parameter_name)
                }
            };
            index_reads
                || spec_integer_expression_reads_current_parameter(initial, parameter_name)
                || spec_integer_expression_reads_current_parameter(body, parameter_name)
        }
    }
}

fn spec_proposition_reads_current_parameter(
    proposition: &SpecProposition,
    parameter_name: &str,
) -> bool {
    match proposition {
        SpecProposition::IntegerComparison { left, right, .. } => {
            spec_integer_expression_reads_current_parameter(left, parameter_name)
                || spec_integer_expression_reads_current_parameter(right, parameter_name)
        }
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
        | SpecProposition::ForAllInteger { body, .. }
        | SpecProposition::ForAllPointer { body, .. }
        | SpecProposition::ExistsInt32 { body, .. }
        | SpecProposition::ExistsInteger { body, .. }
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
                SpecAlgebraicValue::Integer(_) => false,
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
        SpecPureFunctionArgument::Integer(_) => false,
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
        CValue::Bool(term) => term.as_const(),
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
            if c_expression_parameter_offset(pointer, parameter_name).is_some()
                || c_expression_mentions_variable(pointer, parameter_name)
            {
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
        SpecExpression::IntegerToMachine { .. } => *unknown_read = true,
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
        SpecProposition::IntegerComparison { .. } => {}
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
        | SpecProposition::ForAllInteger { body, .. }
        | SpecProposition::ForAllPointer { body, .. }
        | SpecProposition::ExistsInt32 { body, .. }
        | SpecProposition::ExistsInteger { body, .. }
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
                    SpecAlgebraicValue::Integer(_) => {}
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
        SpecPureFunctionArgument::Integer(_) => {}
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

#[cfg(test)]
fn add_verified_function_ensure_facts(
    facts: &mut Vec<ExecutionPureFact>,
    obligations: &[ProofObligation],
    post_contract_state: &CState,
    entry_contract_state: &CState,
    function: &CFunction,
    effective_assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<()> {
    add_verified_function_ensure_facts_selected_with_interface(
        facts,
        obligations,
        post_contract_state,
        entry_contract_state,
        function.contract_interface(),
        function.contract_ensures().iter(),
        effective_assumptions,
        budget,
    )
}

fn add_verified_function_ensure_facts_selected_with_interface<'a>(
    facts: &mut Vec<ExecutionPureFact>,
    obligations: &[ProofObligation],
    post_contract_state: &CState,
    entry_contract_state: &CState,
    interface: &CFunctionContractInterface,
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
            let specialized_assumptions = assumptions_with_path_context(
                &ensure_assumptions,
                &ensure_path.facts,
                &ensure_path.obligations,
            );
            // The callee's ensure holds under its own leading premises. Where
            // one of those premises is exactly available at this call, the
            // consequent is available too, and publishing it saves every
            // caller an `extract`. This is the kernel's modus ponens, so it
            // walks only the ensure's own implication chain and cites each
            // discharged premise exactly: an indexed hit in the call context,
            // or a premise already discharged above it in this chain. A
            // premise neither route settles ends the walk, and the ensure
            // stays available as the implication it was written as, for the
            // proof to discharge with `extract`.
            let mut specialized = ensure_path.proposition.clone();
            let mut discharged_premises: Vec<Proposition> = Vec::new();
            while let Proposition::Implies(premise, body) = specialized {
                let available = specialized_assumptions.proves_exact(&premise)
                    || discharged_premises
                        .iter()
                        .any(|discharged| discharged == premise.as_ref());
                if !available {
                    specialized = Proposition::Implies(premise, body);
                    break;
                }
                discharged_premises.push((*premise).clone());
                specialized = *body;
            }
            if !discharged_premises.is_empty() {
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
        if let Some(unfolding) = interface
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

/// No fixture in either harness reaches the refutation below; the kernel
/// test `continuity_requires_both_the_allocation_base_and_size` pins it, and
/// fails when the route is denied.
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
        // Two allocation sizes at one base are the same allocation, a
        // refuted one, or an undecided pair. The refutation uses the exact
        // fact index and the frozen condition checker on the bare condition;
        // anything else stays undecided and travels on as a condition the
        // consumer must settle.
        if required_obligation_is_exactly_discharged(
            assumptions,
            &Proposition::ConditionIs(condition.clone(), false),
        ) {
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
    interface: &CFunctionContractInterface,
    assumptions: &PureFactContext,
) -> Result<(CMemory, Vec<ExecutionPureFact>), VerifiedAllocationDeltaError> {
    let mut effects = Vec::new();
    let input = expand_all_composite_resource_facts(
        input_resources,
        interface.composite_resource_definitions(),
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
        interface.composite_resource_definitions(),
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
        interface.composite_resource_definitions(),
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
                interface.composite_resource_definitions(),
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
    with_contract_interface_argument_views(state, function.contract_interface(), values)
}

fn with_contract_interface_argument_views(
    state: &CState,
    interface: &CFunctionContractInterface,
    values: &[CValue],
) -> CState {
    let mut state = state.clone();
    for (parameter, value) in interface.parameters().iter().zip(values) {
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
        let value = coerce_c_contract_argument_without_obligations(value, parameter)
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
    set_contract_result(state, function.contract_interface(), value);
}

fn set_contract_result(state: &mut CState, interface: &CFunctionContractInterface, value: CValue) {
    if let Some(layout) = interface.return_aggregate_layout()
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
        value.with_pointer_pointee_constant(interface.return_pointee_is_constant()),
        interface.return_type(),
        false,
        false,
        false,
        interface.return_pointee_is_constant(),
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

#[cfg(test)]
fn symbolic_function_result(function: &CFunction, variable: Variable) -> CValue {
    symbolic_contract_result(function.contract_interface(), variable)
}

fn symbolic_contract_result(interface: &CFunctionContractInterface, variable: Variable) -> CValue {
    symbolic_call_result(interface.return_type(), variable)
        .with_pointer_pointee_constant(interface.return_pointee_is_constant())
}

pub(crate) fn symbolic_call_result(c_type: CType, variable: Variable) -> CValue {
    match c_type {
        CType::Void => CValue::Void,
        CType::Bool => crate::kernel::bool_value(Bitvector32Term::Variable(variable)),
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
    contract_argument_binding_error(function.contract_interface(), function.name(), values)
}

fn contract_argument_binding_error(
    interface: &CFunctionContractInterface,
    name: &str,
    values: &[CValue],
) -> String {
    if interface
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
            name
        )
    } else {
        format!("could not bind arguments for {name}")
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

/// Collect the expressions that read memory when a function body is executed.
///
/// A verified call normally applies the function's contract without executing
/// its body. That is sound for external memory, whose initialization is part
/// of the caller's loadability authority, but a caller's automatic object has
/// a separate initialization history. Keeping the read expressions lets the
/// call boundary recheck that history without rerunning the body or treating a
/// resource transfer as an initialization event.
fn collect_c_memory_read_expressions(statement: &CStatement, reads: &mut Vec<CExpression>) {
    fn values(expression: &CExpression, reads: &mut Vec<CExpression>) {
        match expression {
            CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => {}
            CExpression::Cast { expression, .. }
            | CExpression::FloatNegate(expression)
            | CExpression::FloatClassification { expression, .. }
            | CExpression::PointerOffsetBytes {
                pointer: expression,
                ..
            }
            | CExpression::Not(expression)
            | CExpression::BitwiseNot(expression) => values(expression, reads),
            CExpression::Conditional {
                condition,
                then_branch,
                else_branch,
            } => {
                values(condition, reads);
                values(then_branch, reads);
                values(else_branch, reads);
            }
            CExpression::AddressOf(target) => lvalue_address(target, reads),
            CExpression::Load(pointer) => {
                reads.push(expression.clone());
                values(pointer, reads);
            }
            CExpression::TypedLoad {
                pointer,
                value_type,
                ..
            } => {
                if !matches!(
                    value_type,
                    CType::Int32Array(_)
                        | CType::UInt8Array(_)
                        | CType::Int16Array(_)
                        | CType::UInt16Array(_)
                        | CType::UInt32Array(_)
                        | CType::Int64Array(_)
                        | CType::UInt64Array(_)
                        | CType::Float32Array(_)
                        | CType::Float64Array(_)
                ) {
                    reads.push(expression.clone());
                }
                values(pointer, reads);
            }
            CExpression::Index(base, index) => {
                reads.push(expression.clone());
                values(base, reads);
                values(index, reads);
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
                values(left, reads);
                values(right, reads);
            }
        }
    }

    fn lvalue_address(expression: &CExpression, reads: &mut Vec<CExpression>) {
        match expression {
            CExpression::Variable(_) => {}
            CExpression::Load(pointer) | CExpression::TypedLoad { pointer, .. } => {
                values(pointer, reads)
            }
            CExpression::Index(base, index) => {
                values(base, reads);
                values(index, reads);
            }
            _ => values(expression, reads),
        }
    }

    match statement {
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. } => {}
        CStatement::ContinueWithStep { step } => collect_c_memory_read_expressions(step, reads),
        CStatement::CopyAggregate { target, source, .. } => {
            lvalue_address(target, reads);
            values(source, reads);
        }
        CStatement::Assign { expression, .. } => values(expression, reads),
        CStatement::CallAssign { arguments, .. } | CStatement::Call { arguments, .. } => {
            for argument in arguments {
                values(argument, reads);
            }
        }
        CStatement::HeapAllocate { bytes, .. } => values(bytes, reads),
        CStatement::HeapFree { pointer } => values(pointer, reads),
        CStatement::Assert { condition, .. } => values(condition, reads),
        CStatement::Seq(first, second) => {
            collect_c_memory_read_expressions(first, reads);
            collect_c_memory_read_expressions(second, reads);
        }
        CStatement::Return(expression) => values(expression, reads),
        CStatement::Store { pointer, value } | CStatement::TypedStore { pointer, value, .. } => {
            lvalue_address(pointer, reads);
            values(value, reads);
        }
        CStatement::Update {
            target, operand, ..
        } => {
            values(target, reads);
            values(operand, reads);
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            values(condition, reads);
            collect_c_memory_read_expressions(then_branch, reads);
            collect_c_memory_read_expressions(else_branch, reads);
        }
        CStatement::While {
            condition, body, ..
        } => {
            values(condition, reads);
            collect_c_memory_read_expressions(body, reads);
        }
        CStatement::Switch { expression, cases } => {
            values(expression, reads);
            for case in cases {
                collect_c_memory_read_expressions(&case.body, reads);
            }
        }
    }
}

fn c_expression_mentions_pointer_parameter(
    expression: &CExpression,
    pointer_parameters: &BTreeSet<String>,
) -> bool {
    match expression {
        CExpression::Value(_) | CExpression::FunctionAddress(_) => false,
        CExpression::Variable(name) => pointer_parameters.contains(name),
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
            c_expression_mentions_pointer_parameter(expression, pointer_parameters)
        }
        CExpression::TypedLoad { pointer, .. } => {
            c_expression_mentions_pointer_parameter(pointer, pointer_parameters)
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_mentions_pointer_parameter(condition, pointer_parameters)
                || c_expression_mentions_pointer_parameter(then_branch, pointer_parameters)
                || c_expression_mentions_pointer_parameter(else_branch, pointer_parameters)
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
            c_expression_mentions_pointer_parameter(left, pointer_parameters)
                || c_expression_mentions_pointer_parameter(right, pointer_parameters)
        }
    }
}

fn verified_call_uninitialized_read(
    entry_state: &CState,
    function: &CFunction,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<CUndefinedBehavior>> {
    // Aggregate copies have their own field-by-field initialization checks at
    // execution time. Their lowered lvalues also include typed array views
    // that are not scalar reads of a transferred pointer parameter.
    if function
        .parameters()
        .iter()
        .any(|parameter| parameter.aggregate_layout().is_some())
    {
        return Ok(None);
    }
    let mut reads = Vec::new();
    collect_c_memory_read_expressions(function.body(), &mut reads);
    let pointer_parameters = function
        .parameters()
        .iter()
        .filter(|parameter| parameter.c_type().is_pointer())
        .map(|parameter| parameter.name().to_string())
        .collect::<BTreeSet<_>>();
    for read in reads
        .into_iter()
        .filter(|read| c_expression_mentions_pointer_parameter(read, &pointer_parameters))
    {
        for path in evaluate_c_expression_paths(entry_state, &read, assumptions, budget)? {
            if let CExpressionOutcome::UndefinedBehavior(undefined_behavior) = path.outcome
                && undefined_behavior == CUndefinedBehavior::UninitializedRead
            {
                return Ok(Some(undefined_behavior));
            }
        }
    }
    Ok(None)
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
        // parameter object itself. A volatile pointer parameter is different:
        // its own object is the access, so it needs an address-backed slot for
        // the volatile event to name.
        .filter(|parameter| {
            (address_taken.contains(parameter.name()) || parameter.is_volatile())
                && (parameter.is_volatile() && parameter.c_type().is_pointer()
                    || matches!(
                        parameter.c_type(),
                        CType::Int16
                            | CType::Int32
                            | CType::UInt8
                            | CType::UInt16
                            | CType::UInt32
                            | CType::Float32
                            | CType::Float64
                    ))
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
        )
        .with_next_local_lifetime(caller_state.next_local_lifetime());
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

/// Binds only the locals needed to instantiate a body-independent contract
/// interface. This intentionally does not inspect a statement body, collect
/// address-taken locals, initialize globals, or allocate static storage. It is
/// the binding path for named callbacks and external assumptions, whose
/// applications have no concrete body evidence.
fn bind_c_contract_arguments(
    caller_state: &CState,
    interface: &CFunctionContractInterface,
    values: &[CValue],
) -> Option<CState> {
    if values.len() != interface.parameters().len() {
        return None;
    }
    let frame = caller_state.next_local_frame();
    let has_aggregate_parameters = interface
        .parameters()
        .iter()
        .any(|parameter| parameter.aggregate_layout().is_some());
    let mut callee_state = CState::new()
        .with_memory(caller_state.memory.clone())
        .with_resource_context(caller_state.resources.clone())
        .with_next_local_frame(if has_aggregate_parameters {
            frame.saturating_add(1)
        } else {
            frame
        })
        .with_next_local_lifetime(caller_state.next_local_lifetime());
    callee_state.counted_populations = caller_state.counted_populations.clone();
    for (parameter, value) in interface.parameters().iter().zip(values) {
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
    Some(callee_state)
}

fn coerce_c_function_argument_without_obligations(
    value: &CValue,
    parameter: &CParameter,
) -> Option<CValue> {
    coerce_c_contract_argument_without_obligations(value, parameter)
}

fn coerce_c_contract_argument_without_obligations(
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
    coerce_c_contract_arguments(
        function.contract_interface(),
        values,
        existing_obligations,
        assumptions,
    )
}

fn coerce_c_contract_arguments(
    interface: &CFunctionContractInterface,
    values: &[CValue],
    existing_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
) -> Option<(Vec<CValue>, Vec<ProofObligation>)> {
    if values.len() != interface.parameters().len() {
        return None;
    }
    let mut obligations = existing_obligations.to_vec();
    let mut coerced = Vec::with_capacity(values.len());
    for (parameter, value) in interface.parameters().iter().zip(values) {
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
/// observe writes performed by their caller. Ordinary function entry declares
/// missing storage without restoring its initializer; reads then remain
/// symbolic until a caller state or a precondition constrains them. The
/// startup-only storage constructor passes `true` to materialize initializers.
/// Static locals use a function-qualified block identity and are therefore
/// initialized once for the whole symbolic execution, not once per call frame.
pub(crate) fn initialize_c_function_globals(state: &CState, function: &CFunction) -> CState {
    initialize_c_function_globals_owned(state.clone(), function, false)
}

/// Constructs a fresh startup state, never an ordinary call transition.
/// Storage identities coalesce aliases before permissions are issued. No
/// incoming state is accepted, so this cannot replenish consumed resources.
pub(crate) fn initialize_c_program_storage(
    functions: impl IntoIterator<Item = CFunction>,
) -> CState {
    let mut state = CState::new();
    for function in functions {
        state = initialize_c_function_globals_owned(state, &function, true);
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

fn initialize_c_function_globals_owned(
    mut state: CState,
    function: &CFunction,
    initialize_missing_storage: bool,
) -> CState {
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
            state.memory = state.memory.with_block_or_read_only(
                slot.block.clone(),
                global.c_type().byte_width(),
                global.is_constant(),
            );
            if initialize_missing_storage || global.is_constant() {
                state.memory = state
                    .memory
                    .store(slot.clone(), global.initial_value().clone());
            } else {
                state.memory = materialize_symbolic_cell(state.memory, &slot, global.c_type());
            }
        } else if !initialize_missing_storage
            && !global.is_constant()
            && global.c_type().is_object_pointer()
            && state
                .memory
                .known_value(&slot)
                .is_some_and(|value| symbolic_pointer_placeholder(&value, &slot))
        {
            // Resource setup may declare a pointer's storage before the
            // global binding is installed. Replace an untyped placeholder
            // with the authoritative typed symbolic pointer cell.
            state.memory = materialize_symbolic_cell(state.memory, &slot, global.c_type());
        }
        state.locals.set_global_with_all_qualifiers(
            global.kernel_name().to_string(),
            global.c_type(),
            slot.clone(),
            global.is_volatile(),
            global.pointee_is_volatile(),
            global.is_constant(),
            global.pointee_is_constant(),
        );
        if global.kernel_name() != global.name() && !state.locals.contains_name(global.name()) {
            state.locals.set_global_with_all_qualifiers(
                global.name().to_string(),
                global.c_type(),
                slot,
                global.is_volatile(),
                global.pointee_is_volatile(),
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
            if initialize_missing_storage || global_array.is_constant() {
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
            } else {
                state.memory = materialize_symbolic_array(
                    state.memory,
                    &slot,
                    global_array.element_type(),
                    global_array.length(),
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
            if initialize_missing_storage || global_aggregate.is_constant() {
                state.memory =
                    zero_aggregate_fields(state.memory.clone(), &slot, global_aggregate.layout());
                state.memory = initialize_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    global_aggregate.initializers(),
                );
            } else {
                state.memory = materialize_symbolic_aggregate_fields(
                    state.memory,
                    &slot,
                    global_aggregate.layout(),
                );
            }
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
            if initialize_missing_storage || global_aggregate_array.is_constant() {
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
            } else {
                state.memory = materialize_symbolic_aggregate_array(
                    state.memory,
                    &slot,
                    global_aggregate_array.layout(),
                    global_aggregate_array.length(),
                );
            }
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
            if (initialize_missing_storage || static_local.is_constant())
                && state.memory.known_value(&slot).is_none()
            {
                state.memory = state
                    .memory
                    .store(slot.clone(), static_local.initial_value().clone());
            } else if !initialize_missing_storage
                && !static_local.is_constant()
                && state.memory.known_value(&slot).is_none()
            {
                state.memory =
                    materialize_symbolic_cell(state.memory, &slot, static_local.c_type());
            }
        } else if !initialize_missing_storage
            && !static_local.is_constant()
            && static_local.c_type().is_object_pointer()
            && state
                .memory
                .known_value(&slot)
                .is_some_and(|value| symbolic_pointer_placeholder(&value, &slot))
        {
            state.memory = materialize_symbolic_cell(state.memory, &slot, static_local.c_type());
        }
        state.locals.set_global_with_all_qualifiers(
            static_local.kernel_name().to_string(),
            static_local.c_type(),
            slot.clone(),
            static_local.is_volatile(),
            static_local.pointee_is_volatile(),
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
                static_local.pointee_is_volatile(),
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
            if initialize_missing_storage || static_array.is_constant() {
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
            } else {
                state.memory = materialize_symbolic_array(
                    state.memory,
                    &slot,
                    static_array.element_type(),
                    static_array.length(),
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
            if initialize_missing_storage || static_aggregate.is_constant() {
                state.memory =
                    zero_aggregate_fields(state.memory.clone(), &slot, static_aggregate.layout());
                state.memory = initialize_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    static_aggregate.initializers(),
                );
            } else {
                state.memory = materialize_symbolic_aggregate_fields(
                    state.memory,
                    &slot,
                    static_aggregate.layout(),
                );
            }
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
            if initialize_missing_storage || static_aggregate_array.is_constant() {
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
            } else {
                state.memory = materialize_symbolic_aggregate_array(
                    state.memory,
                    &slot,
                    static_aggregate_array.layout(),
                    static_aggregate_array.length(),
                );
            }
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

fn materialize_symbolic_cell(mut memory: CMemory, pointer: &Pointer, c_type: CType) -> CMemory {
    let symbolic_base = symbolic_memory_base(&memory, pointer);
    let value = if c_type.is_object_pointer() {
        Some(symbolic_pointer_cell_load(&symbolic_base, pointer, c_type))
    } else {
        symbolic_load_value(&symbolic_base, pointer, c_type)
    };
    if let Some(value) = value {
        memory = memory.store(pointer.clone(), value);
    }
    memory
}

fn symbolic_pointer_placeholder(value: &CValue, storage: &Pointer) -> bool {
    let CValue::Pointer(value) = value else {
        return false;
    };
    value.pointer().block == storage.block
        && !matches!(value.pointer().offset, PointerOffsetTerm::Constant(_))
}

fn symbolic_pointer_cell_load(memory: &CMemory, pointer: &Pointer, value_type: CType) -> CValue {
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory.clone()),
        Box::new(pointer.clone()),
    );
    let (variable, _) = crate::kernel::eval::load_variable_for_term(&load)
        .expect("symbolic pointer cells must be backed by memory loads");
    CValue::typed_pointer(Pointer::symbolic(variable), value_type)
}

/// Returns the stable symbolic value of a pointer object whose storage is not
/// available in the current function's C state. Contract-only references to
/// an external pointer use the same canonical load identity as ordinary entry
/// initialization, so resource transfer follows the current pointer value.
pub(crate) fn stable_symbolic_pointer_cell_value(pointer: &Pointer, value_type: CType) -> CValue {
    let memory = CMemory::new()
        .with_block_without_derivation(pointer.block.clone(), value_type.byte_width());
    symbolic_pointer_cell_load(&memory, pointer, value_type)
}

/// Returns the stable symbolic value for a typed static-storage cell. The
/// backing memory contains only the storage block, so resource lowering and
/// ordinary function entry derive the same load identity even when the
/// caller has not yet materialized the surrounding object.
fn symbolic_memory_base(memory: &CMemory, pointer: &Pointer) -> CMemory {
    let size = memory
        .blocks
        .get(&pointer.block)
        .and_then(|block| block.size().as_const())
        .expect("symbolic static-storage block has a constant size");
    CMemory::new().with_block_without_derivation(pointer.block.clone(), size)
}

fn materialize_symbolic_array(
    mut memory: CMemory,
    base: &Pointer,
    element_type: CType,
    length: u32,
) -> CMemory {
    for index in 0..length {
        let pointer = base.offset_by_bytes(index.saturating_mul(element_type.byte_width()));
        memory = materialize_symbolic_cell(memory, &pointer, element_type);
    }
    memory
}

fn materialize_symbolic_aggregate_fields(
    mut memory: CMemory,
    base: &Pointer,
    layout: &CAggregateLayout,
) -> CMemory {
    for field in layout.fields() {
        let field_base = base.offset_by_bytes(field.offset_bytes());
        match field.c_type() {
            CType::Int32Array(length) => {
                memory = materialize_symbolic_array(memory, &field_base, CType::Int32, length);
            }
            CType::UInt8Array(length) => {
                memory = materialize_symbolic_array(memory, &field_base, CType::UInt8, length);
            }
            CType::Float32Array(length) => {
                memory = materialize_symbolic_array(memory, &field_base, CType::Float32, length);
            }
            CType::Float64Array(length) => {
                memory = materialize_symbolic_array(memory, &field_base, CType::Float64, length);
            }
            _ => {
                memory = materialize_symbolic_cell(memory, &field_base, field.c_type());
            }
        }
    }
    for union in layout.unions() {
        let union_base = base.offset_by_bytes(union.offset_bytes());
        for field in union.fields() {
            let pointer = union_base.offset_by_bytes(field.offset_bytes());
            let symbolic_base = symbolic_memory_base(&memory, &pointer);
            if let Some(value) = symbolic_load_value(&symbolic_base, &pointer, field.c_type()) {
                memory = memory.store_union(pointer, field.c_type(), value);
            }
        }
    }
    memory
}

fn materialize_symbolic_aggregate_array(
    mut memory: CMemory,
    base: &Pointer,
    layout: &CAggregateLayout,
    length: u32,
) -> CMemory {
    for index in 0..length {
        let element_base = base.offset_by_bytes(
            index
                .checked_mul(layout.size_bytes())
                .expect("validated aggregate symbolic offset"),
        );
        memory = materialize_symbolic_aggregate_fields(memory, &element_base, layout);
    }
    memory
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
            | CType::Float64PointerPointer
            // Static storage zero-initializes a callback field to a null
            // function pointer, just like a data-pointer field.
            | CType::FunctionPointer(_) => (field.c_type(), 1),
            CType::Int32Array(length) => (CType::Int32, length),
            CType::UInt8Array(length) => (CType::UInt8, length),
            CType::Float32Array(length) => (CType::Float32, length),
            CType::Float64Array(length) => (CType::Float64, length),
            _ => continue,
        };
        let zero = match element_type {
            CType::Bool => CValue::Bool(Bitvector32Term::Constant(0)),
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
            | CType::Float64PointerPointer
            | CType::FunctionPointer(_) => CValue::typed_pointer(Pointer::null(), element_type),
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
            | CType::VoidPointer => {
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
    let Some(bytes) = (end - start).checked_mul(range.element_width()) else {
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
            | CType::UInt8PointerPointer
            | CType::FunctionPointer(_) => (field.c_type(), 1),
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
            | CType::UInt8PointerPointer
            // A callback field is an eight-byte pointer value; carry it so a
            // copied table still dispatches to the same concrete target.
            | CType::FunctionPointer(_) => (field.c_type(), 1),
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
    prepare_contract_resource_transfer(
        caller_state,
        callee_state,
        function.name(),
        function.contract_interface(),
        assumptions,
        budget,
        preserve_explicit_representation,
    )
}

fn prepare_contract_resource_transfer(
    caller_state: &CState,
    callee_state: &CState,
    _interface_name: &str,
    interface: &CFunctionContractInterface,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    preserve_explicit_representation: bool,
) -> ExecutionResult<Result<CFunctionResourceTransfer, CRuntimeError>> {
    // In particular, preparing several pure callback interfaces must not
    // repeatedly enumerate the caller's unrelated resource frame.
    if interface.resource_requires().is_empty() && !preserve_explicit_representation {
        return Ok(Ok(CFunctionResourceTransfer {
            borrowed_inputs: Vec::new(),
            consumed_inputs: Vec::new(),
            callee_resources: ResourceContext::new(),
            caller_resources_after_requirements: caller_state.resources().clone(),
            memory_effects: Vec::new(),
            post_outputs: None,
        }));
    }
    let preserve_explicit_representation = preserve_explicit_representation
        && interface
            .composite_resource_definitions()
            .iter()
            .any(CCompositeResourceDefinition::is_recursive);
    let (required_resources, checked_required_resources) =
        match super::assumptions::capture_implicit_reasoning_provenance(|| {
            evaluate_function_resource_context_with_metadata(
                callee_state,
                interface.resource_requires(),
                interface.composite_resource_definitions(),
                assumptions,
                budget,
            )
        })? {
            Ok(resources) => resources,
            Err(error) => return Ok(Err(error)),
        };
    // Role is section semantics, not a decoration on the access mode.  A
    // viewed fact can only be borrowed, while an owned fact may be either a
    // consumed transfer or an entry borrow returned by the contract.  A
    // produced input, or a post-snapshot requirement, is malformed and is
    // rejected before any residual or effect projection is built.
    if checked_required_resources.iter().any(|checked| {
        checked.role == CResourceTransferRole::Produce
            || checked.snapshot == CResourceSnapshot::Post
            || (checked.fact.is_view() && checked.role != CResourceTransferRole::Borrow)
    }) {
        return Ok(Err(CRuntimeError::FunctionContract(
            "resource requirement has an inconsistent transfer role".to_string(),
        )));
    }
    let Some(canonical_resources) = expand_all_composite_resource_facts(
        &required_resources,
        interface.composite_resource_definitions(),
        callee_state.memory(),
        assumptions,
    ) else {
        return Ok(Err(CRuntimeError::FunctionContract(format!(
            "could not expand required composite resources before call: {required_resources:?}"
        ))));
    };
    let canonical_resources = expand_decidable_composite_resource_frontier(
        &canonical_resources,
        interface.composite_resource_definitions(),
        callee_state.memory(),
        assumptions,
    );
    let population_body_resources = match evaluate_resource_population_body_resources(
        &required_resources,
        callee_state,
        interface.composite_resource_definitions(),
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
                interface.composite_resource_definitions(),
                callee_state.memory(),
                assumptions,
            ) {
                callee_resources =
                    callee_resources.unchecked_with_facts(expanded.facts().iter().cloned());
            }
        }
    }
    // Consumption uses the normalized algebraic context so duplicate token
    // clauses retain their quantity (and diagnostics name the complete
    // requirement).  The provenance-bearing list remains the effect source;
    // normalization is not allowed to erase its role/snapshot metadata.
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
            && interface
                .composite_resource_definitions()
                .iter()
                .any(|definition| definition.is_counted_population() && definition.name() == name)
            && !return_resources.satisfies_fact(resource, assumptions)
            && callee_state
                .counted_population(name, arguments)
                .is_some_and(|count| {
                    quantity_condition_holds(
                        assumptions,
                        ConditionTerm::Bitvector32Equal(
                            Box::new(count.clone()),
                            Box::new(Bitvector32Term::Constant(1)),
                        ),
                    )
                })
        {
            let singleton = ResourceContext::new().unchecked_with_fact(resource.clone());
            let body = match evaluate_resource_population_body_resources(
                &singleton,
                callee_state,
                interface.composite_resource_definitions(),
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
            interface.composite_resource_definitions(),
            caller_state.memory(),
            assumptions,
        ) else {
            return Ok(Err(CRuntimeError::MissingResource {
                resource: resource.clone(),
            }));
        };
        return_resources = resources;
    }
    let borrowed_inputs = checked_required_resources
        .iter()
        .filter(|checked| checked.role == CResourceTransferRole::Borrow)
        .cloned()
        .collect();
    let consumed_inputs = checked_required_resources
        .iter()
        .filter(|checked| checked.role == CResourceTransferRole::Consume)
        .cloned()
        .collect();
    Ok(Ok(CFunctionResourceTransfer {
        borrowed_inputs,
        consumed_inputs,
        callee_resources,
        caller_resources_after_requirements: return_resources,
        memory_effects: Vec::new(),
        post_outputs: None,
    }))
}

/// Evaluates the first `count` returned resources of a contract as one
/// jointly returned context. A borrowed resource (an `owns` clause) is
/// evaluated at `entry_state`: the callee returns exactly what it was lent,
/// even when the clause's address depends on a field the body writes. Every
/// other returned resource is evaluated at `post_state`, where the result and
/// the exit memory are visible.
pub(super) fn evaluate_function_return_resource_context(
    function: &CFunction,
    entry_state: &CState,
    post_state: &CState,
    count: usize,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceContext, CRuntimeError>> {
    evaluate_contract_return_resource_context(
        function.contract_interface(),
        entry_state,
        post_state,
        count,
        assumptions,
        budget,
    )
}

fn evaluate_contract_return_resource_context(
    interface: &CFunctionContractInterface,
    entry_state: &CState,
    post_state: &CState,
    count: usize,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceContext, CRuntimeError>> {
    let mut context = ResourceContext::new();
    for resource in interface.resource_ensures().iter().take(count) {
        // Snapshot selection is carried by the normalized specification. A
        // named instance is always post-evaluated by lowering, so its
        // identity remains stable while its fields can be fresh.
        let state = match resource.snapshot() {
            CResourceSnapshot::Entry => entry_state,
            CResourceSnapshot::Current | CResourceSnapshot::Post => post_state,
        };
        // A returned borrow is addressed through the cells the contract
        // already holds, including those a folded matched instance publishes
        // for its selected arm (D7). Without that read authority
        // `owns node->right->augmented` could be required at entry and then
        // fail to be evaluated at the very same state on return.
        let supply = state
            .resources()
            .clone()
            .unchecked_with_facts(context.facts().iter().cloned());
        let views = selected_instance_arm_views(
            &supply,
            interface.composite_resource_definitions(),
            state,
            assumptions,
        );
        let evaluation_state = state
            .clone()
            .with_resource_context(supply.unchecked_with_facts(views));
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

fn evaluate_function_return_resources(
    caller_resources_after_requirements: &ResourceContext,
    entry_state: &CState,
    post_state: &CState,
    function: &CFunction,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceContext, CRuntimeError>> {
    evaluate_contract_return_resources(
        caller_resources_after_requirements,
        entry_state,
        post_state,
        function.name(),
        function.contract_interface(),
        assumptions,
        budget,
    )
}

fn evaluate_contract_return_resources(
    caller_resources_after_requirements: &ResourceContext,
    entry_state: &CState,
    post_state: &CState,
    interface_name: &str,
    interface: &CFunctionContractInterface,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceContext, CRuntimeError>> {
    let ensured_resources = match crate::instrumentation::measure_operation(
        interface_name,
        "contract resource transition",
        "ensured resource lowering",
        || {
            evaluate_contract_return_resource_context(
                interface,
                entry_state,
                post_state,
                interface.resource_ensures().len(),
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
        interface_name,
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
        interface_name,
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
        interface_name,
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
                        interface.composite_resource_definitions(),
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

/// Population quantity relations are decided by exact routes only: syntactic
/// identity, constant folding, an indexed exact fact lookup, and the retained
/// atomic condition checker on the bare condition. No general proposition
/// search runs here; a relation that only follows logically becomes an
/// explicit obligation at the consuming operation.
fn population_quantity_is_zero(quantity: &Bitvector32Term, assumptions: &PureFactContext) -> bool {
    quantity == &Bitvector32Term::Constant(0)
        || quantity_condition_holds(
            assumptions,
            ConditionTerm::Bitvector32Equal(
                Box::new(quantity.clone()),
                Box::new(Bitvector32Term::Constant(0)),
            ),
        )
}

fn population_quantity_is_positive(
    quantity: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    quantity.as_const().is_some_and(|value| value > 0)
        || quantity_condition_holds(
            assumptions,
            ConditionTerm::Bitvector32SignedGreaterThan(
                Box::new(quantity.clone()),
                Box::new(Bitvector32Term::Constant(0)),
            ),
        )
}

fn population_quantities_are_equal(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    left == right
        || quantity_condition_holds(
            assumptions,
            ConditionTerm::Bitvector32Equal(Box::new(left.clone()), Box::new(right.clone())),
        )
}

fn resource_spec_has_snapshot_independent_footprint(resource: &CResourceSpec) -> bool {
    if resource.is_instance() {
        return false;
    }
    let term_independent = match resource.term() {
        CResourceTerm::Memory(segment) => {
            segment.guard.is_none()
                && c_expression_is_snapshot_independent(&segment.base)
                && c_expression_is_snapshot_independent(&segment.start)
                && c_expression_is_snapshot_independent(&segment.end)
        }
        CResourceTerm::Composite { arguments, .. } | CResourceTerm::Token { arguments, .. } => {
            arguments.iter().all(c_expression_is_snapshot_independent)
        }
        CResourceTerm::Instance { .. } => false,
    };
    term_independent
        && match resource.quantity() {
            CResourceQuantity::One => true,
            CResourceQuantity::Count(quantity) => c_expression_is_snapshot_independent(quantity),
        }
}

fn population_body_requires_positive_witness(definition: &CCompositeResourceDefinition) -> bool {
    fn resource_is_duplicable_view(resource: &CResourceSpec) -> bool {
        !resource.is_instance() && resource.is_view()
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
    apply_counted_population_transitions_with_interface(
        caller_state,
        post_state,
        Some(function),
        function.contract_interface(),
        argument_values,
        assumptions,
        reestablish_invariants,
        track_ordinary_populations,
        budget,
    )
}

fn apply_counted_population_transitions_with_interface(
    caller_state: &CState,
    post_state: &mut CState,
    evidence: Option<&CFunction>,
    interface: &CFunctionContractInterface,
    argument_values: &[CValue],
    assumptions: &PureFactContext,
    reestablish_invariants: bool,
    track_ordinary_populations: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CCountedPopulationTransition, CRuntimeError>> {
    let Some(mut entry_state) = evidence
        .map(|function| bind_c_function_arguments(caller_state, function, argument_values))
        .unwrap_or_else(|| bind_c_contract_arguments(caller_state, interface, argument_values))
    else {
        return Ok(Err(CRuntimeError::TypeMismatch));
    };
    // Resource formals belong to this call, just like the C argument views.
    entry_state.resource_bindings = post_state.resource_bindings.clone();
    let required = match evaluate_function_resource_context(
        &entry_state,
        interface.resource_requires(),
        interface.composite_resource_definitions(),
        assumptions,
        budget,
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    let post_contract_state =
        with_contract_interface_argument_views(post_state, interface, argument_values);
    let ensured = match evaluate_function_resource_context(
        &post_contract_state,
        interface.resource_ensures(),
        interface.composite_resource_definitions(),
        assumptions,
        budget,
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    let required_quantities = counted_population_quantities(
        &required,
        interface.composite_resource_definitions(),
        caller_state,
        assumptions,
        track_ordinary_populations,
    );
    let ensured_quantities = counted_population_quantities(
        &ensured,
        interface.composite_resource_definitions(),
        caller_state,
        assumptions,
        track_ordinary_populations,
    );
    let caller_quantities = counted_population_quantities(
        caller_state.resources(),
        interface.composite_resource_definitions(),
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
        let declared_population_definition = interface
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
                    interface.composite_resource_definitions(),
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
                    interface.composite_resource_definitions(),
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
        let population_ends = consumes_entire_population
            || bitvector_terms_proven_equal_for_memory_resolution(
                &new_count,
                &Bitvector32Term::Constant(0),
                assumptions,
            )
            || quantity_condition_holds(
                assumptions,
                ConditionTerm::Bitvector32Equal(
                    Box::new(new_count.clone()),
                    Box::new(Bitvector32Term::Constant(0)),
                ),
            );
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
                    interface.composite_resource_definitions(),
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
                    interface.composite_resource_definitions(),
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
                                && quantity_condition_holds(
                                    assumptions,
                                    ConditionTerm::Bitvector32SignedGreaterEqual(
                                        Box::new(required_quantity.clone()),
                                        Box::new(Bitvector32Term::Constant(0)),
                                    ),
                                )
                                && quantity_condition_holds(
                                    assumptions,
                                    ConditionTerm::Bitvector32SignedLessEqual(
                                        Box::new(required_quantity.clone()),
                                        Box::new(prior.clone()),
                                    ),
                                )
                        });
                if residual_is_certified_nonnegative
                    || quantity_condition_holds(
                        assumptions,
                        ConditionTerm::Bitvector32SignedGreaterEqual(
                            Box::new(new_count.clone()),
                            Box::new(ensured_quantity.clone()),
                        ),
                    )
                {
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
    let post_contract_state =
        with_contract_interface_argument_views(post_state, interface, argument_values);
    let mut active_populations = Vec::new();
    for population in post_contract_state.counted_populations() {
        if population_quantity_is_zero(&population.count, assumptions) {
            continue;
        }
        let population_body =
            interface
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
        interface.composite_resource_definitions(),
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
        // The transition's own algebraic guarantee, then the retained exact
        // routes. Anything else is a genuine verification condition for a
        // Surface tactic, not something for lowering to prove here.
        if !transition_guaranteed_facts.contains(&proposition) {
            add_required_proof_obligation_with_context(
                &mut transition.postcondition_obligations,
                assumptions,
                proposition,
                Some("resource population invariant"),
                None,
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
            prepare_contract_resource_transfer(
                caller_state,
                &callee_state,
                function.name(),
                function.contract_interface(),
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
    let child_name = definition.contains().iter().find_map(|spec| {
        let arguments = spec.declared_arguments()?;
        (spec.family() == ResourceFamily::Composite
            && matches!(arguments, [CExpression::Variable(argument)] if argument == witness))
        .then(|| spec.declared_name().expect("composite spec has a name"))
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
                ..
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
/// Recursive children require explicit independent child selections.
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
        std::slice::from_ref(definition),
        assumptions,
        unfold,
        None,
    )
}

/// The composite definition a matched arm's child names. A child of the
/// parent's own family resolves to the definition already in hand; any other
/// declared resource is looked up in the registered definitions, so the
/// child's own parameters and fields decide what the rewrite checks.
pub(in crate::kernel) fn child_composite_definition<'a>(
    definition: &'a CCompositeResourceDefinition,
    definitions: &'a [CCompositeResourceDefinition],
    child: &CResourceChildSpec,
) -> Result<&'a CCompositeResourceDefinition, &'static str> {
    if child.resource == definition.name() {
        return Ok(definition);
    }
    definitions
        .binary_search_by(|candidate| candidate.name().cmp(&child.resource))
        .ok()
        .map(|index| &definitions[index])
        .ok_or("resource match child has no registered definition")
}

pub(crate) fn rewrite_resource_instance_selecting_children(
    state: &CState,
    instance: &ResourceInstance,
    definition: &CCompositeResourceDefinition,
    definitions: &[CCompositeResourceDefinition],
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
            .any(|body| body.family() != ResourceFamily::Memory || body.is_view())
    {
        return Err("instance fold/unfold requires a nonrecursive, witness-free memory body");
    }
    let folded_instance = instance.clone();
    let folded = CResourceFact::own(CResource::Instance(folded_instance.clone()));
    if unfold {
        if state.resources.owned_instance(instance.identity) != Some(instance) {
            return Err("instance is not exclusively owned in folded form");
        }
    } else if state.resources.owned_instance(instance.identity).is_some() {
        return Err("fold result identity is already in use");
    }
    let mut evaluation = instance_body_evaluation(state, instance, definition)?;
    let mut budget = ExecutionBudget::default();
    let mut algebraic_bindings = BTreeMap::new();
    let mut integer_bindings = BTreeMap::new();
    let mut constructor_fields = Vec::new();
    let selected = if definition.matched.is_some() {
        let (arm, constructor) =
            selected_instance_match_arm(instance, definition, definitions, assumptions)?;
        let AlgebraicTermNode::Constructor { fields, .. } = constructor.node else {
            unreachable!()
        };
        constructor_fields = fields.clone();
        for (index, value) in fields.iter().enumerate() {
            let name = arm
                .bindings
                .get(index)
                .ok_or("resource match binding count mismatch")?;
            let binding_type = arm
                .binding_types
                .get(index)
                .ok_or("resource match binding type count mismatch")?;
            let binding_variable = arm
                .binding_variables
                .get(index)
                .ok_or("resource match Integer binding identity count mismatch")?;
            match (binding_type, binding_variable, value) {
                (AlgebraicValueType::C(_), None, AlgebraicValue::C(value)) => {
                    let ty = value.c_type();
                    evaluation.locals.set_typed(name.clone(), value.clone(), ty);
                }
                (AlgebraicValueType::Integer, Some(variable), AlgebraicValue::Integer(value)) => {
                    if integer_bindings.insert(*variable, value.clone()).is_some() {
                        return Err("resource match Integer bindings reuse an identity");
                    }
                }
                (AlgebraicValueType::Algebraic { .. }, None, AlgebraicValue::Algebraic(value)) => {
                    algebraic_bindings.insert(name.clone(), value.clone());
                }
                _ => return Err("resource match constructor binding type mismatch"),
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
    if explicit_children.is_none() && selected.is_some_and(|arm| !arm.children.is_empty()) {
        return Err("recursive children require explicit independent child selections");
    }
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
        // A resource body is rewritten against its own declared memory only;
        // expanding a contained composite here would hand the body read
        // authority it has not opened.
        &[],
        assumptions,
        &mut budget,
        false,
    )
    .map_err(|_| "instance body evaluation exceeded its budget")?
    .map(|(context, _)| context)
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
    let mut resource_bindings = BTreeMap::from([(Variable(u64::MAX), instance.identity)]);
    for child in selected.into_iter().flat_map(|arm| &arm.children) {
        crate::instrumentation::record_deterministic_work(1);
        // The child's own definition supplies the parameter types its
        // arguments are coerced to and the schema its fields must satisfy.
        let child_definition = child_composite_definition(definition, definitions, child)?;
        let child_schema = if child_definition.name() == definition.name() {
            instance.schema.clone()
        } else {
            child_definition
                .instance_schema
                .clone()
                .ok_or("resource match child requires a field-bearing definition")?
        };
        let arguments = child
            .arguments
            .iter()
            .zip(&child_definition.parameters)
            .map(|(argument, parameter)| {
                let paths = evaluate_c_expression_paths(
                    &child_evaluation,
                    argument,
                    &child_assumptions,
                    &mut budget,
                )
                .map_err(|_| "recursive child argument evaluation exceeded its budget")?;
                // A child argument is a prerequisite of the rewrite, not a
                // proof site: it has no obligation vector to receive an
                // unmet condition. Restrict it to the retained exact routes
                // and refuse the rewrite otherwise, which is the
                // conservative equivalent of emitting the obligation.
                if paths.len() != 1
                    || paths[0].facts.iter().any(|fact| {
                        !required_obligation_is_exactly_discharged(
                            &child_assumptions,
                            fact.proposition(),
                        )
                    })
                    || paths[0].obligations.iter().any(|goal| {
                        !required_obligation_is_exactly_discharged(
                            &child_assumptions,
                            goal.proposition(),
                        )
                    })
                {
                    return Err("recursive child argument requires a proved, readable expression");
                }
                match &paths[0].outcome {
                    CExpressionOutcome::Value(value) => {
                        coerce_c_function_argument_without_obligations(value, parameter)
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
        let identity =
            explicit_children.as_ref().expect("checked child selection")[child.name.as_str()];
        if unfold && state.resources.owned_instance(identity).is_some() {
            return Err("unfold child result identity is already in use");
        }
        let mut child_instance = ResourceInstance::new(
            identity,
            child_definition.name().to_string(),
            arguments,
            child_schema,
            fields,
        )
        .ok_or("recursive child fields or arguments have invalid types")?;
        if child_instance.arguments.len() != child_definition.parameters.len()
            || child_instance
                .arguments
                .iter()
                .zip(&child_definition.parameters)
                .any(|(argument, parameter)| {
                    argument
                        .as_c_value()
                        .is_none_or(|value| value.c_type() != parameter.c_type())
                })
        {
            return Err("recursive child arguments have invalid types");
        }
        if !unfold {
            let actual = state
                .resources
                .owned_instance(identity)
                .ok_or("fold requires an owned, folded child")?;
            if actual.name != child_instance.name
                || actual.schema != child_instance.schema
                || actual.arguments.len() != child_instance.arguments.len()
                || actual.fields.len() != child_instance.fields.len()
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
    }
    evaluation.resources = if unfold {
        next.resources.clone()
    } else {
        state.resources.clone()
    };
    evaluation.resource_bindings = Some(std::sync::Arc::new(resource_bindings));
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
    let c_replacements = BTreeMap::new();
    let algebraic_replacements = BTreeMap::new();
    let mut fact_rewrite =
        crate::kernel::proof::term_rewrite::TermRewrite::for_checked_typed_variables(
            &c_replacements,
            &integer_bindings,
            &algebraic_replacements,
        );
    // A matched Integer binding may occur inside the pointer offset of a
    // registered load in a body fact.  Resolve that selected load origin
    // while rewriting the fact so the replacement is applied to the pointer
    // and the result is re-minted in the same memory snapshot.  The checked
    // TermRewrite path keeps the registry DAG bounded and rejects cycles.
    fact_rewrite.enable_registered_load_resolution();
    let facts_to_rewrite = selected.map_or(&definition.facts, |arm| &arm.facts);
    fact_rewrite
        .reserve_spec_proposition_sources(facts_to_rewrite.iter())
        .map_err(|_| "resource match Integer binding substitution exceeded its checked scope")?;
    for fact in facts_to_rewrite.iter().filter(|_| active) {
        let fact = fact_rewrite.spec_proposition(fact).map_err(
            |_| "resource match Integer binding substitution exceeded its checked scope",
        )?;
        let paths = crate::kernel::spec::lower_spec_proposition_at_state_with_algebraic_bindings(
            &evaluation,
            &fact,
            None,
            &body_assumptions,
            &algebraic_bindings,
            &mut budget,
        )
        .map_err(|_| "could not evaluate instance body fact")?;
        if paths.len() != 1 {
            return Err("instance body fact needs an unsupported conditional proof");
        }
        let path = paths
            .into_iter()
            .next()
            .ok_or("instance body fact produced no evaluation path")?;
        if path.facts.iter().any(|fact| {
            !required_obligation_is_exactly_discharged(&body_assumptions, fact.proposition())
        }) || path.obligations.iter().any(|goal| {
            !required_obligation_is_exactly_discharged(&body_assumptions, goal.proposition())
        }) {
            return Err("instance body fact needs an unsupported conditional proof");
        }
        let proposition = path.proposition;
        // The fold prerequisite is a rewrite precondition with no obligation
        // vector of its own; the exact routes decide it or the fold is
        // refused with this diagnostic.
        if !unfold && !required_obligation_is_exactly_discharged(assumptions, &proposition) {
            return Err("fold requires the instance body facts for the proposed fields");
        }
        facts.push(proposition);
    }
    Ok((next, if unfold { facts } else { vec![] }))
}

pub(in crate::kernel) fn selected_instance_match_arm<'a>(
    instance: &ResourceInstance,
    definition: &'a CCompositeResourceDefinition,
    definitions: &'a [CCompositeResourceDefinition],
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
                    **fields != arm.binding_types
                        || fields.len() != arm.bindings.len()
                        || arm.binding_variables.len() != arm.bindings.len()
                })
            || arm.bindings.iter().any(|name| {
                name.is_empty() || !names.insert(name) || reserved.contains(name.as_str())
            })
            || arm.binding_variables.iter().zip(&arm.binding_types).any(
                |(variable, binding_type)| match binding_type {
                    AlgebraicValueType::Integer => variable.is_none(),
                    _ => variable.is_some(),
                },
            )
            || arm
                .contains
                .iter()
                .any(|resource| resource.family() != ResourceFamily::Memory || resource.is_view())
        {
            return Err("invalid resource match arm");
        }
        let mut integer_binding_variables = BTreeSet::new();
        for (variable, binding_type) in arm.binding_variables.iter().zip(&arm.binding_types) {
            if binding_type == &AlgebraicValueType::Integer
                && !integer_binding_variables.insert(variable.expect("checked above"))
            {
                return Err("resource match Integer bindings reuse an identity");
            }
        }
        let mut child_names = BTreeSet::new();
        let mut child_bindings = BTreeSet::new();
        for child in &arm.children {
            // A child is checked against its own definition, which is the
            // parent's for a directly recursive child and another declared
            // resource otherwise.
            let child_definition = child_composite_definition(definition, definitions, child)?;
            let child_schema = if child_definition.name() == definition.name() {
                instance.schema()
            } else {
                child_definition
                    .instance_schema
                    .as_ref()
                    .ok_or("resource match child requires a field-bearing definition")?
            };
            if child.name.is_empty()
                || reserved.contains(child.name.as_str())
                || names.contains(&child.name)
                || !child_names.insert(&child.name)
                || child.binding == Variable(u64::MAX)
                || !child_bindings.insert(child.binding)
                || child.arguments.len() != child_definition.parameters.len()
                || child.field_bindings.len() != child_schema.fields().len()
            {
                return Err("invalid recursive child schema");
            }
            for ((_, field_type), index) in child_schema.fields().iter().zip(&child.field_bindings)
            {
                let expected = match field_type {
                    ResourceFieldType::Integer => AlgebraicValueType::Integer,
                    ResourceFieldType::C(ty) => AlgebraicValueType::C(*ty),
                    ResourceFieldType::Algebraic(ty) => ty.value_type(),
                };
                if arm.binding_types.get(*index) != Some(&expected) {
                    return Err(
                        "recursive child fields must be immediate constructor bindings of the declared type",
                    );
                }
            }
            // In particular, a same-family child's model is bound to a field
            // of this constructor, never to the whole parent model. A child of
            // another family has no such field; its own matched field is
            // already checked above, against its own declared type.
            if child_definition.name() == definition.name()
                && arm
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
    // Fold and unfold bind the arm's fields, so they need the constructor
    // itself: an arm merely entailed by the premises (D7) grants reading, not
    // the values a rewrite would substitute.
    let Some(ResourceModelArmSelection::Constructor(constructor)) =
        select_resource_model_arm(model, assumptions)
    else {
        return Err("resource match requires constructor evidence for the instance field");
    };
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

/// Which arm of a matched resource model one section's premises select.
///
/// `Constructor` carries the model's own constructor application, so the arm's
/// bindings have values. `Variant` names the arm without naming its fields:
/// the premises rule out every other variant, or witness this one, but no
/// premise says what it holds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResourceModelArmSelection {
    Constructor(AlgebraicTerm),
    Variant(String),
}

impl ResourceModelArmSelection {
    pub fn variant(&self) -> &str {
        match self {
            Self::Constructor(constructor) => match &constructor.node {
                AlgebraicTermNode::Constructor { variant, .. } => variant,
                _ => unreachable!("a selected constructor term is a constructor application"),
            },
            Self::Variant(variant) => variant,
        }
    }
}

/// The one arm-selection decision in Click: premises plus constructor
/// exhaustiveness against one matched model value.
///
/// Contract lowering asks it for a `requires`-selected arm; a loop head asks
/// the same question with its invariants playing the part of the requirements,
/// and a fold or unfold asks it through [`selected_instance_match_arm`], which
/// needs the stronger `Constructor` answer because it binds the arm's fields.
///
/// Selection is decided, never searched: a constructor premise answers
/// outright, an existential premise witnesses one variant, and disequalities
/// against field-free constructors rule variants out until one is left. Any
/// other state of evidence is `None` — the caller keeps the model folded
/// rather than proving by cases.
///
/// Cost is the number of premises about this exact value plus the declared
/// variants of its type. Unrelated premises are never visited.
pub fn select_resource_model_arm(
    model: &AlgebraicTerm,
    assumptions: &PureFactContext,
) -> Option<ResourceModelArmSelection> {
    if let Some(constructor) = assumptions.known_algebraic_constructor(model) {
        return Some(ResourceModelArmSelection::Constructor(constructor));
    }
    let AlgebraicTermNode::Variable(variable) = &model.node else {
        return None;
    };
    let declared = model
        .algebraic_type
        .variants
        .iter()
        .map(|variant| variant.name.as_str())
        .collect::<BTreeSet<_>>();
    if declared.is_empty() {
        return None;
    }
    let mut witnessed = BTreeMap::new();
    let mut excluded = BTreeMap::new();
    for (premise, evidence) in assumptions.algebraic_variant_evidence(*variable) {
        if !declared.contains(evidence.variant.as_str()) {
            continue;
        }
        match evidence.kind {
            AlgebraicVariantEvidenceKind::Witnessed => {
                witnessed.insert(evidence.variant.as_str(), premise);
            }
            AlgebraicVariantEvidenceKind::Excluded => {
                excluded.insert(evidence.variant.as_str(), premise);
            }
        }
    }
    // A witness names its arm directly. Two witnesses would need the context
    // to be inconsistent, which is not this decision's business to exploit.
    // Cite what decided the arm, so an expansion of the selected arm names the
    // premises a reader would look for.
    let selected = if let [(variant, premise)] = witnessed.iter().collect::<Vec<_>>().as_slice() {
        super::assumptions::record_reasoning_provenance(assumptions, premise);
        **variant
    } else if witnessed.is_empty() {
        let excluded_variants = excluded.keys().copied().collect::<BTreeSet<_>>();
        let mut remaining = declared.difference(&excluded_variants);
        let first = *remaining.next()?;
        if remaining.next().is_some() {
            return None;
        }
        for premise in excluded.values() {
            super::assumptions::record_reasoning_provenance(assumptions, premise);
        }
        first
    } else {
        return None;
    };
    Some(ResourceModelArmSelection::Variant(selected.to_string()))
}

fn instance_body_evaluation(
    state: &CState,
    instance: &ResourceInstance,
    definition: &CCompositeResourceDefinition,
) -> Result<CState, &'static str> {
    let mut evaluation = state.clone();
    {
        // A local interpretation of proposed fields, never ownership or a
        // persistent open handle. Guards may refer to these fields as well.
        evaluation.instance_field_scope = evaluation
            .instance_field_scope
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

/// The proposition asserting the opposite of `proposition`, without adding a
/// logical rule: a bare condition flips its value, a negation drops, and
/// anything else is wrapped in one `Not`.
fn negated_contract_proposition(proposition: &Proposition) -> Proposition {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            Proposition::ConditionIs(condition.clone(), !value)
        }
        Proposition::Not(body) => body.as_ref().clone(),
        proposition => Proposition::Not(Box::new(proposition.clone())),
    }
}

/// Decide one lowered contract guard by the retained exact routes only:
/// `Some(true)` when the guard holds, `Some(false)` when its opposite does,
/// and `None` when neither is decided.
///
/// `None` is not "false". It is the answer that leaves the choice to the
/// consumer — which refuses the refinement, keeps both specification paths,
/// or emits an obligation — instead of letting a general proof search inside
/// the kernel settle a contract branch.
fn guard_value_by_exact_routes(assumptions: &PureFactContext, guard: &Proposition) -> Option<bool> {
    if required_obligation_is_exactly_discharged(assumptions, guard) {
        return Some(true);
    }
    required_obligation_is_exactly_discharged(assumptions, &negated_contract_proposition(guard))
        .then_some(false)
}

/// Decide one guard: `Some(true)`, `Some(false)`, or `None` for undecided.
///
/// Package 10(b) removed the general-prover leg, so every answer now comes
/// from the exact fact index, the frozen condition checker on a bare
/// condition, or the frozen atomic memory/resource checkers. An undecided
/// guard travels to the caller, which keeps both specification paths or
/// refuses the operation.
///
/// `resource_guard_conjunction` is the reaching fixture for a guard that is
/// not a bare condition. The obligation check below has no reaching fixture:
/// a guard is the condition of a resource body, and a resource condition must
/// be load-free, so the lowered guard path carries no obligation.
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
    if !path.obligations.iter().all(|obligation| {
        required_obligation_is_exactly_discharged(assumptions, obligation.proposition())
    }) {
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
        // No general prover leg. A guard this does not decide is undecided,
        // and the caller keeps both specification paths or refuses the
        // operation rather than having the kernel search for a proof.
        _ => required_obligation_is_exactly_discharged(assumptions, proposition),
    };
    if proves_body_condition(&path.proposition) {
        super::assumptions::record_reasoning_provenance(assumptions, &path.proposition);
        return Some(true);
    }
    let false_proposition = negated_contract_proposition(&path.proposition);
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
    // A token or composite target that the starting context already holds
    // needs no unfolding, and the starting context is the first one the
    // search below would accept. Answering from the index first keeps
    // exposing each of a context's members from re-expanding every composite
    // it still holds, which made exposing all of them quadratic.
    if !structural && context.satisfies_fact(target, assumptions) {
        return Some(context.clone());
    }
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
                    if required_obligation_is_exactly_discharged(
                        &fact_assumptions,
                        obligation.proposition(),
                    ) {
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
        let Some(segment) = resource.memory_segment() else {
            continue;
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
                if required_obligation_is_exactly_discharged(
                    &fact_assumptions,
                    obligation.proposition(),
                ) {
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

/// Whether a body outcome establishes every resource the contract returns,
/// by the rule contract certification applies to a `produces` claim: each
/// returned resource, read as one jointly returned context, is satisfied by
/// the body's returned context definitionally, so a composite whose pieces
/// and facts the body holds counts as returned, and a duplicable body such
/// as a view yields any quantity, while a consumed cell the body no longer
/// holds does not.
pub(super) fn function_return_resources_definitionally_established(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    outcome: &CFunctionOutcome,
    assumptions: &PureFactContext,
) -> bool {
    let CFunctionOutcome::Return {
        value,
        state: return_state,
    } = outcome
    else {
        return false;
    };
    let Some(argument_values) = arguments
        .iter()
        .map(|argument| match argument {
            CExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    let Some(callee_state) = bind_c_function_arguments(caller_state, function, &argument_values)
    else {
        return false;
    };
    let exit_memory = function_exit_memory(caller_state, return_state, value, function);
    let mut claim_return_state = return_state.clone();
    claim_return_state.memory = exit_memory.clone();
    let definitions = function.composite_resource_definitions();
    let Some(post_resources) = expand_all_composite_resource_facts(
        claim_return_state.resources(),
        definitions,
        claim_return_state.memory(),
        assumptions,
    ) else {
        return false;
    };
    let Ok(post_resource_facts) = post_resources.observable_facts(assumptions) else {
        return false;
    };
    let assumptions = assumptions_with_propositions(assumptions, &post_resource_facts);
    let mut post_state = callee_state.with_memory(exit_memory);
    post_state.resources = post_resources;
    post_state.counted_populations = return_state.counted_populations.clone();
    if function.return_type() != CType::Void {
        post_state
            .locals
            .set_typed("result".to_string(), value.clone(), function.return_type());
    }
    let mut budget = ExecutionBudget::default();
    let entry_resource_state =
        with_contract_argument_views(caller_state, function, &argument_values);
    let Ok(Ok(expected)) = evaluate_function_return_resource_context(
        function,
        &entry_resource_state,
        &post_state,
        function.resource_ensures().len(),
        &assumptions,
        &mut budget,
    ) else {
        return false;
    };
    expected.facts().iter().all(|fact| {
        resource_context_satisfies_definitional_fact(
            claim_return_state.resources(),
            fact,
            definitions,
            claim_return_state.memory(),
            &assumptions,
        )
    })
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

pub(crate) fn evaluate_function_resource_context(
    state: &CState,
    resources: &[CResourceSpec],
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceContext, CRuntimeError>> {
    evaluate_function_resource_context_with_metadata(
        state,
        resources,
        definitions,
        assumptions,
        budget,
    )
    .map(|result| result.map(|(context, _)| context))
}

/// Evaluate a resource section once and retain the source metadata alongside
/// each checked fact.  The ordinary context API below is a compatibility view
/// for callers that only need algebraic containment; transition/effect code
/// must use this provenance-bearing result.
pub(crate) fn evaluate_function_resource_context_with_metadata(
    state: &CState,
    resources: &[CResourceSpec],
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(ResourceContext, Vec<CCheckedResourceFact>), CRuntimeError>> {
    evaluate_function_resource_context_with_normalization(
        state,
        resources,
        definitions,
        assumptions,
        budget,
        true,
    )
}

fn evaluate_function_resource_context_with_normalization(
    state: &CState,
    resources: &[CResourceSpec],
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    normalize: bool,
) -> ExecutionResult<Result<(ResourceContext, Vec<CCheckedResourceFact>), CRuntimeError>> {
    let evaluated = match evaluate_resource_clauses_against_whole_section(
        state,
        resources,
        definitions,
        assumptions,
        budget,
    )? {
        Ok(evaluated) => evaluated,
        Err(error) => return Ok(Err(error)),
    };
    let mut context = ResourceContext::new();
    let checked = evaluated;
    for resource in &checked {
        // Instance rewrites retain the declared memory pieces so folding does
        // not need to normalize an ambient block just to consume those pieces.
        let composed = if normalize {
            context.try_compose_with_fact(resource.fact.clone(), assumptions)
        } else {
            context.try_compose_into_valid_context_delaying_normalization(
                [resource.fact.clone()],
                assumptions,
            )
        };
        context = match composed {
            Ok(context) => context,
            Err(error) => return Ok(Err(resource_context_runtime_error(error))),
        };
    }
    Ok(Ok((context, checked)))
}

/// Evaluates one contract section's resource clauses against the loadability
/// the whole section supplies, and returns their resources in source order.
///
/// A base load in one clause may read a cell any other clause of the same
/// section owns or views, including a cell inside a folded composite, exactly
/// as a `requires` clause may. The first pass walks the clauses in source
/// order. If it leaves clauses unevaluated, the successful portion is expanded
/// once and the missing-resource edges recorded by each failed clause drive an
/// indexed event queue. A newly supplied memory fact therefore wakes only its
/// dependent clauses; no fixed-point round rescans all pending clauses.
///
/// Each clause contributes its resource exactly once: a clause that evaluates
/// is never revisited, and the caller composes the results once, in source
/// order. Retrying a clause that has not yet produced a resource cannot
/// double-count authority.
///
/// Clauses that no order evaluates are refused by name. That is the honest
/// verdict for a dependency cycle between two clauses and for two clauses that
/// are independently unevaluable; either way the user needs both positions.
fn evaluate_resource_clauses_against_whole_section(
    state: &CState,
    resources: &[CResourceSpec],
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<Vec<CCheckedResourceFact>, CRuntimeError>> {
    let mut evaluated: Vec<Option<CResourceFact>> = vec![None; resources.len()];
    let mut supplied: Vec<CResourceFact> = Vec::new();
    let mut failures: Vec<Option<CRuntimeError>> = vec![None; resources.len()];
    let mut dependencies: Vec<Vec<CResourceFact>> = vec![Vec::new(); resources.len()];
    let mut waiters = ResourceClauseWaiterIndex::default();
    for (index, resource) in resources.iter().enumerate() {
        let evaluation_state = state.clone().with_resource_context(
            state
                .resources()
                .clone()
                .unchecked_with_facts(supplied.iter().cloned()),
        );
        let (outcome, missing) = evaluate_resource_clause_with_dependencies(
            &evaluation_state,
            resource,
            assumptions,
            budget,
        )?;
        match outcome {
            Ok(resource) => {
                supplied.push(resource.clone());
                evaluated[index] = Some(resource);
            }
            Err(error) => {
                failures[index] = Some(error);
                resource_clause_register_waiters(index, missing, &mut dependencies, &mut waiters);
            }
        }
    }
    let mut section_supply =
        resource_clause_section_supply(state, &supplied, definitions, assumptions);
    let mut pending = VecDeque::new();
    let mut queued = vec![false; resources.len()];
    for index in 0..resources.len() {
        if evaluated[index].is_none()
            && dependencies[index]
                .iter()
                .any(|dependency| section_supply.satisfies_fact(dependency, assumptions))
        {
            queued[index] = true;
            pending.push_back(index);
        }
    }
    while let Some(index) = pending.pop_front() {
        queued[index] = false;
        if evaluated[index].is_some() {
            continue;
        }
        resource_clause_unregister_waiters(index, &mut dependencies, &mut waiters);
        let evaluation_state = state.clone().with_resource_context(section_supply.clone());
        let (outcome, missing) = evaluate_resource_clause_with_dependencies(
            &evaluation_state,
            &resources[index],
            assumptions,
            budget,
        )?;
        match outcome {
            Ok(resource) => {
                let (next_supply, newly_supplied) = resource_clause_supply_with_fact(
                    section_supply,
                    resource.clone(),
                    definitions,
                    state.memory(),
                    assumptions,
                );
                section_supply = next_supply;
                supplied.push(resource.clone());
                evaluated[index] = Some(resource);
                failures[index] = None;
                for fact in newly_supplied {
                    resource_clause_enqueue_waiters(
                        &fact,
                        assumptions,
                        &section_supply,
                        &evaluated,
                        &mut queued,
                        &mut pending,
                        &dependencies,
                        &waiters,
                    );
                }
            }
            Err(error) => {
                failures[index] = Some(error);
                resource_clause_register_waiters(index, missing, &mut dependencies, &mut waiters);
            }
        }
    }
    // A clause refused for its own shape is reported at its own position: no
    // other clause's authority was ever going to repair it, so naming a pair
    // would send the user to a clause that is fine.
    let unresolved = evaluated
        .iter()
        .enumerate()
        .filter_map(|(index, resource)| resource.is_none().then_some(index))
        .collect::<Vec<_>>();
    let refused = unresolved
        .iter()
        .copied()
        .filter(|index| {
            let error = failures[*index].as_ref();
            let awaits = !dependencies[*index].is_empty()
                || error.is_some_and(resource_clause_failure_awaits_supply);
            !awaits
        })
        .min_by_key(|index| resource_clause_position(resources, *index));
    if let Some(index) = refused.or_else(|| {
        unresolved
            .iter()
            .copied()
            .min_by_key(|index| resource_clause_position(resources, *index))
    }) {
        let error = failures[index]
            .take()
            .unwrap_or_else(|| CRuntimeError::FunctionContract("unevaluated".to_string()));
        let cycle = refused
            .is_none()
            .then(|| {
                let source_index = resource_clause_position(resources, index).0;
                unresolved
                    .iter()
                    .copied()
                    .filter(|other| {
                        *other != index
                            && resource_clause_position(resources, *other).0 != source_index
                    })
                    .min_by_key(|other| resource_clause_position(resources, *other))
                    .map(|other| (index, other))
            })
            .flatten();
        return Ok(Err(match cycle {
            Some((index, other)) => {
                resource_clause_cycle_runtime_error(error, index, other, resources)
            }
            None => resource_clause_runtime_error(error, index, resources),
        }));
    }
    Ok(Ok(evaluated
        .into_iter()
        .enumerate()
        .filter_map(|(index, fact)| {
            fact.map(|fact| CCheckedResourceFact {
                fact,
                role: resources[index].role(),
                snapshot: resources[index].snapshot(),
                clause_position: resources[index].clause_position(),
            })
        })
        .collect()))
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ResourceClauseDependencyKey {
    Fact(CResourceFact),
    MemoryBase(Pointer),
    MemoryBlock(PointerBlock),
}

/// A sparse segment-tree coordinate space for a concrete memory block.
///
/// The range bounds are normalized to the block's physical byte coordinate,
/// using the pointer base's proven constant byte offset and checked element
/// widths.  Keeping the base out of the key is what lets a clause based at
/// `p + 2` wake a clause based at `p`, while refusing to compare symbolic
/// pointer offsets.  A non-concrete base or bound uses the bounded block/base
/// fallback below instead.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ResourceClauseIntervalSpace {
    block: PointerBlock,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ResourceClauseIntervalNode {
    space: ResourceClauseIntervalSpace,
    /// `level` is the base-2 logarithm of the node's byte span.  The root
    /// is level 32 and the leaves are level 0; no node represents individual
    /// cells outside this fixed-depth index.
    level: u8,
    start: u32,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ResourceClauseIntervalWaiter {
    clause: usize,
    dependency: usize,
}

#[derive(Default)]
struct ResourceClauseIntervalIndex {
    exact: BTreeMap<ResourceClauseIntervalNode, BTreeSet<ResourceClauseIntervalWaiter>>,
    /// Subtree aggregates are used only when a query fully covers a node.
    /// Partial queries follow their two boundary paths, so a tiny supplied
    /// range never reads the root aggregate and never wakes every waiter in a
    /// block.  Each update touches at most 33 ancestors per canonical range
    /// node, independent of the number of memory cells in that range.
    subtree: BTreeMap<ResourceClauseIntervalNode, BTreeSet<ResourceClauseIntervalWaiter>>,
}

#[derive(Default)]
struct ResourceClauseWaiterIndex {
    coarse: BTreeMap<ResourceClauseDependencyKey, BTreeSet<usize>>,
    /// Concrete waiters also have a block-local fallback entry.  It is used
    /// only when the *supplied* memory fact cannot be normalized to a
    /// concrete interval: a symbolic event has no interval key to query, but
    /// its explicit block is still a sound conservative candidate boundary.
    /// Store the dependency index as well as the clause so register/remove
    /// stay symmetric when one clause waits on multiple ranges in a block.
    concrete_block_fallback: BTreeMap<PointerBlock, BTreeSet<ResourceClauseIntervalWaiter>>,
    intervals: ResourceClauseIntervalIndex,
}

/// Returns a concrete, block-relative byte interval when the base and both
/// bounds have a checked signed integer interpretation.  The interval index
/// is deliberately conservative: ranges that cannot be normalized into the
/// fixed 32-bit coordinate universe remain on the symbolic block/base path.
fn resource_clause_concrete_memory_interval(
    range: &CMemoryRange,
) -> Option<(ResourceClauseIntervalSpace, i64, i64)> {
    let base_offset = range.base().offset.as_const()?;
    let start_elements = signed_bitvector_constant(range.start())?;
    let end_elements = signed_bitvector_constant(range.end())?;
    if start_elements >= end_elements {
        return None;
    }
    let element_width = i64::from(range.element_width());
    let start = base_offset.checked_add(start_elements.checked_mul(element_width)?)?;
    let byte_count = end_elements
        .checked_sub(start_elements)?
        .checked_mul(element_width)?;
    let end = start.checked_add(byte_count)?;
    if !(i64::from(i32::MIN)..=i64::from(i32::MAX)).contains(&start)
        || !(i64::from(i32::MIN)..=i64::from(i32::MAX)).contains(&end)
    {
        return None;
    }
    Some((
        ResourceClauseIntervalSpace {
            block: range.base().block.clone(),
        },
        start,
        end,
    ))
}

fn resource_clause_biased_coordinate(value: i64) -> Option<u64> {
    (i64::from(i32::MIN)..=i64::from(i32::MAX))
        .contains(&value)
        .then_some((value - i64::from(i32::MIN)) as u64)
}

fn resource_clause_interval_node_start(coordinate: u64, level: u8) -> u32 {
    if level >= 32 {
        0
    } else {
        ((coordinate >> level) << level) as u32
    }
}

fn resource_clause_interval_node(
    space: &ResourceClauseIntervalSpace,
    level: u8,
    start: u32,
) -> ResourceClauseIntervalNode {
    ResourceClauseIntervalNode {
        space: space.clone(),
        level,
        start,
    }
}

/// Canonical segment-tree decomposition of `[start, end)`.  A range is
/// represented by O(32) aligned nodes, rather than by its cells.
fn resource_clause_interval_nodes(
    space: &ResourceClauseIntervalSpace,
    start: i64,
    end: i64,
) -> Option<Vec<ResourceClauseIntervalNode>> {
    let mut start = resource_clause_biased_coordinate(start)?;
    let end = resource_clause_biased_coordinate(end)?;
    if start >= end {
        return None;
    }
    let mut nodes = Vec::new();
    while start < end {
        let alignment = if start == 0 {
            32
        } else {
            start.trailing_zeros().min(32)
        };
        let remaining = end - start;
        let magnitude = 63 - remaining.leading_zeros();
        let level = alignment.min(magnitude).min(32) as u8;
        let node_start = resource_clause_interval_node_start(start, level);
        nodes.push(resource_clause_interval_node(space, level, node_start));
        start += 1u64 << level;
    }
    Some(nodes)
}

fn resource_clause_interval_node_ancestors(
    node: &ResourceClauseIntervalNode,
) -> Vec<ResourceClauseIntervalNode> {
    (node.level..=32)
        .map(|level| {
            resource_clause_interval_node(
                &node.space,
                level,
                resource_clause_interval_node_start(u64::from(node.start), level),
            )
        })
        .collect()
}

fn resource_clause_interval_node_bounds(node: &ResourceClauseIntervalNode) -> (u64, u64) {
    let start = u64::from(node.start);
    (start, start + (1u64 << node.level))
}

impl ResourceClauseIntervalIndex {
    fn insert(
        &mut self,
        waiter: ResourceClauseIntervalWaiter,
        space: &ResourceClauseIntervalSpace,
        start: i64,
        end: i64,
    ) {
        let Some(nodes) = resource_clause_interval_nodes(space, start, end) else {
            return;
        };
        for node in nodes {
            self.exact
                .entry(node.clone())
                .or_default()
                .insert(waiter.clone());
            for ancestor in resource_clause_interval_node_ancestors(&node) {
                self.subtree
                    .entry(ancestor)
                    .or_default()
                    .insert(waiter.clone());
            }
        }
    }

    fn remove(
        &mut self,
        waiter: &ResourceClauseIntervalWaiter,
        space: &ResourceClauseIntervalSpace,
        start: i64,
        end: i64,
    ) {
        let Some(nodes) = resource_clause_interval_nodes(space, start, end) else {
            return;
        };
        for node in nodes {
            let remove_exact = self.exact.get_mut(&node).is_some_and(|waiters| {
                waiters.remove(waiter);
                waiters.is_empty()
            });
            if remove_exact {
                self.exact.remove(&node);
            }
            for ancestor in resource_clause_interval_node_ancestors(&node) {
                let remove_subtree = self.subtree.get_mut(&ancestor).is_some_and(|waiters| {
                    waiters.remove(waiter);
                    waiters.is_empty()
                });
                if remove_subtree {
                    self.subtree.remove(&ancestor);
                }
            }
        }
    }

    fn add_candidates(
        waiters: &BTreeSet<ResourceClauseIntervalWaiter>,
        candidates: &mut BTreeSet<usize>,
    ) {
        candidates.extend(waiters.iter().map(|waiter| waiter.clause));
    }

    fn query_node(
        &self,
        node: &ResourceClauseIntervalNode,
        query_start: u64,
        query_end: u64,
        candidates: &mut BTreeSet<usize>,
    ) {
        let (node_start, node_end) = resource_clause_interval_node_bounds(node);
        if node_end <= query_start || query_end <= node_start {
            return;
        }
        if let Some(waiters) = self.exact.get(node) {
            Self::add_candidates(waiters, candidates);
        }
        if query_start <= node_start && node_end <= query_end {
            if let Some(waiters) = self.subtree.get(node) {
                Self::add_candidates(waiters, candidates);
            }
            return;
        }
        if node.level == 0 {
            return;
        }
        let child_level = node.level - 1;
        let left = resource_clause_interval_node(&node.space, child_level, node.start);
        let right_start = (u64::from(node.start) + (1u64 << child_level)) as u32;
        let right = resource_clause_interval_node(&node.space, child_level, right_start);
        self.query_node(&left, query_start, query_end, candidates);
        self.query_node(&right, query_start, query_end, candidates);
    }

    fn candidates_for_fact(&self, fact: &CResourceFact) -> BTreeSet<usize> {
        let mut candidates = BTreeSet::new();
        let Some(range) = fact.memory_range() else {
            return candidates;
        };
        let Some((space, start, end)) = resource_clause_concrete_memory_interval(range) else {
            return candidates;
        };
        let Some(query_start) = resource_clause_biased_coordinate(start) else {
            return candidates;
        };
        let Some(query_end) = resource_clause_biased_coordinate(end) else {
            return candidates;
        };
        let root = resource_clause_interval_node(&space, 32, 0);
        self.query_node(&root, query_start, query_end, &mut candidates);
        candidates
    }
}

fn resource_clause_coarse_keys(fact: &CResourceFact) -> Vec<ResourceClauseDependencyKey> {
    let mut keys = vec![ResourceClauseDependencyKey::Fact(fact.clone())];
    if let Some(range) = fact.memory_range() {
        keys.push(ResourceClauseDependencyKey::MemoryBase(
            range.base().clone(),
        ));
        keys.push(ResourceClauseDependencyKey::MemoryBlock(
            range.base().block.clone(),
        ));
    }
    keys
}

impl ResourceClauseWaiterIndex {
    fn register(&mut self, clause: usize, dependencies: &[CResourceFact]) {
        for (dependency_index, dependency) in dependencies.iter().enumerate() {
            if let Some((space, start, end)) = dependency
                .memory_range()
                .and_then(resource_clause_concrete_memory_interval)
            {
                let waiter = ResourceClauseIntervalWaiter {
                    clause,
                    dependency: dependency_index,
                };
                self.coarse
                    .entry(ResourceClauseDependencyKey::Fact(dependency.clone()))
                    .or_default()
                    .insert(clause);
                self.concrete_block_fallback
                    .entry(space.block.clone())
                    .or_default()
                    .insert(waiter.clone());
                self.intervals.insert(waiter, &space, start, end);
            } else {
                for key in resource_clause_coarse_keys(dependency) {
                    self.coarse.entry(key).or_default().insert(clause);
                }
            }
        }
    }

    fn unregister(&mut self, clause: usize, dependencies: &[CResourceFact]) {
        for (dependency_index, dependency) in dependencies.iter().enumerate() {
            if let Some((space, start, end)) = dependency
                .memory_range()
                .and_then(resource_clause_concrete_memory_interval)
            {
                let waiter = ResourceClauseIntervalWaiter {
                    clause,
                    dependency: dependency_index,
                };
                let key = ResourceClauseDependencyKey::Fact(dependency.clone());
                let remove_key = self.coarse.get_mut(&key).is_some_and(|clauses| {
                    clauses.remove(&clause);
                    clauses.is_empty()
                });
                if remove_key {
                    self.coarse.remove(&key);
                }
                let remove_block = self
                    .concrete_block_fallback
                    .get_mut(&space.block)
                    .is_some_and(|waiters| {
                        waiters.remove(&waiter);
                        waiters.is_empty()
                    });
                if remove_block {
                    self.concrete_block_fallback.remove(&space.block);
                }
                self.intervals.remove(&waiter, &space, start, end);
            } else {
                for key in resource_clause_coarse_keys(dependency) {
                    let remove_key = self.coarse.get_mut(&key).is_some_and(|clauses| {
                        clauses.remove(&clause);
                        clauses.is_empty()
                    });
                    if remove_key {
                        self.coarse.remove(&key);
                    }
                }
            }
        }
    }

    fn candidates_for_supplied(&self, supplied: &CResourceFact) -> BTreeSet<usize> {
        let mut candidates = self.intervals.candidates_for_fact(supplied);
        // Concrete supplied facts use only exact/interval events.  The
        // fallback below is deliberately reserved for symbolic or otherwise
        // un-normalizable supplied memory: scanning concrete waiters in one
        // explicit symbolic block event is conservative and bounded by that
        // event's block-local waiter set, while concrete same-block events
        // retain their interval-sensitive work curve.
        if supplied
            .memory_range()
            .and_then(resource_clause_concrete_memory_interval)
            .is_none()
            && let Some(range) = supplied.memory_range()
            && let Some(waiters) = self.concrete_block_fallback.get(&range.base().block)
        {
            ResourceClauseIntervalIndex::add_candidates(waiters, &mut candidates);
        }
        for key in resource_clause_coarse_keys(supplied) {
            if let Some(clauses) = self.coarse.get(&key) {
                candidates.extend(clauses.iter().copied());
            }
        }
        candidates
    }
}

fn resource_clause_register_waiters(
    index: usize,
    missing: Vec<CResourceFact>,
    dependencies: &mut [Vec<CResourceFact>],
    waiters: &mut ResourceClauseWaiterIndex,
) {
    let mut unique = Vec::new();
    for dependency in missing {
        if unique.contains(&dependency) {
            continue;
        }
        unique.push(dependency.clone());
    }
    waiters.register(index, &unique);
    dependencies[index] = unique;
}

fn resource_clause_unregister_waiters(
    index: usize,
    dependencies: &mut [Vec<CResourceFact>],
    waiters: &mut ResourceClauseWaiterIndex,
) {
    let previous = std::mem::take(&mut dependencies[index]);
    waiters.unregister(index, &previous);
}

fn resource_clause_enqueue_waiters(
    supplied: &CResourceFact,
    assumptions: &PureFactContext,
    section_supply: &ResourceContext,
    evaluated: &[Option<CResourceFact>],
    queued: &mut [bool],
    pending: &mut VecDeque<usize>,
    dependencies: &[Vec<CResourceFact>],
    waiters: &ResourceClauseWaiterIndex,
) {
    let candidates = waiters.candidates_for_supplied(supplied);
    for index in candidates {
        if evaluated[index].is_none()
            && !queued[index]
            && dependencies[index]
                .iter()
                .any(|dependency| section_supply.satisfies_fact(dependency, assumptions))
        {
            queued[index] = true;
            pending.push_back(index);
        }
    }
}

#[cfg(test)]
mod resource_clause_worklist_tests {
    use super::*;

    #[test]
    fn adjacent_supply_wakes_wide_memory_waiter() {
        let base = Pointer {
            block: PointerBlock::Concrete("resource-clause-adjacent".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let wide = CResourceFact::view_memory(CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(2),
        ));
        let left = CResourceFact::view_memory(CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ));
        let right = CResourceFact::view_memory(CMemoryRange::new(
            base,
            Bitvector32Term::Constant(1),
            Bitvector32Term::Constant(2),
        ));
        let assumptions = PureFactContext::new();
        let mut dependencies = vec![Vec::new()];
        let mut waiters = ResourceClauseWaiterIndex::default();
        resource_clause_register_waiters(0, vec![wide.clone()], &mut dependencies, &mut waiters);
        let evaluated = vec![None];
        let mut queued = vec![false];
        let mut pending = VecDeque::new();
        let section_supply = ResourceContext::new().unchecked_with_fact(left.clone());

        assert!(!section_supply.satisfies_fact(&wide, &assumptions));
        resource_clause_enqueue_waiters(
            &left,
            &assumptions,
            &section_supply,
            &evaluated,
            &mut queued,
            &mut pending,
            &dependencies,
            &waiters,
        );
        assert!(pending.is_empty());

        let section_supply = section_supply.unchecked_with_fact(right.clone());
        assert!(section_supply.satisfies_fact(&wide, &assumptions));
        resource_clause_enqueue_waiters(
            &right,
            &assumptions,
            &section_supply,
            &evaluated,
            &mut queued,
            &mut pending,
            &dependencies,
            &waiters,
        );
        assert_eq!(pending, VecDeque::from([0]));
    }

    /// Same-block disjoint ranges have one real dependency edge apiece.  The
    /// interval index must visit those edges, not every waiter sharing the
    /// block key.  The exact candidate count is the regression: the old
    /// `MemoryBlock` index would produce `size * size` visits here.
    #[test]
    fn same_block_disjoint_waiters_use_interval_candidates() {
        let base = Pointer {
            block: PointerBlock::Concrete("resource-clause-disjoint".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let samples = [4_usize, 8, 16, 32]
            .into_iter()
            .map(|size| {
                let mut dependencies = vec![Vec::new(); size];
                let mut waiters = ResourceClauseWaiterIndex::default();
                for index in 0..size {
                    let start = (index * 2) as u32;
                    let dependency = CResourceFact::view_memory(CMemoryRange::new(
                        base.clone(),
                        Bitvector32Term::Constant(start),
                        Bitvector32Term::Constant(start + 1),
                    ));
                    resource_clause_register_waiters(
                        index,
                        vec![dependency],
                        &mut dependencies,
                        &mut waiters,
                    );
                }
                let mut candidate_visits = 0;
                for index in 0..size {
                    let start = (index * 2) as u32;
                    let supplied = CResourceFact::view_memory(CMemoryRange::new(
                        base.clone(),
                        Bitvector32Term::Constant(start),
                        Bitvector32Term::Constant(start + 1),
                    ));
                    let candidates = waiters.candidates_for_supplied(&supplied);
                    candidate_visits += candidates.len();
                    assert_eq!(
                        candidates.into_iter().collect::<Vec<_>>(),
                        vec![index],
                        "a disjoint supplied range woke unrelated same-block waiters: size={size} index={index}"
                    );
                }
                (size, candidate_visits)
            })
            .collect::<Vec<_>>();
        assert_eq!(
            samples,
            vec![(4, 4), (8, 8), (16, 16), (32, 32)],
            "same-block interval candidate work should follow actual dependency edges"
        );
    }

    #[test]
    fn comparable_constant_bases_share_interval_space() {
        let block = PointerBlock::Concrete("resource-clause-base-aware".to_string());
        let dependency_base = Pointer {
            block: block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let supplied_base = Pointer {
            block,
            offset: PointerOffsetTerm::Constant(8),
        };
        let dependency = CResourceFact::view_memory(CMemoryRange::new(
            dependency_base,
            Bitvector32Term::Constant(2),
            Bitvector32Term::Constant(3),
        ));
        let supplied = CResourceFact::view_memory(CMemoryRange::new(
            supplied_base,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ));
        let mut dependencies = vec![Vec::new()];
        let mut waiters = ResourceClauseWaiterIndex::default();
        resource_clause_register_waiters(0, vec![dependency], &mut dependencies, &mut waiters);
        assert_eq!(
            waiters.candidates_for_supplied(&supplied),
            BTreeSet::from([0])
        );
    }

    #[test]
    fn concrete_memory_waiters_share_physical_byte_space_across_widths() {
        let base = Pointer {
            block: PointerBlock::Concrete("resource-clause-byte-space".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let dependency = CResourceFact::view_memory(CMemoryRange::new_with_element_width(
            base.clone(),
            Bitvector32Term::Constant(8),
            Bitvector32Term::Constant(12),
            1,
        ));
        let supplied = CResourceFact::view_memory(CMemoryRange::new_with_element_width(
            base,
            Bitvector32Term::Constant(2),
            Bitvector32Term::Constant(3),
            4,
        ));
        let mut dependencies = vec![Vec::new()];
        let mut waiters = ResourceClauseWaiterIndex::default();
        resource_clause_register_waiters(0, vec![dependency], &mut dependencies, &mut waiters);
        assert_eq!(
            waiters.candidates_for_supplied(&supplied),
            BTreeSet::from([0])
        );
    }

    #[test]
    fn symbolic_memory_waiters_keep_conservative_block_fallback() {
        let base = Pointer {
            block: PointerBlock::Concrete("resource-clause-symbolic".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let dependency = CResourceFact::view_memory(CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Variable(Variable(9_901)),
        ));
        let supplied = CResourceFact::view_memory(CMemoryRange::new(
            base,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ));
        let mut dependencies = vec![Vec::new()];
        let mut waiters = ResourceClauseWaiterIndex::default();
        resource_clause_register_waiters(0, vec![dependency], &mut dependencies, &mut waiters);
        assert_eq!(
            waiters.candidates_for_supplied(&supplied),
            BTreeSet::from([0])
        );
    }

    #[test]
    fn concrete_waiter_block_fallback_registers_and_unregisters_symmetrically() {
        let base = Pointer {
            block: PointerBlock::Concrete("resource-clause-fallback-lifetime".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let dependency = CResourceFact::view_memory(CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ));
        let symbolic_supplied = CResourceFact::view_memory(CMemoryRange::new(
            base,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Variable(Variable(9_902)),
        ));
        let mut dependencies = vec![Vec::new()];
        let mut waiters = ResourceClauseWaiterIndex::default();
        resource_clause_register_waiters(0, vec![dependency], &mut dependencies, &mut waiters);
        assert_eq!(
            waiters.candidates_for_supplied(&symbolic_supplied),
            BTreeSet::from([0])
        );
        resource_clause_unregister_waiters(0, &mut dependencies, &mut waiters);
        assert!(
            waiters
                .candidates_for_supplied(&symbolic_supplied)
                .is_empty()
        );
    }
}

fn evaluate_resource_clause_with_dependencies(
    state: &CState,
    resource: &CResourceSpec,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<(Result<CResourceFact, CRuntimeError>, Vec<CResourceFact>)> {
    #[cfg(test)]
    record_resource_clause_attempt();
    let (result, dependencies) = capture_resource_dependencies(|| {
        evaluate_function_resource_spec(state, resource, assumptions, budget)
    });
    result.map(|result| (result, dependencies))
}

/// The read authority a section's already-evaluated clauses supply to the
/// clauses that still need one.
///
/// Expansion adds views, never ownership: a folded composite's cells become
/// readable so a later clause's base load denotes, while every owned resource
/// stays exactly where the clause set put it. This state is a scratch
/// evaluation frame and is never the section's result.
fn resource_clause_section_supply(
    state: &CState,
    supplied: &[CResourceFact],
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> ResourceContext {
    let base = state
        .resources()
        .clone()
        .unchecked_with_facts(supplied.iter().cloned());
    if definitions.is_empty() {
        return base;
    }
    // A matched instance supplies the cells of the arm this section's
    // premises select, and nothing when they select none (D7). The arm stays
    // folded either way: only its read authority is published here.
    let mut views = selected_instance_arm_views(&base, definitions, state, assumptions);
    let Some(expanded) =
        expand_all_composite_resource_facts(&base, definitions, state.memory(), assumptions)
    else {
        return base.unchecked_with_facts(views);
    };
    views.extend(
        expanded
            .facts()
            .iter()
            .filter_map(|fact| match fact.resource() {
                CResource::Memory(range) => Some(CResourceFact::view_memory(range.clone())),
                _ => None,
            }),
    );
    base.unchecked_with_facts(views)
}

/// The read authority every folded matched instance of `context` publishes
/// for the arm this context's premises select.
pub(super) fn selected_instance_arm_views(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    state: &CState,
    assumptions: &PureFactContext,
) -> Vec<CResourceFact> {
    if definitions.is_empty() {
        return Vec::new();
    }
    context
        .facts()
        .iter()
        .filter_map(|fact| match fact.resource() {
            CResource::Instance(instance) => Some(instance),
            _ => None,
        })
        .flat_map(|instance| {
            selected_instance_arm_read_authority(instance, definitions, state, assumptions)
        })
        .collect()
}

/// The cells owned by the match arm this context's premises select for
/// `instance`, as views.
///
/// This is the kernel half of decision D7. The decision is
/// [`select_resource_model_arm`]; what it selects is published as read
/// authority only, so a contract clause or requirement may read a cell a
/// folded matched instance owns exactly as it may read one a folded
/// `if`-bodied composite owns. Ownership is untouched: only an explicit
/// `unfold` moves the arm's cells into the proof state.
///
/// Cost is the selected arm's own clauses. An instance whose arm is not
/// selected, or whose arm names a constructor binding in a memory clause,
/// publishes nothing.
fn selected_instance_arm_read_authority(
    instance: &ResourceInstance,
    definitions: &[CCompositeResourceDefinition],
    state: &CState,
    assumptions: &PureFactContext,
) -> Vec<CResourceFact> {
    let Some(definition) = definitions
        .iter()
        .find(|definition| definition.name() == instance.name())
    else {
        return Vec::new();
    };
    let Some(body) = definition.matched.as_ref() else {
        return Vec::new();
    };
    let Some(AlgebraicValue::Algebraic(model)) = instance.fields().get(body.field_index) else {
        return Vec::new();
    };
    let Some(selection) = select_resource_model_arm(model, assumptions) else {
        return Vec::new();
    };
    let Some(arm) = body
        .arms
        .iter()
        .find(|arm| arm.variant == selection.variant())
    else {
        return Vec::new();
    };
    let Ok(evaluation) = instance_body_evaluation(state, instance, definition) else {
        return Vec::new();
    };
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    let mut budget = ExecutionBudget::default();
    let Ok(Ok(body_resources)) = evaluate_function_resource_context_with_normalization(
        &evaluation,
        &arm.contains,
        &[],
        &evaluation_assumptions,
        &mut budget,
        false,
    ) else {
        return Vec::new();
    };
    body_resources
        .0
        .facts()
        .iter()
        .filter_map(|fact| match fact.resource() {
            CResource::Memory(range) => Some(CResourceFact::view_memory(range.clone())),
            _ => None,
        })
        .collect()
}

/// Incrementally exposes the memory cells beneath one newly evaluated
/// composite clause.  The outer section supply already expanded all facts
/// from the previous pass; walking only this fact and its nested children
/// keeps a dependency chain proportional to its own nodes and edges instead
/// of rescanning the complete section after every successful retry.
fn resource_clause_supply_with_fact(
    mut supply: ResourceContext,
    fact: CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> (ResourceContext, Vec<CResourceFact>) {
    let mut added = Vec::new();
    if !supply.facts().contains(&fact) {
        supply = supply.unchecked_with_fact(fact.clone());
        added.push(fact.clone());
    }
    if definitions.is_empty() || !matches!(fact.resource(), CResource::Composite { .. }) {
        return (supply, added);
    }
    let mut pending = VecDeque::from([fact]);
    let mut seen = BTreeSet::new();
    while let Some(composite) = pending.pop_front() {
        if !seen.insert(composite.clone()) {
            continue;
        }
        let expansion_context = supply.clone().unchecked_with_fact(composite.clone());
        let Some((_, children, _)) = expand_composite_resource_fact_with_children(
            &expansion_context,
            &composite,
            definitions,
            memory,
            assumptions,
        ) else {
            continue;
        };
        for child in children {
            match child.resource() {
                CResource::Memory(range) => {
                    let view = CResourceFact::view_memory(range.clone());
                    if !supply.facts().contains(&view) {
                        supply = supply.unchecked_with_fact(view.clone());
                        added.push(view);
                    }
                }
                CResource::Composite { .. } => pending.push_back(child),
                CResource::Token { .. } | CResource::Instance(_) => {}
            }
        }
    }
    (supply, added)
}

/// Names which resource clause of a contract section could not be addressed.
///
/// Two checks reach this conclusion about the same contract: the surface
/// refuses a clause whose segment base reads a cell the contract holds no
/// authority over, and this evaluator refuses a clause whose base it cannot
/// read at all. They are one defect, so they identify the clause with one
/// wording, formatted here and in [`resource_clause_stall_note`].
pub(crate) fn resource_clause_position_note(index: usize, total: usize) -> String {
    format!("resource clause {} of {total}", index + 1)
}

/// Names two clauses that no order addresses. Clause order does not decide a
/// section, so reporting only the first position would send the user to a
/// clause that is fine on its own.
pub(crate) fn resource_clause_stall_note(index: usize, other: usize) -> String {
    format!(
        "resource clauses {} and {} cannot be evaluated in any order: each needs a cell no \
         clause evaluated before it supplies",
        index + 1,
        other + 1
    )
}

/// Names which resource clause of a contract section failed to evaluate. The
/// evaluator walks the declared clauses in order, so the position is the only
/// identification available here, and it is enough for a user to find the
/// clause. Structured errors already print the offending resource and are
/// passed through unchanged.
fn resource_clause_position(resources: &[CResourceSpec], index: usize) -> (usize, usize) {
    resources
        .get(index)
        .and_then(CResourceSpec::clause_position)
        .unwrap_or((index, resources.len()))
}

fn resource_clause_runtime_error(
    error: CRuntimeError,
    index: usize,
    resources: &[CResourceSpec],
) -> CRuntimeError {
    let CRuntimeError::FunctionContract(message) = error else {
        return error;
    };
    let (index, total) = resource_clause_position(resources, index);
    CRuntimeError::FunctionContract(format!(
        "{message} ({})",
        resource_clause_position_note(index, total)
    ))
}

/// Whether a clause failed for want of a value it had to read, which is the
/// only failure another clause's authority can repair. The evaluator reports
/// a section that stalls on these as a pair; anything else is one clause's own
/// problem.
fn resource_clause_failure_awaits_supply(error: &CRuntimeError) -> bool {
    let CRuntimeError::FunctionContract(message) = error else {
        return false;
    };
    message.starts_with("could not evaluate an owned memory resource segment")
        || message.starts_with("could not evaluate a viewed memory resource segment")
        || message.starts_with("could not evaluate resource `")
}

fn resource_clause_cycle_runtime_error(
    error: CRuntimeError,
    index: usize,
    other: usize,
    resources: &[CResourceSpec],
) -> CRuntimeError {
    let CRuntimeError::FunctionContract(message) = error else {
        return error;
    };
    let (index, _) = resource_clause_position(resources, index);
    let (other, _) = resource_clause_position(resources, other);
    CRuntimeError::FunctionContract(format!(
        "{message} ({})",
        resource_clause_stall_note(index, other)
    ))
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
    match resource.term() {
        CResourceTerm::Instance {
            identity,
            schema,
            resource: inner_term,
            ..
        } => {
            let inner = match CResourceSpec::new(
                (**inner_term).clone(),
                CResourceAccessMode::Own,
                CResourceQuantity::One,
                resource.role(),
                resource.snapshot(),
            ) {
                Ok(inner) => inner,
                Err(error) => {
                    return Ok(Err(CRuntimeError::FunctionContract(format!(
                        "invalid named resource body: {error}"
                    ))));
                }
            };
            let required =
                match evaluate_function_resource_spec(state, &inner, assumptions, budget)? {
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
        CResourceTerm::Memory(segment) => {
            let element_width = segment.element_width();
            let segment = match evaluate_loop_effect_segment(state, segment, assumptions, budget)? {
                Ok(segment) => segment,
                Err(_) => {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        if resource.is_view() {
                            "could not evaluate a viewed memory resource segment".to_string()
                        } else {
                            "could not evaluate an owned memory resource segment".to_string()
                        },
                    )));
                }
            };
            let range = CMemoryRange::new_with_element_width(
                segment.base,
                segment.start,
                segment.end,
                element_width,
            );
            Ok(Ok(if resource.is_view() {
                CResourceFact::view_memory(range)
            } else {
                CResourceFact::own_memory(range)
            }))
        }
        CResourceTerm::Composite {
            name,
            arguments,
            parameter_types,
        }
        | CResourceTerm::Token {
            name,
            arguments,
            parameter_types,
        } => {
            let family = resource.family();
            let mut fact = match evaluate_function_declared_resource_spec(
                state,
                resource.access(),
                family,
                name,
                arguments,
                parameter_types,
                assumptions,
                budget,
            )? {
                Ok(fact) => fact,
                Err(error) => return Ok(Err(error)),
            };
            if let CResourceQuantity::Count(quantity) = resource.quantity() {
                if resource.access() != CResourceAccessMode::Own
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
                if !quantity_condition_holds(
                    assumptions,
                    ConditionTerm::Bitvector32SignedGreaterEqual(
                        Box::new(quantity.clone()),
                        Box::new(Bitvector32Term::Constant(0)),
                    ),
                ) {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "declared resource quantity is not known nonnegative; state that the \
                         quantity expression is at least 0 as a requirement, an invariant, or a \
                         fact proved in scope"
                            .to_string(),
                    )));
                }
                let CResourceFact::Own(inner, _) = fact else {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "declared resource quantity did not lower to owned authority".to_string(),
                    )));
                };
                fact = CResourceFact::own_quantity(inner, quantity);
            }
            Ok(Ok(fact))
        }
    }
}

/// Lowers the nonnegativity conditions implicit in quantified resource
/// requirements. A function may assume these at its own entry just as it may
/// assume its ordinary `requires`; call sites still use
/// `evaluate_function_resource_spec` and must prove every condition.
pub(crate) fn quantified_resource_requirement_assumptions(
    state: &CState,
    resources: &[CResourceSpec],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<Vec<Proposition>, CRuntimeError>> {
    let mut propositions = Vec::new();
    for resource in resources {
        let CResourceQuantity::Count(quantity) = resource.quantity() else {
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
                    resource.family() == ResourceFamily::Token
                        && resource.declared_name() == Some(CResourceFact::ALLOCATION_RESOURCE_NAME)
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
        function.composite_resource_definitions(),
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
    let entry_resource_state =
        with_contract_argument_views(caller_state, function, argument_values);
    let return_resources = match crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "return resource evaluation",
        || {
            evaluate_function_return_resources(
                &caller_resources_after_requirements,
                &entry_resource_state,
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
    return_state.next_local_lifetime = state.next_local_lifetime;
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
            if function.has_inline_body() {
                // Inline bodies execute with a parameter-only local
                // environment, so pointer stores into caller locals cannot
                // synchronize their named bindings during body execution.
                // Reconcile those bindings from the shared caller memory
                // before the caller resumes evaluating its next statement.
                let memory = caller_state.memory.clone();
                caller_state.sync_scalar_locals_from_memory(&memory);
            }
            if return_resources.is_none() {
                caller_state.instance_field_scope = state.instance_field_scope;
            }
            caller_state.resources = return_resources.cloned().unwrap_or(state.resources);
            caller_state.counted_populations = state.counted_populations;
            caller_state.next_local_frame = state.next_local_frame;
            caller_state.next_local_lifetime = state.next_local_lifetime;
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

#[cfg(test)]
mod verified_call_initialization_tests {
    use super::*;

    fn local_pointer() -> Pointer {
        Pointer {
            block: PointerBlock::Concrete("local:caller:x".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    fn owned_cell_spec() -> CResourceSpec {
        CResourceSpec::owned_memory(CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(1),
        ))
    }

    fn caller_state(pointer: &Pointer) -> CState {
        let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own(
            CResource::Memory(CMemoryRange::new(
                pointer.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )),
        ));
        CState::new()
            .with_memory(CMemory::new().with_block(pointer.block.clone(), 4))
            .with_resource_context(resources)
    }

    fn apply(function: CFunction, state: &CState, pointer: &Pointer) -> Vec<CFunctionPath> {
        let environment =
            CExecutionEnvironment::new().with_verified_function_rule(CVerifiedFunctionRule {
                function: function.clone(),
            });
        execute_c_function_call_paths(
            state,
            &function,
            &[c_pointer_value(pointer.clone())],
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .expect("verified call should execute")
    }

    #[test]
    fn owned_read_does_not_treat_ownership_as_initialization() {
        let pointer = local_pointer();
        let function = c_function(
            CType::Int32,
            "read_owned",
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_index(c_variable("p"), c_int32_literal(0))),
        )
        .with_resource_summary(vec![owned_cell_spec()], Vec::new());
        let paths = apply(function, &caller_state(&pointer), &pointer);
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead),
                ..
            }]
        ));
    }

    #[test]
    fn owned_write_keeps_an_uninitialized_output_writable() {
        let pointer = local_pointer();
        let function = c_function(
            CType::Void,
            "write_owned",
            vec![c_parameter("p", CType::Int32Pointer)],
            c_store(
                c_index(c_variable("p"), c_int32_literal(0)),
                c_int32_literal(7),
            ),
        )
        .with_resource_summary(vec![owned_cell_spec()], Vec::new())
        .with_contract(
            Vec::new(),
            Vec::new(),
            vec![CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(1),
            )],
            Vec::new(),
            true,
        );
        let paths = apply(function, &caller_state(&pointer), &pointer);
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::Return { .. },
                ..
            }]
        ));
    }
}

#[cfg(test)]
mod integer_parameter_read_tests {
    use super::*;

    #[test]
    fn nested_integer_conversions_keep_current_parameter_reads_visible() {
        let value = SpecIntegerExpression::Negate(Box::new(SpecIntegerExpression::FromMachine(
            Box::new(SpecExpression::CExpression(c_variable("parameter"))),
        )));
        let conversion = SpecExpression::IntegerToMachine {
            value: Box::new(value.clone()),
            destination: MachineIntegerType::Int32,
        };
        assert!(spec_expression_reads_current_parameter(
            &conversion,
            "parameter"
        ));
        assert!(!spec_expression_reads_current_parameter(
            &conversion,
            "other"
        ));
        let comparison = SpecProposition::IntegerComparison {
            left: SpecIntegerExpression::Term(IntegerTerm::constant_i64(0)),
            operator: IntegerComparisonOperator::Equal,
            right: value,
        };
        assert!(spec_proposition_reads_current_parameter(
            &comparison,
            "parameter"
        ));
        assert!(!spec_proposition_reads_current_parameter(
            &comparison,
            "other"
        ));
    }
}
