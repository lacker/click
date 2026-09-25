use super::loans::{
    CheckedLoanCallEvidenceSequence, concat_checked_loan_evidence,
    empty_checked_loan_evidence_sequence,
};
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
            arguments: vec![Term::CState(Box::new(CState::new())), Term::CValue(value)],
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
    if environment
        .modeled_pthread_binding
        .as_ref()
        .is_some_and(|binding| function_name == binding.create_name)
    {
        return execute_modeled_pthread_create_paths(
            state,
            Some(target),
            arguments,
            assumptions,
            environment,
            budget,
        );
    }
    if environment
        .modeled_pthread_binding
        .as_ref()
        .is_some_and(|binding| function_name == binding.join_name)
    {
        return execute_modeled_pthread_join_paths(
            state,
            Some(target),
            arguments,
            assumptions,
            environment,
            budget,
        );
    }
    if let Some(binding) = environment.modeled_pthread_binding.as_ref()
        && [
            binding.mutex_init_name,
            binding.mutex_lock_name,
            binding.mutex_unlock_name,
            binding.mutex_destroy_name,
        ]
        .contains(&function_name)
    {
        return execute_modeled_pthread_mutex_paths(
            state,
            Some(target),
            function_name,
            arguments,
            assumptions,
            environment,
            budget,
        );
    }
    if let Some(path) = unbound_modeled_pthread_call(function_name, environment) {
        return Ok(vec![path]);
    }
    if function_name == "realloc" {
        if environment.selected_call_contract.is_some() {
            return Ok(vec![CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(
                    "step(Contract) requires a function-pointer call".to_string(),
                )),
                facts: Vec::new(),
                obligations: Vec::new(),

                loan_evidence: empty_checked_loan_evidence_sequence(),
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
            loop_invariant_correspondence: Default::default(),
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::UnknownFunction(
                function_name.to_string(),
            )),
            facts: Vec::new(),
            obligations: Vec::new(),

            loan_evidence: empty_checked_loan_evidence_sequence(),
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
                        loop_invariant_correspondence: Default::default(),
                        outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: path.facts,
                        obligations: path.obligations,

                        loan_evidence: path.loan_evidence.clone(),
                    };
                }
                if let Some(layout) = function.return_aggregate_layout() {
                    if matches!(
                        state.locals.binding(target),
                        Some(CLocalBinding::AggregateObject { constant: true, .. })
                    ) {
                        return CStatementExecutionPath {
                            loop_invariant_correspondence: Default::default(),
                            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            facts: path.facts,
                            obligations: path.obligations,

                            loan_evidence: path.loan_evidence.clone(),
                        };
                    }
                    let Some(target_layout) = state.locals.aggregate_layout(target) else {
                        return CStatementExecutionPath {
                            loop_invariant_correspondence: Default::default(),
                            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            facts: path.facts,
                            obligations: path.obligations,

                            loan_evidence: path.loan_evidence.clone(),
                        };
                    };
                    if target_layout != layout {
                        return CStatementExecutionPath {
                            loop_invariant_correspondence: Default::default(),
                            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            facts: path.facts,
                            obligations: path.obligations,

                            loan_evidence: path.loan_evidence.clone(),
                        };
                    }
                    let CValue::Pointer(pointer) = &value else {
                        return CStatementExecutionPath {
                            loop_invariant_correspondence: Default::default(),
                            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            facts: path.facts,
                            obligations: path.obligations,

                            loan_evidence: path.loan_evidence.clone(),
                        };
                    };
                    if pointer.is_null() {
                        return CStatementExecutionPath {
                            loop_invariant_correspondence: Default::default(),
                            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            facts: path.facts,
                            obligations: path.obligations,

                            loan_evidence: path.loan_evidence.clone(),
                        };
                    }
                    let Some(slot) = state.locals.slot(target).cloned() else {
                        return CStatementExecutionPath {
                            loop_invariant_correspondence: Default::default(),
                            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            facts: path.facts,
                            obligations: path.obligations,

                            loan_evidence: path.loan_evidence.clone(),
                        };
                    };
                    if let Some(outcome) = crate::kernel::eval::stable_loan_memory_write_outcome(
                        &state,
                        &slot,
                        layout.size_bytes(),
                        &crate::kernel::reasoning::path_facts::assumptions_with_path_context(
                            assumptions,
                            &path.facts,
                            &path.obligations,
                        ),
                    ) {
                        return CStatementExecutionPath {
                            loop_invariant_correspondence: Default::default(),
                            outcome,
                            facts: path.facts,
                            obligations: path.obligations,

                            loan_evidence: path.loan_evidence.clone(),
                        };
                    }
                    let next_memory = match copy_aggregate_fields_checked(
                        state.memory.clone(),
                        pointer.pointer(),
                        &slot,
                        layout,
                    ) {
                        Ok(memory) => memory,
                        Err(undefined_behavior) => {
                            return CStatementExecutionPath {
                                loop_invariant_correspondence: Default::default(),
                                outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                                facts: path.facts,
                                obligations: path.obligations,

                                loan_evidence: path.loan_evidence.clone(),
                            };
                        }
                    };
                    state.set_memory(next_memory);
                    return CStatementExecutionPath {
                        loop_invariant_correspondence: Default::default(),
                        outcome: CStatementOutcome::Normal(state),
                        facts: path.facts,
                        obligations: path.obligations,

                        loan_evidence: path.loan_evidence.clone(),
                    };
                }
                if state.locals.is_array_object(target) {
                    return CStatementExecutionPath {
                        loop_invariant_correspondence: Default::default(),
                        outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: path.facts,
                        obligations: path.obligations,

                        loan_evidence: path.loan_evidence.clone(),
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
            CFunctionOutcome::Throw { value, state } => CStatementOutcome::Throw { value, state },
            CFunctionOutcome::VerificationDiverges => CStatementOutcome::VerificationDiverges,
            CFunctionOutcome::UndefinedBehavior(undefined_behavior) => {
                CStatementOutcome::UndefinedBehavior(undefined_behavior)
            }
            CFunctionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
        };

        CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome,
            facts: path.facts,
            obligations: path.obligations,

            loan_evidence: path.loan_evidence.clone(),
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
    if environment
        .modeled_pthread_binding
        .as_ref()
        .is_some_and(|binding| function_name == binding.create_name)
    {
        return execute_modeled_pthread_create_paths(
            state,
            None,
            arguments,
            assumptions,
            environment,
            budget,
        );
    }
    if environment
        .modeled_pthread_binding
        .as_ref()
        .is_some_and(|binding| function_name == binding.join_name)
    {
        return execute_modeled_pthread_join_paths(
            state,
            None,
            arguments,
            assumptions,
            environment,
            budget,
        );
    }
    if let Some(binding) = environment.modeled_pthread_binding.as_ref()
        && [
            binding.mutex_init_name,
            binding.mutex_lock_name,
            binding.mutex_unlock_name,
            binding.mutex_destroy_name,
        ]
        .contains(&function_name)
    {
        return execute_modeled_pthread_mutex_paths(
            state,
            None,
            function_name,
            arguments,
            assumptions,
            environment,
            budget,
        );
    }
    if let Some(path) = unbound_modeled_pthread_call(function_name, environment) {
        return Ok(vec![path]);
    }
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
            loop_invariant_correspondence: Default::default(),
            outcome: match path.outcome {
                CFunctionOutcome::Return { state, .. } => CStatementOutcome::Normal(state),
                CFunctionOutcome::Throw { value, state } => {
                    CStatementOutcome::Throw { value, state }
                }
                CFunctionOutcome::VerificationDiverges => CStatementOutcome::VerificationDiverges,
                CFunctionOutcome::UndefinedBehavior(error) => {
                    CStatementOutcome::UndefinedBehavior(error)
                }
                CFunctionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
            },
            facts: path.facts,
            obligations: path.obligations,
            loan_evidence: path.loan_evidence,
        })
        .collect::<Vec<_>>();
        budget.check_path_width(paths.len())?;
        return Ok(paths);
    }

    let Some(function) = environment.get_function(function_name) else {
        return Ok(vec![CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::UnknownFunction(
                function_name.to_string(),
            )),
            facts: Vec::new(),
            obligations: Vec::new(),

            loan_evidence: empty_checked_loan_evidence_sequence(),
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
        loop_invariant_correspondence: Default::default(),
        outcome: match path.outcome {
            CFunctionOutcome::Return { state, .. } => CStatementOutcome::Normal(state),
            CFunctionOutcome::Throw { value, state } => CStatementOutcome::Throw { value, state },
            CFunctionOutcome::VerificationDiverges => CStatementOutcome::VerificationDiverges,
            CFunctionOutcome::UndefinedBehavior(undefined_behavior) => {
                CStatementOutcome::UndefinedBehavior(undefined_behavior)
            }
            CFunctionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
        },
        facts: path.facts,
        obligations: path.obligations,
        loan_evidence: path.loan_evidence,
    })
    .collect::<Vec<_>>();
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn unbound_modeled_pthread_call(
    function_name: &str,
    environment: &CExecutionEnvironment,
) -> Option<CStatementExecutionPath> {
    let binding = environment.modeled_pthread_binding.as_ref()?;
    if ![
        binding.create_name,
        binding.join_name,
        binding.mutex_init_name,
        binding.mutex_lock_name,
        binding.mutex_unlock_name,
        binding.mutex_destroy_name,
    ]
    .contains(&function_name)
    {
        return None;
    }
    Some(CStatementExecutionPath {
        loop_invariant_correspondence: Default::default(),
        outcome: CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
            "modeled-pthread `{function_name}` has no checked C transition yet"
        ))),
        facts: Vec::new(),
        obligations: Vec::new(),
        loan_evidence: empty_checked_loan_evidence_sequence(),
    })
}

fn execute_modeled_pthread_mutex_paths(
    state: &CState,
    target: Option<&str>,
    function_name: &str,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let binding = environment
        .modeled_pthread_binding
        .as_ref()
        .expect("selected runtime");
    let initializing = function_name == binding.mutex_init_name;
    let expected_arity = if initializing { 2 } else { 1 };
    let refusal = |message: &str| {
        CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(message.to_string()))
    };
    if state.pending_thread_create.is_some()
        || environment.selected_call_contract.is_some()
        || arguments.len() != expected_arity
        || (!initializing && environment.selected_call_binders.is_some())
    {
        return Ok(vec![CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome: refusal(
                "modeled-pthread mutex call has unsupported arguments or pending thread authority",
            ),
            facts: Vec::new(),
            obligations: Vec::new(),
            loan_evidence: empty_checked_loan_evidence_sequence(),
        }]);
    }
    let mut paths = Vec::new();
    for mut path in super::functions::evaluate_c_arguments_paths(
        state,
        arguments,
        assumptions,
        budget,
        Some(environment),
    )? {
        let outcome = if let Some(outcome) = path.outcome {
            match outcome {
                CFunctionOutcome::UndefinedBehavior(error) => {
                    CStatementOutcome::UndefinedBehavior(error)
                }
                CFunctionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
                _ => refusal("modeled-pthread mutex argument did not evaluate"),
            }
        } else if !matches!(&path.values[0], CValue::Pointer(pointer) if !pointer.is_null()) {
            refusal("modeled-pthread mutex requires a nonnull mutex pointer")
        } else if initializing
            && !matches!(&path.values[1],
                CValue::Pointer(pointer) if pointer.is_null())
            && !matches!(&path.values[1], CValue::Int32(Bitvector32Term::Constant(0)))
        {
            refusal("modeled-pthread mutex init requires null attributes")
        } else {
            let CValue::Pointer(mutex) = &path.values[0] else {
                unreachable!()
            };
            let current = super::reasoning::path_facts::assumptions_with_path_context(
                assumptions,
                &path.facts,
                &path.obligations,
            );
            let transition = if initializing {
                let selected = environment.selected_call_binders.as_ref();
                let identity = selected
                    .filter(|transport| {
                        transport.function.as_ref() == function_name
                            && transport.arity == expected_arity
                            && transport.bindings.len() == 1
                    })
                    .and_then(|transport| transport.bindings.get(&Variable(u64::MAX - 1)));
                identity
                    .ok_or("mutex init requires `step(pthread_mutex_init(...), { invariant: instance })`")
                    .and_then(|identity| state.resources.owned_instance(*identity)
                        .ok_or("selected mutex invariant is not held folded"))
                    .and_then(|instance| {
                        let guard = environment.modeled_mutex_guards.get(instance.name())
                            .ok_or("selected resource has no `guarded_by` mutex field")?;
                        let Some(AlgebraicValue::C(CValue::Pointer(base))) =
                            instance.arguments().get(guard.parameter_index) else {
                            return Err("guarded resource parameter is not a pointer");
                        };
                        let expected = base.pointer().offset_by_bytes(guard.field_offset_bytes);
                        if !super::reasoning::pointers_proven_equal_for_memory_resolution(
                            &expected, mutex.pointer(), &current,
                        ) {
                            return Err("selected resource is guarded by a different mutex");
                        }
                        let fact = CResourceFact::own(CResource::Instance(instance.clone()));
                        super::mutexes::MutexContext::new(state.clone())
                            .publish(expected, fact, &current)
                            .map(|context| context.into_state())
                    })
            } else {
                let context = super::mutexes::MutexContext::new(state.clone());
                let result = if function_name == binding.mutex_lock_name {
                    context.acquire_current(mutex.pointer(), &current)
                } else if function_name == binding.mutex_unlock_name {
                    context.release_current(mutex.pointer(), &current)
                } else {
                    context.destroy(mutex.pointer(), &current)
                };
                result.map(|context| context.into_state())
            };
            match transition {
                Ok(mut next) => {
                    if target.is_some_and(|target| {
                        assign_call_result(
                            &mut next,
                            target,
                            CValue::Int32(Bitvector32Term::Constant(0)),
                            &mut path.obligations,
                            &current,
                        )
                        .is_none()
                    }) {
                        refusal("modeled-pthread mutex status target is not writable")
                    } else {
                        CStatementOutcome::Normal(next)
                    }
                }
                Err(message) => refusal(message),
            }
        };
        paths.push(CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome,
            facts: path.facts,
            obligations: path.obligations,
            loan_evidence: empty_checked_loan_evidence_sequence(),
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn modeled_pthread_handle_store(
    state: &CState,
    slot: &CValue,
    value: CValue,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<(CState, Vec<ProofObligation>)>> {
    let statement = CStatement::TypedStore {
        pointer: CExpression::Value(slot.clone()),
        value: CExpression::Value(value),
        value_type: CType::UInt64,
        volatile: false,
        pointee_constant: false,
    };
    let paths = super::eval::execute_c_statement_paths(
        state,
        &statement,
        assumptions,
        environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        budget,
    )?;
    let [path] = paths.as_slice() else {
        return Ok(None);
    };
    match &path.outcome {
        CStatementOutcome::Normal(next) => Ok(Some((next.clone(), path.obligations.clone()))),
        _ => Ok(None),
    }
}

fn modeled_pthread_indeterminate_handle(
    mut state: CState,
    slot: &Pointer,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<CState> {
    let range = CMemoryRange::new_with_element_width(
        slot.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
        8,
    );
    let marker = budget.allocate_kernel_variable()?;
    state.set_memory(
        state
            .memory
            .clone()
            .with_call_memory_havoc(marker, &[range], assumptions),
    );
    if let Some(name) = state.locals.slots.get(slot).cloned() {
        let binding = state.locals.binding(&name).cloned();
        if let Some(
            CLocalBinding::Object {
                c_type,
                slot,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
                ..
            }
            | CLocalBinding::UninitializedObject {
                c_type,
                slot,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
            },
        ) = binding
        {
            state.locals.set_uninitialized_with_all_qualifiers(
                name,
                c_type,
                slot,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
            );
        }
    }
    Ok(state)
}

fn execute_modeled_pthread_create_paths(
    state: &CState,
    target: Option<&str>,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let refusal = |message: &str| {
        CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(message.to_string()))
    };
    if state.pending_thread_create.is_some()
        || environment.selected_call_contract.is_some()
        || arguments.len() != 4
        || target.is_none()
    {
        return Ok(vec![CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome: refusal(
                "modeled-pthread create requires a direct, assigned four-argument call with no unresolved earlier create",
            ),
            facts: Vec::new(),
            obligations: Vec::new(),
            loan_evidence: empty_checked_loan_evidence_sequence(),
        }]);
    }
    let mut paths = Vec::new();
    for mut path in super::functions::evaluate_c_arguments_paths(
        state,
        arguments,
        assumptions,
        budget,
        Some(environment),
    )? {
        let outcome = if let Some(outcome) = path.outcome {
            match outcome {
                CFunctionOutcome::UndefinedBehavior(error) => {
                    CStatementOutcome::UndefinedBehavior(error)
                }
                CFunctionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
                _ => refusal("modeled-pthread create argument did not evaluate"),
            }
        } else if !matches!(&path.values[0], CValue::Pointer(slot) if slot.c_type() == CType::UInt64Pointer)
            || !matches!(&path.values[1], CValue::Pointer(attr) if attr.is_null())
            || !matches!(&path.values[3], CValue::Pointer(_))
        {
            refusal(
                "modeled-pthread create requires a writable pthread_t slot, null attributes, and a pointer argument",
            )
        } else if let CValue::Pointer(callback) = &path.values[2] {
            if let PointerBlock::Function(worker_name) = &callback.block {
                let Some(worker) = environment.get_verified_function_rule(worker_name) else {
                    paths.push(CStatementExecutionPath {
                        loop_invariant_correspondence: Default::default(),
                        outcome: refusal(
                            "modeled-pthread create requires the direct worker's verified contract",
                        ),
                        facts: path.facts,
                        obligations: path.obligations,
                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    });
                    continue;
                };
                let callback_type =
                    CType::FunctionPointer(CType::qualified_function_pointer_signature(
                        CType::VoidPointer,
                        false,
                        &[(CType::VoidPointer, false)],
                    ));
                if callback.c_type() != callback_type
                    || worker.function.function_pointer_type() != callback_type
                {
                    paths.push(CStatementExecutionPath {
                        loop_invariant_correspondence: Default::default(),
                        outcome: refusal(
                            "modeled-pthread create requires a void *(*)(void *) worker",
                        ),
                        facts: path.facts,
                        obligations: path.obligations,
                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    });
                    continue;
                }
                let termination = environment.get_verified_function_termination_rule(worker_name);
                let current = super::reasoning::path_facts::assumptions_with_path_context(
                    assumptions,
                    &path.facts,
                    &path.obligations,
                );
                match super::threads::ThreadContext::new(state.clone()) {
                    Ok(context) => match context.prepare_create(
                        worker,
                        termination,
                        path.values[3].clone(),
                        &current,
                        environment,
                        budget,
                    )? {
                        Ok(prepared) => {
                            let failure = prepared.failure();
                            let (success, handle, _) = prepared.success();
                            let checked_failure_value =
                                CValue::UInt64(Bitvector32Term::Constant(0));
                            let slot = &path.values[0];
                            let checked_success = modeled_pthread_handle_store(
                                success.parent(),
                                slot,
                                handle.c_value(),
                                &current,
                                environment,
                                budget,
                            )?;
                            let checked_failure = modeled_pthread_handle_store(
                                failure.parent(),
                                slot,
                                checked_failure_value,
                                &current,
                                environment,
                                budget,
                            )?;
                            if let (
                                Some((mut success, success_obligations)),
                                Some((_, failure_obligations)),
                            ) = (checked_success, checked_failure)
                            {
                                path.obligations.extend(success_obligations);
                                path.obligations.extend(failure_obligations);
                                let CValue::Pointer(slot_pointer) = slot else {
                                    unreachable!()
                                };
                                let output_slot = slot_pointer.pointer();
                                let mut failure = modeled_pthread_indeterminate_handle(
                                    failure.parent().clone(),
                                    output_slot,
                                    &current,
                                    budget,
                                )?;
                                let status =
                                    Bitvector32Term::Variable(budget.allocate_kernel_variable()?);
                                let result = CValue::Int32(status.clone());
                                let target = target.expect("checked assigned call");
                                if assign_call_result(
                                    &mut success,
                                    target,
                                    result.clone(),
                                    &mut path.obligations,
                                    &current,
                                )
                                .is_none()
                                    || assign_call_result(
                                        &mut failure,
                                        target,
                                        result,
                                        &mut path.obligations,
                                        &current,
                                    )
                                    .is_none()
                                {
                                    refusal("modeled-pthread create status target is not writable")
                                } else {
                                    let mut neutral = failure.clone();
                                    neutral.resources = success.resources.clone();
                                    neutral.loan_ledger = success.loan_ledger.clone();
                                    neutral.loan_view_bindings = success.loan_view_bindings.clone();
                                    neutral.mutex_ledger = success.mutex_ledger.clone();
                                    neutral = modeled_pthread_indeterminate_handle(
                                        neutral,
                                        output_slot,
                                        &current,
                                        budget,
                                    )?;
                                    neutral.pending_thread_create =
                                        Some(super::threads::PendingThreadCreate::new(
                                            status,
                                            output_slot.clone(),
                                            handle.c_value(),
                                            &success,
                                            &failure,
                                        ));
                                    CStatementOutcome::Normal(neutral)
                                }
                            } else {
                                refusal(
                                    "modeled-pthread handle output is not writable or overlaps the worker task",
                                )
                            }
                        }
                        Err(message) => refusal(&message),
                    },
                    Err(message) => refusal(message),
                }
            } else {
                refusal("modeled-pthread create requires a direct worker address")
            }
        } else {
            refusal("modeled-pthread create requires a direct worker address")
        };
        paths.push(CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome,
            facts: path.facts,
            obligations: path.obligations,
            loan_evidence: empty_checked_loan_evidence_sequence(),
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn execute_modeled_pthread_join_paths(
    state: &CState,
    target: Option<&str>,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let refusal = |message: &str| {
        CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(message.to_string()))
    };
    if environment.selected_call_contract.is_some() || arguments.len() != 2 {
        return Ok(vec![CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome: refusal("modeled-pthread join requires its direct two-argument C call"),
            facts: Vec::new(),
            obligations: Vec::new(),
            loan_evidence: empty_checked_loan_evidence_sequence(),
        }]);
    }
    let mut paths = Vec::new();
    for mut path in super::functions::evaluate_c_arguments_paths(
        state,
        arguments,
        assumptions,
        budget,
        Some(environment),
    )? {
        let outcome = if let Some(outcome) = path.outcome {
            match outcome {
                CFunctionOutcome::UndefinedBehavior(error) => {
                    CStatementOutcome::UndefinedBehavior(error)
                }
                CFunctionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
                _ => refusal("modeled-pthread join argument did not evaluate"),
            }
        } else if !matches!(&path.values[1], CValue::Pointer(pointer) if pointer.is_null()) {
            refusal("modeled-pthread join requires a null result slot")
        } else if let Some(handle) = super::threads::ThreadHandle::from_c_value(&path.values[0]) {
            let current = super::reasoning::path_facts::assumptions_with_path_context(
                assumptions,
                &path.facts,
                &path.obligations,
            );
            match super::threads::ThreadContext::new(state.clone()).and_then(|context| {
                context.join(
                    handle,
                    super::threads::JoinRuntimeAssumption::ValidJoinSucceeds,
                    &current,
                )
            }) {
                Ok((joined, facts)) => {
                    path.facts.extend(facts);
                    let mut next = joined.parent().clone();
                    if target.is_some_and(|target| {
                        assign_call_result(
                            &mut next,
                            target,
                            CValue::Int32(Bitvector32Term::Constant(0)),
                            &mut path.obligations,
                            &current,
                        )
                        .is_none()
                    }) {
                        CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
                    } else {
                        CStatementOutcome::Normal(next)
                    }
                }
                Err(message) => refusal(message),
            }
        } else {
            refusal("modeled-pthread join handle does not name a live child")
        };
        paths.push(CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome,
            facts: path.facts,
            obligations: path.obligations,
            loan_evidence: empty_checked_loan_evidence_sequence(),
        });
    }
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
                CFunctionOutcome::Throw { value, state } => {
                    CStatementOutcome::Throw { value, state }
                }
                CFunctionOutcome::VerificationDiverges => CStatementOutcome::VerificationDiverges,
                CFunctionOutcome::UndefinedBehavior(undefined_behavior) => {
                    CStatementOutcome::UndefinedBehavior(undefined_behavior)
                }
                CFunctionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
            };
            CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome,
                facts: path.facts,
                obligations: path.obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
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
    budget.install_c_byte_order(environment.byte_order());
    if function_type == CType::FunctionPointer(CallbackSignature::UNSPECIFIED) {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                "indirect calls require a supported callback signature".into(),
            )),
            facts: Vec::new(),
            obligations: Vec::new(),

            loan_evidence: empty_checked_loan_evidence_sequence(),
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

                                loan_evidence: empty_checked_loan_evidence_sequence(),});
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

                                loan_evidence: empty_checked_loan_evidence_sequence(),
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

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            }
            CExpressionOutcome::RuntimeError(error) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
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

                    loan_evidence: empty_checked_loan_evidence_sequence(),
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

                    loan_evidence: empty_checked_loan_evidence_sequence(),
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

                    loan_evidence: empty_checked_loan_evidence_sequence(),
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
                    loan_evidence: call_path.loan_evidence,
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
    prefix_loan_evidence: &CheckedLoanCallEvidenceSequence,
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
            loop_invariant_correspondence: Default::default(),
            outcome: path.outcome,
            facts,
            obligations,
            loan_evidence: concat_checked_loan_evidence(prefix_loan_evidence, &path.loan_evidence),
        })
    })
    .collect::<Vec<_>>();
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn execute_statement_suffix_with_loan_evidence(
    state: &CState,
    statement: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    prefix_facts: &[ExecutionPureFact],
    prefix_obligations: &[ProofObligation],
    prefix_loan_evidence: &CheckedLoanCallEvidenceSequence,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let suffix_paths = execute_c_statement_verification_paths_with_prefix(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        prefix_facts,
        prefix_obligations,
        budget,
        variables,
    )?;
    Ok(suffix_paths
        .into_iter()
        .map(|mut path| {
            path.loan_evidence =
                concat_checked_loan_evidence(prefix_loan_evidence, &path.loan_evidence);
            path
        })
        .collect())
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
    budget.install_c_byte_order(environment.byte_order());
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
                let CStatementExecutionPath {
                    loop_invariant_correspondence: _,
                    outcome,
                    facts,
                    obligations,
                    loan_evidence,
                } = first_path;
                match outcome {
                    CStatementOutcome::Normal(state) => {
                        if loan_evidence.is_empty() {
                            paths.extend(execute_c_statement_verification_paths_with_prefix(
                                &state,
                                second,
                                assumptions,
                                environment,
                                execution_semantics,
                                &facts,
                                &obligations,
                                budget,
                                variables,
                            )?);
                        } else {
                            paths.extend(execute_statement_suffix_with_loan_evidence(
                                &state,
                                second,
                                assumptions,
                                environment,
                                execution_semantics,
                                &facts,
                                &obligations,
                                &loan_evidence,
                                budget,
                                variables,
                            )?);
                        }
                    }
                    outcome @ (CStatementOutcome::Break(_)
                    | CStatementOutcome::Continue(_)
                    | CStatementOutcome::Jump { .. }
                    | CStatementOutcome::Return { .. }
                    | CStatementOutcome::Throw { .. }
                    | CStatementOutcome::VerificationDiverges
                    | CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_)) => paths.push(CStatementExecutionPath {
                        loop_invariant_correspondence: Default::default(),
                        outcome,
                        facts,
                        obligations,
                        loan_evidence,
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
            for condition_path in evaluate_c_condition_paths(state, condition, assumptions, budget)?
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
                            // The arm is a scope: what it declares stops
                            // existing however control leaves it.
                            let declared = scope_declared_names(branch);
                            paths.extend(paths_after_scope_exit(
                                execute_c_statement_verification_paths_with_prefix(
                                    &branch_state,
                                    branch,
                                    assumptions,
                                    environment,
                                    execution_semantics,
                                    &truthiness_path.facts,
                                    &truthiness_path.obligations,
                                    budget,
                                    variables,
                                )?,
                                &declared,
                            ));
                        }
                    }
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                        paths.push(CStatementExecutionPath {
                            loop_invariant_correspondence: Default::default(),
                            outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                            facts,
                            obligations,

                            loan_evidence: empty_checked_loan_evidence_sequence(),
                        })
                    }
                    CExpressionOutcome::RuntimeError(error) => {
                        paths.push(CStatementExecutionPath {
                            loop_invariant_correspondence: Default::default(),
                            outcome: CStatementOutcome::RuntimeError(error),
                            facts,
                            obligations,

                            loan_evidence: empty_checked_loan_evidence_sequence(),
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
            backedge_target,
            natural_exit_target,
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
                *backedge_target,
                *natural_exit_target,
            )?
        }
        _ => {
            // Loop verification and verified-call execution share one symbolic
            // identity stream: `variables` allocates from `budget`, so nothing
            // has to be synchronized across this boundary.
            let operation = match statement {
                CStatement::Skip => "verification statement: skip",
                CStatement::Break => "verification statement: break",
                CStatement::Continue => "verification statement: continue",
                CStatement::Goto { .. } => "verification statement: goto",
                CStatement::ForStep { .. } => "verification statement: continue with for step",
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
                CStatement::Throw(_) => "verification statement: throw",
                CStatement::TryCatchInt32 { .. } => "verification statement: int32 handler",
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
            loop_invariant_correspondence: Default::default(),
            outcome: path.outcome,
            facts,
            obligations,
            loan_evidence: path.loan_evidence,
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
    ranking_measures: &[CRankingComponent],
    structural_measure: Option<&str>,
    body: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
    do_while: bool,
    backedge_target: Option<CControlTargetId>,
    natural_exit_target: Option<CControlTargetId>,
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
        &[],
        execution_semantics,
        false,
        do_while,
        backedge_target,
        natural_exit_target,
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
        .map_err(|limit| {
            format!(
                "could not classify the loop condition: it stopped at {}",
                limit.describe()
            )
        })
}

fn c_loop_condition_feasibility(
    state: &CState,
    condition: &CExpression,
    assumptions: &PureFactContext,
) -> ExecutionResult<(bool, bool)> {
    let mut budget = ExecutionBudget::beside_live_state().with_c_expression_cost(condition);
    let expression_paths = evaluate_c_condition_paths(state, condition, assumptions, &mut budget)?;
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
    if !top_state
        .memory()
        .heap
        .have_same_allocation_lifetimes(&next_state.memory().heap)
    {
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
    if top_state.loan_ledger != next_state.loan_ledger {
        changed.push("stable-view loan authority");
    }
    if top_state.loan_participant != next_state.loan_participant {
        changed.push("stable-view loan participant");
    }
    if top_state.loan_view_bindings != next_state.loan_view_bindings {
        changed.push("stable-view occurrence bindings");
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
    ranking_measures: &[CRankingComponent],
    structural_measure: Option<&str>,
    body: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    initialization_proven: bool,
    preservation_proven: bool,
    final_exit_candidates: &[CLoopFinalExitCandidate],
    break_exits: &[CLoopBreakExit],
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
    do_while: bool,
    backedge_target: Option<CControlTargetId>,
    natural_exit_target: Option<CControlTargetId>,
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
        break_exits,
        execution_semantics,
        initialization_proven,
        do_while,
        backedge_target,
        natural_exit_target,
        budget,
        variables,
    )
}

/// Whether one exact condition fact is the negation of another.
fn condition_fact_refutes(fact: &Proposition, other: &Proposition) -> bool {
    match (fact, other) {
        (Proposition::ConditionIs(left, left_value), Proposition::ConditionIs(right, value)) => {
            left == right && left_value != value
        }
        _ => false,
    }
}

/// The disjunction of what each short-circuit guard path states on its own.
///
/// One entry per path, holding only the facts that path added. A conjunct an
/// earlier disjunct contradicts is dropped, which only weakens that disjunct
/// and so keeps the disjunction true, turning `!a | (a & !b)` into the
/// `!a | !b` a proof can name. A path that states nothing of its own makes the
/// whole disjunction vacuous, so there is nothing to export.
///
/// The disjuncts come out in short-circuit evaluation order, which is a stable
/// sort of the paths by how many facts each states: the path that decided the
/// guard on an earlier operand states fewer of them, and ties keep the order
/// the paths were enumerated in. The kernel enumerates a disjunctive guard's
/// entry paths with the operand-false one first, so `a || b` would otherwise
/// read `(a == 0 and b != 0) or a != 0` instead of the `a != 0 or b != 0` a
/// proof writes. Narrowing runs after the sort, so it drops the conjunct the
/// short-circuit path refutes rather than the other way round. Both the entry
/// join and the exit join come through here, so they agree on the spelling.
pub(super) fn guard_path_disjunction(own_facts: &[Vec<Proposition>]) -> Option<Proposition> {
    if own_facts.len() <= 1 {
        return None;
    }
    let mut ordered = own_facts.iter().collect::<Vec<_>>();
    ordered.sort_by_key(|own| own.len());
    let mut disjuncts = Vec::new();
    for (index, own) in ordered.iter().enumerate() {
        let narrowed = own
            .iter()
            .filter(|fact| {
                !ordered[..index].iter().any(|facts| {
                    facts
                        .iter()
                        .any(|earlier| condition_fact_refutes(earlier, fact))
                })
            })
            .collect::<Vec<_>>();
        let mut own = if narrowed.is_empty() {
            own.iter().collect::<Vec<_>>().into_iter()
        } else {
            narrowed.into_iter()
        };
        let first = own.next()?;
        disjuncts.push(own.fold(first.clone(), |left, right| {
            Proposition::And(Box::new(left), Box::new(right.clone()))
        }));
    }
    let mut disjunction = disjuncts.pop()?;
    while let Some(disjunct) = disjuncts.pop() {
        disjunction = Proposition::Or(Box::new(disjunct), Box::new(disjunction));
    }
    Some(disjunction)
}

/// Joins the exit paths of one loop guard into the single exit the loop rule
/// certifies.
///
/// A short-circuit guard such as `while (a && b)` leaves the loop by one path
/// per conjunct: `!a`, or `a && !b`. They reach the same exit state — the
/// loop's top state, with the invariants holding and the body's effects
/// summarized — and differ only in what the failed guard says. Dropping any of
/// them would export an exit the C never reaches that way (the hole S1
/// closed), and keeping them as separate statement successors is what the
/// `loop` tactic refused. So the rule exports their join instead: every fact
/// all the paths state, in the order the first path stated them, followed by
/// the disjunction of what each path states alone. A proof after the loop
/// reasons from the disjunction by cases.
///
/// Obligations are the union: an obligation any exit path owes is owed by the
/// join, which can only refuse more, never less. Keep deterministic fact
/// order; invariant source correspondence is retained separately by clause
/// index and never inferred from this ordering.
fn join_loop_exit_paths(
    mut exits: Vec<LoopExitFacts>,
) -> Option<(
    Vec<ExecutionPureFact>,
    Vec<ProofObligation>,
    CheckedLoanCallEvidenceSequence,
)> {
    if exits.len() <= 1 {
        let exit = exits.pop()?;
        return Some((exit.stated, exit.obligations, exit.loan_evidence));
    }
    let (first_facts, first_obligations) = (exits[0].stated.clone(), exits[0].obligations.clone());
    let loan_evidence = exits[1..]
        .iter()
        .fold(exits[0].loan_evidence.clone(), |sequence, exit| {
            concat_checked_loan_evidence(&sequence, &exit.loan_evidence)
        });
    let shared = first_facts
        .iter()
        .filter(|fact| {
            exits[1..].iter().all(|exit| {
                exit.stated
                    .iter()
                    .any(|other| other.proposition() == fact.proposition())
            })
        })
        .cloned()
        .collect::<Vec<_>>();
    let own_facts = exits
        .iter()
        .map(|exit| {
            exit.disjunct
                .iter()
                .filter(|proposition| {
                    !shared
                        .iter()
                        .any(|common| common.proposition() == *proposition)
                })
                .cloned()
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    // Short-circuit paths refine one another: the second conjunct's exit also
    // states the first conjunct true, which the first exit states false. A
    // conjunct another disjunct contradicts is dropped, which only weakens
    // that disjunct and so keeps the disjunction true, and turns
    // `!a | (a & !b)` into the `!a | !b` a proof can name.
    let mut facts = shared;
    if let Some(disjunction) = guard_path_disjunction(&own_facts) {
        facts.push(ExecutionPureFact::new(disjunction));
    }
    let mut obligations = first_obligations;
    for exit in exits.iter().skip(1) {
        for obligation in &exit.obligations {
            if !obligations.contains(obligation) {
                obligations.push(obligation.clone());
            }
        }
    }
    Some((facts, obligations, loan_evidence))
}

/// One exit's contribution to a loop's join.
///
/// `stated` is what that path actually holds, and the join's common prefix is
/// the intersection of those. These facts keep the symbolic names under
/// which they were established; they are not necessarily exit invariants.
/// `disjunct` is the same path restated about the successor the join builds:
/// with no abstraction it is exactly `stated`, and when a component was
/// abstracted it is that path's own description of the fresh names instead of
/// names the loop left behind.
struct LoopExitFacts {
    stated: Vec<ExecutionPureFact>,
    disjunct: Vec<Proposition>,
    obligations: Vec<ProofObligation>,
    loan_evidence: CheckedLoanCallEvidenceSequence,
}

impl LoopExitFacts {
    /// An exit whose state the join did not have to abstract: it describes the
    /// successor in the names it already used.
    fn unabstracted(
        facts: Vec<ExecutionPureFact>,
        obligations: Vec<ProofObligation>,
        loan_evidence: CheckedLoanCallEvidenceSequence,
    ) -> Self {
        Self {
            disjunct: facts
                .iter()
                .map(|fact| fact.proposition().clone())
                .collect(),
            stated: facts,
            obligations,
            loan_evidence,
        }
    }
}

/// Joins every way out of one loop into the single successor path the
/// enclosing frontier continues from.
///
/// The guard-false exits stand at the loop's head state; a `break` exit
/// stands where that path left the body. A loop has one successor, so the
/// exits that reach one state are joined by [`join_loop_exit_paths`], which
/// keeps what every exit states and disjoins what each states alone.
///
/// Exits that reach *different* states are described the way the loop head
/// describes an arbitrary visit (D5), by
/// [`abstract_loop_exit_states`]: the loop's declared binders are rebound at
/// each exit by family and argument equality, whatever the body called them;
/// every component the exits disagree about — a binder's model, a local, a
/// cell one exit wrote differently — becomes one fresh name; and each exit
/// contributes, as its own disjunct, the equations pinning those fresh names
/// to what that exit actually reached. Each disjunct is exactly what its path
/// established about the successor, so the join is the standard weakening and
/// nothing is assumed of an exit that did not state it. A component no binder
/// can describe is still refused by name; dropping an exit, or picking one
/// exit's state for all of them, would export an exit the C never reaches
/// that way.
fn join_loop_exits(
    head: &CLoopHead,
    invariant_propositions: &crate::kernel::proof::PersistentSequence<Proposition>,
    binders: &[CLoopBinder],
    exits: Vec<(
        CState,
        Vec<ExecutionPureFact>,
        Vec<ProofObligation>,
        CheckedLoanCallEvidenceSequence,
    )>,
    assumptions: &PureFactContext,
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Option<CStatementExecutionPath> {
    let exit_state = exits.first()?.0.clone();
    let states = exits
        .iter()
        .map(|(state, _, _, _)| state)
        .collect::<Vec<_>>();
    let unchanged = || vec![LoopExitRestatement::default(); exits.len()];
    let invariant_state_unchanged = states[1..].iter().all(|other| **other == exit_state);
    let (exit_state, restatements, mismatch) = if invariant_state_unchanged {
        (exit_state, unchanged(), None)
    } else {
        match abstract_loop_exit_states(head, binders, &states, assumptions, variables, budget) {
            Ok((state, restatements)) => (state, restatements, None),
            Err(mismatch) => (exit_state, unchanged(), Some(mismatch)),
        }
    };
    let (facts, mut obligations, loan_evidence) = join_loop_exit_paths(
        exits
            .into_iter()
            .zip(restatements)
            .map(|((_, facts, obligations, loan_evidence), restatement)| {
                restatement.restate(facts, obligations, loan_evidence)
            })
            .collect(),
    )?;
    if let Some(mismatch) = mismatch {
        obligations.push(
            ProofObligation::verification_condition(false_equals_true_proposition())
                .with_context(format!(
                    "loop exits reach different states, so they have no common successor: {mismatch}"
                )),
        );
    }
    // Only name invariants whose source still denotes this successor. A
    // changed-state break can leave old head facts in the intersection; those
    // facts must not acquire spellings about fresh exit values.
    let loop_invariant_correspondence = if invariant_state_unchanged {
        retained_loop_invariant_correspondence(invariant_propositions, &facts)
    } else {
        Default::default()
    };
    Some(CStatementExecutionPath {
        loop_invariant_correspondence,
        outcome: CStatementOutcome::Normal(exit_state),
        facts,
        obligations,

        loan_evidence,
    })
}

/// Associate only this producer's surviving facts with the original clause
/// indices. Semantic duplicates retain each index; guard and lowering side
/// facts never consume a clause slot. Work is confined to the output delta.
fn retained_loop_invariant_correspondence(
    declarations: &crate::kernel::proof::PersistentSequence<Proposition>,
    facts: &[ExecutionPureFact],
) -> LoopInvariantCorrespondence {
    if declarations.is_empty() {
        return Default::default();
    }
    let correspondence = retained_loop_invariant_declarations(
        declarations.iter(),
        facts.iter().map(ExecutionPureFact::proposition),
    )
    .into_iter()
    .map(|(index, proposition)| (index, proposition.clone()))
    .collect::<Vec<_>>();
    LoopInvariantCorrespondence((!correspondence.is_empty()).then(|| correspondence.into()))
}

fn retained_loop_invariant_declarations<'a, T: Ord + 'a>(
    declarations: impl Iterator<Item = &'a T>,
    facts: impl Iterator<Item = &'a T>,
) -> Vec<(usize, &'a T)> {
    let emitted = facts.collect::<BTreeSet<_>>();
    declarations
        .enumerate()
        .filter(|(_, proposition)| emitted.contains(proposition))
        .collect()
}

#[cfg(test)]
mod loop_invariant_correspondence_tests {
    use super::*;
    use std::cell::Cell;

    #[test]
    fn declaration_identity_survives_duplicates_missing_facts_and_guard_facts() {
        let declarations = [3, 3, 8, 9, 9];
        let emitted = [42, 9, 3, 17];
        assert_eq!(
            retained_loop_invariant_declarations(declarations.iter(), emitted.iter()),
            [(0, &3), (1, &3), (3, &9), (4, &9)],
        );
    }

    #[test]
    fn loop_invariant_correspondence_has_output_logarithmic_indexing_cost() {
        #[derive(Eq)]
        struct Counted<'a>(usize, &'a Cell<usize>);
        impl PartialEq for Counted<'_> {
            fn eq(&self, other: &Self) -> bool {
                self.cmp(other).is_eq()
            }
        }
        impl PartialOrd for Counted<'_> {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for Counted<'_> {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.1.set(self.1.get() + 1);
                self.0.cmp(&other.0)
            }
        }
        for size in [32usize, 128, 512, 2048] {
            let comparisons = Cell::new(0);
            let declarations = (0..size)
                .flat_map(|i| [Counted(i, &comparisons), Counted(i, &comparisons)])
                .collect::<Vec<_>>();
            let facts = (0..size)
                .rev()
                .map(|i| Counted(i, &comparisons))
                .collect::<Vec<_>>();
            let retained = retained_loop_invariant_declarations(declarations.iter(), facts.iter());
            assert_eq!(retained.len(), size * 2);
            assert!(
                comparisons.get() <= 16 * size * (size.ilog2() as usize + 1),
                "size {size}: {} comparisons",
                comparisons.get()
            );
        }
    }
}

/// The one post-loop state several exits join into, and the equations each
/// exit owes about it.
///
/// This is decision D5 applied at the exits, exactly as the loop head and the
/// back edge apply it. Every exit first rebinds the loop's declared binders by
/// family and argument equality, so a body that refolded its instance under
/// another name still hands the loop back the resource the header declared.
/// Then, component by component, the exits' agreement is kept and their
/// disagreement is replaced by a fresh symbolic name:
///
/// - a declared binder's arguments and fields (the loop head havocs the same
///   fields, for the same reason: an exit's model is whatever its own path
///   established, and the successor holds only the disjunction of those);
/// - the locals the exits disagree on, with the local's stack cell resynced;
/// - a memory cell the exits wrote differently, which is a cell folded into a
///   declared binder — the loop body owns nothing else — and which a proof
///   after the loop therefore reads back through that binder's model.
///
/// The returned restatement is per exit: it pins every fresh name to the value
/// that exit reached, so the caller's disjunction says exactly "the successor
/// is what one of these exits reached" and never more, and it renames the
/// exit's own bare symbolic values to those fresh names so the disjunct speaks
/// about the successor rather than about a value the loop left behind.
///
/// Refusals are named, never silent: an exit that holds no instance for a
/// declared binder, a cell the exits disagree about when the loop declares no
/// binder to describe it, and any disagreement outside these components
/// (allocation lifetimes, block shapes, ownership beyond the binders) refuse
/// with the component that differs.
///
/// Cost is the loop's own binders, the locals the exits disagree on, and the
/// cells they disagree on; no unrelated project-wide or path-wide state is
/// scanned, and a component every exit agrees on is compared once and kept.
fn abstract_loop_exit_states(
    head: &CLoopHead,
    binders: &[CLoopBinder],
    states: &[&CState],
    assumptions: &PureFactContext,
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Result<(CState, Vec<LoopExitRestatement>), String> {
    let mut rebound = Vec::with_capacity(states.len());
    for (index, state) in states.iter().enumerate() {
        match c_loop_state_with_loop_binders_rebound(&head.top, state, binders, assumptions) {
            Ok(state) => rebound.push(state),
            Err(failure) => {
                return Err(format!("at loop exit {}, {failure}", index + 1));
            }
        }
    }
    let mut successor = rebound[0].clone();
    let mut restatements = vec![LoopExitRestatement::default(); rebound.len()];
    abstract_loop_exit_binders(
        &mut successor,
        &rebound,
        binders,
        &mut restatements,
        variables,
        budget,
    )?;
    let locals = abstract_loop_exit_locals(
        &mut successor,
        &rebound,
        &mut restatements,
        variables,
        budget,
    )?;
    let resynced = locals
        .iter()
        .filter_map(|(name, _)| successor.locals.slot(name).cloned())
        .collect::<BTreeSet<_>>();
    // A cell the exits wrote differently is described through a binder's
    // model, so a cell the loop declared as plain memory of its own has no
    // such description. Those ranges are what the head handed the body
    // besides its binders.
    let declared_memory = if binders.is_empty() {
        Vec::new()
    } else {
        loop_declared_memory_ranges(&head.body)
    };
    let cells = abstract_loop_exit_memory(
        &mut successor,
        &rebound,
        &resynced,
        binders.is_empty(),
        &declared_memory,
        assumptions,
        &mut restatements,
        variables,
        budget,
    )?;
    // Everything the rule knows how to describe has now been made common. A
    // state that still differs differs in something this rule does not model,
    // so it is refused under its own name rather than abstracted blindly.
    if let Some(mismatch) = rebound.iter().find_map(|state| {
        loop_exit_residual_difference(&successor, state, &locals, &cells, binders)
    }) {
        return Err(mismatch);
    }
    Ok((successor, restatements))
}

/// What one loop exit owes about the successor the join exports.
///
/// `equations` pin the successor's fresh names to the values this exit
/// reached. `renamings` say which bare symbolic value this exit held for a
/// name the successor now calls something else: a guard-false exit stands at
/// the loop head, where every local the body writes is one fresh variable, so
/// `i <= 0` there is a fact about a variable that no longer names anything
/// after the loop. Rewriting this exit's own facts through its own equation is
/// the weakening that turns such a fact into one about the local a proof after
/// the loop can name, and it is valid exactly because the equation holds on
/// this path — which is why it is applied only to this exit's disjunct.
#[derive(Clone, Debug, Default)]
struct LoopExitRestatement {
    equations: Vec<Proposition>,
    renamings: Vec<(Variable, Bitvector32Term)>,
}

impl LoopExitRestatement {
    /// Records that this exit's `held` value became the successor's `fresh`
    /// one.
    fn pin(&mut self, fresh: &CValue, held: &CValue) {
        // The C comparison form, not a raw term equality: a proof after the
        // loop spells this disjunct as `x == <value>`, and `cases` needs the
        // exported fact to be exactly what that spelling lowers to.
        self.equations.push(
            c_value_comparison_proposition(fresh, CComparisonOperator::Equal, held).unwrap_or_else(
                || Proposition::Equal(Term::CValue(fresh.clone()), Term::CValue(held.clone())),
            ),
        );
        if let (Some(Bitvector32Term::Variable(from)), Some(to)) =
            (scalar_bitvector(held), scalar_bitvector(fresh))
        {
            self.renamings.push((*from, to.clone()));
        }
    }

    /// Records that this exit's `held` resource argument or field became the
    /// successor's `fresh` one.
    fn pin_resource_value(&mut self, fresh: &AlgebraicValue, held: &AlgebraicValue) {
        if let (AlgebraicValue::C(fresh), AlgebraicValue::C(held)) = (fresh, held) {
            self.pin(fresh, held);
            return;
        }
        self.equations.push(Proposition::Equal(
            resource_value_term(fresh),
            resource_value_term(held),
        ));
    }

    /// This exit's contribution to the join: what it states, and the same
    /// path restated about the successor's fresh names for its disjunct.
    ///
    /// The restated reading never replaces what the path stated — the loop
    /// may retain historical facts under the names the head stated them —
    /// but the disjunct is built from the restated reading
    /// alone, because a name the loop left behind is one no proof after the
    /// loop can spell, and a `cases` over the exported disjunction has to
    /// spell it.
    fn restate(
        self,
        facts: Vec<ExecutionPureFact>,
        obligations: Vec<ProofObligation>,
        loan_evidence: CheckedLoanCallEvidenceSequence,
    ) -> LoopExitFacts {
        if self.renamings.is_empty() && self.equations.is_empty() {
            return LoopExitFacts::unabstracted(facts, obligations, loan_evidence);
        }
        let rename = |proposition: &Proposition| {
            self.renamings
                .iter()
                .fold(proposition.clone(), |proposition, (from, to)| {
                    substitute_bitvector_variable_in_proposition(&proposition, *from, to)
                })
        };
        let mut disjunct = facts
            .iter()
            .map(|fact| rename(fact.proposition()))
            .collect::<Vec<_>>();
        for equation in &self.equations {
            // An equation the renaming covers is dropped: every fact this exit
            // stated about the renamed value was restated about the
            // successor's name above, so keeping it would state nothing.
            let renamed = rename(equation);
            if equation_states_nothing(&renamed) {
                continue;
            }
            disjunct.push(renamed);
        }
        LoopExitFacts {
            stated: facts,
            disjunct,
            obligations,
            loan_evidence,
        }
    }
}

/// Whether a pinning equation has become vacuous, which is what a renaming
/// that already covered it leaves behind.
fn equation_states_nothing(equation: &Proposition) -> bool {
    match equation {
        Proposition::Equal(left, right) => left == right,
        Proposition::ConditionIs(condition, value) => {
            PureFactContext::decide_intrinsically(condition) == Some(*value)
        }
        _ => false,
    }
}

/// The scalar term a C value carries, for the one-variable renaming above.
fn scalar_bitvector(value: &CValue) -> Option<&Bitvector32Term> {
    match value {
        CValue::Int8(term) => Some(term),
        CValue::Bool(term)
        | CValue::Int16(term)
        | CValue::Int32(term)
        | CValue::UInt8(term)
        | CValue::UInt16(term)
        | CValue::UInt32(term)
        | CValue::Int64(term)
        | CValue::UInt64(term)
        | CValue::Float32(term)
        | CValue::Float64(term) => Some(term),
        CValue::Void | CValue::Pointer(_) => None,
    }
}

/// Gives each declared loop binder the arguments and fields every exit agrees
/// on, and one fresh name wherever they disagree.
fn abstract_loop_exit_binders(
    successor: &mut CState,
    exits: &[CState],
    binders: &[CLoopBinder],
    restatements: &mut [LoopExitRestatement],
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Result<(), String> {
    for binder in binders {
        let mut instances = Vec::with_capacity(exits.len());
        for (index, state) in exits.iter().enumerate() {
            let Some(instance) = state.resources().owned_instance(binder.identity) else {
                return Err(format!(
                    "at loop exit {}, loop binder `{}` holds no instance",
                    index + 1,
                    binder.name
                ));
            };
            instances.push(instance.clone());
        }
        let base = instances[0].clone();
        if instances[1..]
            .iter()
            .any(|instance| instance.name != base.name || instance.schema != base.schema)
        {
            return Err(format!(
                "the exits hold different resources for loop binder `{}`",
                binder.name
            ));
        }
        let arguments = joined_resource_values(
            &base.arguments,
            instances.iter().map(|instance| &instance.arguments),
            restatements,
            variables,
            budget,
        )?;
        let fields = joined_resource_values(
            &base.fields,
            instances.iter().map(|instance| &instance.fields),
            restatements,
            variables,
            budget,
        )?;
        if arguments == base.arguments && fields == base.fields {
            continue;
        }
        let Some(joined) = ResourceInstance::new(
            binder.identity,
            base.name.clone(),
            arguments,
            base.schema.clone(),
            fields,
        ) else {
            return Err(format!(
                "loop binder `{}` names an instance whose fields do not match its schema",
                binder.name
            ));
        };
        let Some(resources) = successor.resources().clone().without_fact_incrementally(
            &CResourceFact::own(CResource::Instance(base)),
            &PureFactContext::new(),
        ) else {
            return Err(format!(
                "loop binder `{}` could not be rebound at the loop's exit",
                binder.name
            ));
        };
        *successor = successor.clone().with_resource_context(
            resources.unchecked_with_fact(CResourceFact::own(CResource::Instance(joined))),
        );
    }
    Ok(())
}

/// One resource argument or field vector, position by position: the common
/// value where every exit agrees, a fresh name plus one equation per exit
/// where they do not.
fn joined_resource_values<'a>(
    base: &ResourceArguments,
    exits: impl Iterator<Item = &'a ResourceArguments> + Clone,
    restatements: &mut [LoopExitRestatement],
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Result<ResourceArguments, String> {
    let mut joined = base.to_vec();
    for (position, value) in joined.iter_mut().enumerate() {
        let mut held = Vec::with_capacity(restatements.len());
        for exit in exits.clone() {
            let Some(value) = exit.get(position) else {
                return Err("the exits hold resource instances of different widths".to_string());
            };
            held.push(value.clone());
        }
        if held.iter().all(|other| other == value) {
            continue;
        }
        let fresh = fresh_resource_value_like(value, variables, budget)?;
        for (restatement, held) in restatements.iter_mut().zip(held) {
            restatement.pin_resource_value(&fresh, &held);
        }
        *value = fresh;
    }
    Ok(joined.into())
}

/// A fresh symbolic value of the same sort as `value`.
fn fresh_resource_value_like(
    value: &AlgebraicValue,
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Result<AlgebraicValue, String> {
    let variable = variables.next_in(budget).map_err(exhausted_identities)?;
    Ok(match value {
        AlgebraicValue::Integer(_) => AlgebraicValue::Integer(IntegerTerm::Variable(variable)),
        AlgebraicValue::C(value) => {
            AlgebraicValue::C(symbolic_call_result(value.c_type(), variable))
        }
        AlgebraicValue::Algebraic(term) => AlgebraicValue::Algebraic(AlgebraicTerm {
            algebraic_type: term.algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(variable),
        }),
    })
}

/// The loop-exit abstraction reports its refusals as text the caller shows
/// beside the states it could not make common. An exhausted identity counter
/// is one of those refusals, named rather than swallowed.
fn exhausted_identities(limit: ExecutionLimit) -> String {
    format!(
        "the execution has no fresh identity left: it stopped at {}",
        limit.describe()
    )
}

/// One resource argument or field as the term an equation is written over.
fn resource_value_term(value: &AlgebraicValue) -> Term {
    match value {
        AlgebraicValue::Integer(term) => Term::Integer(term.clone()),
        AlgebraicValue::C(value) => Term::CValue(value.clone()),
        AlgebraicValue::Algebraic(term) => Term::Algebraic(term.clone()),
    }
}

/// Havocs the locals the exits disagree on, keeping the rest, and reports
/// which ones it abstracted.
fn abstract_loop_exit_locals(
    successor: &mut CState,
    exits: &[CState],
    restatements: &mut [LoopExitRestatement],
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Result<Vec<(String, CType)>, String> {
    let mut abstracted = Vec::new();
    let names = successor
        .locals()
        .object_values()
        .map(|(name, _)| name.to_string())
        .collect::<Vec<_>>();
    for name in names {
        let mut held = Vec::with_capacity(exits.len());
        for state in exits {
            let Some(value) = state.locals().get(&name) else {
                return Err(format!("local `{name}` is not bound by every exit"));
            };
            held.push(value.clone());
        }
        if held[1..].iter().all(|value| *value == held[0]) {
            continue;
        }
        let Some(c_type) = successor.local_object_type(&name) else {
            return Err(format!("local `{name}` has no scalar type here"));
        };
        let Some(fresh) =
            fresh_loop_local_value(c_type, variables, budget).map_err(exhausted_identities)?
        else {
            return Err(format!("local `{name}` has no abstract value of its type"));
        };
        for (restatement, held) in restatements.iter_mut().zip(held) {
            restatement.pin(&fresh, &held);
        }
        sync_stack_local(successor, &name, &fresh);
        successor.locals.set_typed(name.clone(), fresh, c_type);
        abstracted.push((name, c_type));
    }
    Ok(abstracted)
}

/// Havocs the cells the exits wrote differently, keeping the rest.
///
/// The loop body owns exactly what the loop header declared, so a cell one
/// exit left holding a different value is a cell inside a declared binder: the
/// binder's model is what a proof after the loop reads it back through, and
/// the disjunction relates the two. A loop that declares no binder has nothing
/// to read such a cell through, so the disagreement is refused by name.
fn abstract_loop_exit_memory(
    successor: &mut CState,
    exits: &[CState],
    resynced: &BTreeSet<Pointer>,
    no_binders: bool,
    declared_memory: &[CMemoryRange],
    assumptions: &PureFactContext,
    restatements: &mut [LoopExitRestatement],
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Result<BTreeSet<Pointer>, String> {
    let mut memory = successor.memory().clone();
    if exits.iter().any(|state| {
        !state
            .memory()
            .heap
            .have_same_allocation_lifetimes(&memory.heap)
    }) {
        return Err("heap allocation lifetimes".to_string());
    }
    let pointers = memory
        .cells
        .keys()
        .filter(|pointer| !resynced.contains(*pointer))
        .cloned()
        .collect::<Vec<_>>();
    let mut dropped = Vec::new();
    let mut havoced = Vec::new();
    for pointer in pointers {
        let mut held = Vec::with_capacity(exits.len());
        for state in exits {
            match state.memory().cells.get(&pointer) {
                Some(value) => held.push(value.clone()),
                // A cell one exit does not hold is authority the successor
                // cannot have; dropping it only makes a later read fail.
                None => {
                    dropped.push(pointer.clone());
                    break;
                }
            }
        }
        if held.len() != exits.len() {
            continue;
        }
        if held[1..].iter().all(|value| *value == held[0]) {
            continue;
        }
        if no_binders || !assumptions.ranges_proven_disjoint_from_pointer(declared_memory, &pointer)
        {
            return Err(format!(
                "the cell in `{}` that the exits write differently is owned by no loop binder",
                pointer.block
            ));
        }
        let Some(fresh) = fresh_loop_local_value(held[0].c_type(), variables, budget)
            .map_err(exhausted_identities)?
        else {
            return Err(format!(
                "the cell in `{}` has no abstract value of its type",
                pointer.block
            ));
        };
        for (restatement, held) in restatements.iter_mut().zip(held) {
            restatement.pin(&fresh, &held);
        }
        havoced.push((pointer, fresh));
    }
    if let Some(ledger) = successor.loan_ledger() {
        for pointer in dropped
            .iter()
            .chain(havoced.iter().map(|(pointer, _)| pointer))
        {
            let byte_width = memory
                .cells
                .get(pointer)
                .map(CValue::byte_width)
                .unwrap_or(0);
            if byte_width == 0 {
                continue;
            }
            let range = CMemoryRange::new_with_element_width(
                pointer.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(byte_width),
                1,
            );
            if ledger
                .permits_memory_access_with_assumptions(&range, assumptions)
                .is_err()
            {
                return Err(format!(
                    "the cell in `{}` that the exits abstract is under an active stable-view loan",
                    pointer.block
                ));
            }
        }
    }
    let mut abstracted = BTreeSet::new();
    if !dropped.is_empty() || !havoced.is_empty() {
        let cells = std::sync::Arc::make_mut(&mut memory.cells);
        for pointer in dropped {
            cells.remove(&pointer);
            abstracted.insert(pointer);
        }
        for (pointer, value) in havoced {
            cells.insert(pointer.clone(), value);
            abstracted.insert(pointer);
        }
        *successor = successor.clone().with_memory(memory);
    }
    Ok(abstracted)
}

/// The memory ranges a loop's own header declared, rather than folded into one
/// of its binders.
fn loop_declared_memory_ranges(body_state: &CState) -> Vec<CMemoryRange> {
    body_state
        .resources()
        .facts()
        .iter()
        .filter_map(|fact| match fact {
            CResourceFact::Own(CResource::Memory(range), _) => Some(range.clone()),
            _ => None,
        })
        .collect()
}

/// The abstract value a loop havoc gives a local of this type, if it has one.
fn fresh_loop_local_value(
    c_type: CType,
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<CValue>> {
    // An array object is never assigned by name (C forbids it) and binds as
    // an array object rather than a scalar one, and `void` has no value, so
    // neither type takes an identity from the counter at all.
    match c_type {
        CType::Int8Array(_) => return Ok(None),
        CType::Void
        | CType::Int32Array(_)
        | CType::UInt8Array(_)
        | CType::Int16Array(_)
        | CType::UInt16Array(_)
        | CType::UInt32Array(_)
        | CType::Int64Array(_)
        | CType::UInt64Array(_)
        | CType::Float32Array(_)
        | CType::Float64Array(_) => return Ok(None),
        _ => {}
    }
    let variable = variables.next_in(budget)?;
    Ok(Some(match c_type {
        CType::Bool => CValue::Bool(Bitvector32Term::Variable(variable)),
        CType::Int8 => int8(Bitvector32Term::Variable(variable)),
        CType::Int16 => int16(Bitvector32Term::Variable(variable)),
        CType::Int32 => int32(Bitvector32Term::Variable(variable)),
        CType::UInt8 => uint8(Bitvector32Term::Variable(variable)),
        CType::UInt16 => uint16(Bitvector32Term::Variable(variable)),
        CType::UInt32 => uint32(Bitvector32Term::Variable(variable)),
        CType::Int64 => CValue::Int64(Bitvector32Term::Variable(variable)),
        CType::UInt64 => CValue::UInt64(Bitvector32Term::Variable(variable)),
        CType::Float32 => CValue::Float32(Bitvector32Term::Variable(variable)),
        CType::Float64 => CValue::Float64(Bitvector32Term::Variable(variable)),
        CType::FunctionPointer(_) => {
            CValue::typed_pointer(Pointer::symbolic_function(variable), c_type)
        }
        // A pointer local reassigned in the body (`p = p + 1`) must not keep
        // its entry value across the abstract iteration, exactly as the join
        // abstraction treats it; an invariant must relate it.
        _ => CValue::typed_pointer(Pointer::symbolic(variable), c_type),
    }))
}

/// What an abstracted successor and one exit still disagree about once the
/// components the abstraction deliberately replaced are put back.
///
/// The successor is reconstructed at this exit: its binder instances, its
/// havocked locals, and its havocked cells are restored to the values this
/// exit reached. Anything still different is a component the rule did not
/// model — an allocation lifetime, a block shape, ownership beyond the
/// binders — and the join refuses under that name rather than exporting a
/// state no exit stands in.
fn loop_exit_residual_difference(
    successor: &CState,
    exit: &CState,
    locals: &[(String, CType)],
    cells: &BTreeSet<Pointer>,
    binders: &[CLoopBinder],
) -> Option<String> {
    let mut witness = successor.clone();
    for binder in binders {
        let Some(joined) = witness.resources().owned_instance(binder.identity).cloned() else {
            continue;
        };
        let Some(held) = exit.resources().owned_instance(binder.identity).cloned() else {
            continue;
        };
        let Some(resources) = witness.resources().clone().without_fact_incrementally(
            &CResourceFact::own(CResource::Instance(joined)),
            &PureFactContext::new(),
        ) else {
            continue;
        };
        witness = witness.with_resource_context(
            resources.unchecked_with_fact(CResourceFact::own(CResource::Instance(held))),
        );
    }
    for (name, c_type) in locals {
        let value = exit.locals().get(name)?.clone();
        sync_stack_local(&mut witness, name, &value);
        witness.locals.set_typed(name.clone(), value, *c_type);
    }
    if !cells.is_empty() {
        let mut memory = witness.memory().clone();
        let restored = std::sync::Arc::make_mut(&mut memory.cells);
        for pointer in cells {
            match exit.memory().cells.get(pointer) {
                Some(value) => {
                    restored.insert(pointer.clone(), value.clone());
                }
                None => {
                    restored.remove(pointer);
                }
            }
        }
        witness = witness.with_memory(memory);
    }
    loop_exit_state_difference(&witness, exit)
}

/// What two loop exit states disagree about, named for a refusal.
fn loop_exit_state_difference(left: &CState, right: &CState) -> Option<String> {
    if left == right {
        return None;
    }
    let mut differences = Vec::new();
    let changed_locals = left
        .locals()
        .object_values()
        .filter(|(name, value)| right.locals().get(name) != Some(*value))
        .map(|(name, _)| name.to_string())
        .collect::<Vec<_>>();
    if !changed_locals.is_empty() {
        differences.push(format!("local `{}`", changed_locals.join("`, `")));
    }
    if left.memory() != right.memory() {
        differences.push("memory".to_string());
    }
    if left.resources() != right.resources() {
        differences.push("resource ownership".to_string());
    }
    if left.loan_ledger != right.loan_ledger {
        differences.push("stable-view loan authority".to_string());
    }
    if left.loan_participant != right.loan_participant {
        differences.push("stable-view loan participant".to_string());
    }
    if left.loan_view_bindings != right.loan_view_bindings {
        differences.push("stable-view occurrence bindings".to_string());
    }
    if differences.is_empty() {
        differences.push("the symbolic state".to_string());
    }
    Some(differences.join(", "))
}

#[allow(clippy::too_many_arguments)]
fn execute_c_while_exit_paths(
    state: &CState,
    condition: &CExpression,
    invariant: &[Proposition],
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    resource_specs: &[CResourceSpec],
    ranking_measures: &[CRankingComponent],
    structural_measure: Option<&str>,
    body: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    preservation_environment: Option<&CExecutionEnvironment>,
    final_exit_candidates: &[CLoopFinalExitCandidate],
    break_exits: &[CLoopBreakExit],
    execution_semantics: CExecutionSemantics,
    initialization_proven: bool,
    do_while: bool,
    backedge_target: Option<CControlTargetId>,
    natural_exit_target: Option<CControlTargetId>,
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
    // The loop's declared binders, for the exit join: D5 names them at the
    // head, at the back edge, and at every exit by the same rule.
    let binders = c_loop_binders(resource_specs);
    // The guard and the invariants are read with the selected arm's cells
    // published (D7); the loop's exit outcome stays `top_state`, so that read
    // authority never leaves the head.
    let guard_state = head.guard.clone();
    let whole_loop_effect_summaries = head.summaries.clone();
    let (preservation_obligations, mut final_exit_paths, body_break_exits) =
        if let Some(environment) = preservation_environment {
            let summary = collect_loop_preservation_summary(
                state,
                &head,
                condition,
                invariant_checks,
                &head.effect_checks,
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
                backedge_target,
                natural_exit_target,
                budget,
                variables,
            )?;
            (
                summary.obligations,
                summary.final_exit_paths,
                summary.break_exits,
            )
        } else {
            (Vec::new(), Vec::new(), Vec::new())
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
    let mut candidate_exit_entries = Vec::new();
    if initial_may_continue {
        for candidate in final_exit_candidates {
            let candidate_assumptions =
                assumptions_with_propositions(assumptions, candidate.pure_facts());
            let mut exits = Vec::new();
            for assumption in assume_condition_truthiness(
                candidate.state(),
                condition,
                &composite_resource_definitions,
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
                        loop_invariant_correspondence: Default::default(),
                        outcome: outcome.clone(),
                        facts,
                        obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    });
                    continue;
                }
                exits.push(LoopExitFacts::unabstracted(
                    facts,
                    obligations,
                    candidate.loan_evidence().clone(),
                ));
            }
            if let Some((facts, obligations, loan_evidence)) = join_loop_exit_paths(exits) {
                // A candidate is one more way out, not a second successor:
                // it joins the guard-false and `break` exits below on the
                // same terms. Exporting it as its own path would give the
                // loop statement several successors, and for a `do ... while`
                // — whose only guard-false exit is this one, since its guard
                // is read after the body — it is the exit, so dropping it
                // exported no exit state at all and made every post-loop
                // claim vacuous.
                candidate_exit_entries.push((
                    head.restored_exit_state(candidate.state()),
                    facts,
                    obligations,
                    loan_evidence,
                ));
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
    for (invariant_facts, invariant_obligations, _) in &invariant_contexts {
        if do_while
            || !assume_condition_truthiness(
                &guard_state,
                condition,
                &composite_resource_definitions,
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
    // Every `break` in the body is one more way out of the loop, at the
    // state that path reached. They are certified exits, so they carry no
    // invariant and no measure, and they join the guard-false exit below
    // rather than exporting a second successor the enclosing frontier would
    // have to choose between.
    let break_exit_entries = break_exits
        .iter()
        .chain(body_break_exits.iter())
        .map(|exit| {
            (
                head.restored_exit_state(exit.state()),
                exit.pure_facts()
                    .iter()
                    .cloned()
                    .map(ExecutionPureFact::certified)
                    .collect::<Vec<_>>(),
                loop_check_obligations.clone(),
                exit.loan_evidence().clone(),
            )
        })
        .chain(candidate_exit_entries)
        .collect::<Vec<_>>();
    if initial_may_exit {
        for (invariant_facts, invariant_obligations, invariant_propositions) in invariant_contexts {
            let condition_contexts = assume_condition_truthiness(
                &guard_state,
                condition,
                &composite_resource_definitions,
                assumptions,
                &invariant_facts,
                &invariant_obligations,
                false,
                budget,
            )?;
            let mut exits = Vec::new();
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
                        loop_invariant_correspondence: Default::default(),
                        outcome,
                        facts,
                        obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
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
                for fact in crate::kernel::publish_instance_arms(
                    top_state.resources(),
                    &composite_resource_definitions,
                    &top_state,
                    &exit_assumptions,
                )
                .model_facts
                {
                    facts.push(ExecutionPureFact::new(fact));
                }
                exits.push((facts, obligations, empty_checked_loan_evidence_sequence()));
            }
            // A short-circuit guard leaves the loop by one path per conjunct,
            // all at the same exit state. Every one of them is certified, and
            // the loop exports their join: what they all state, plus the
            // disjunction of what each states alone. A `break` exit joins
            // here too, on the same terms.
            let exits = exits
                .into_iter()
                .map(|(facts, obligations, loan_evidence)| {
                    (top_state.clone(), facts, obligations, loan_evidence)
                })
                .chain(break_exit_entries.iter().cloned())
                .collect::<Vec<_>>();
            if let Some(path) = join_loop_exits(
                &head,
                &invariant_propositions,
                &binders,
                exits,
                assumptions,
                variables,
                budget,
            ) {
                paths.push(path);
            }
        }
    } else if let Some(path) = join_loop_exits(
        &head,
        &Default::default(),
        &binders,
        break_exit_entries,
        assumptions,
        variables,
        budget,
    ) {
        // A guard that cannot be false, `while (true)`, has no guard-false
        // exit: the successor is the join of the `break` exits alone.
        paths.push(path);
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
            loop_invariant_correspondence: Default::default(),
            outcome: CStatementOutcome::VerificationDiverges,
            facts: whole_loop_effect_facts,
            obligations,

            loan_evidence: empty_checked_loan_evidence_sequence(),
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
        None,
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
        None,
    )
}

/// Collects every declaration's exact lowered goals before outstanding-obligation
/// filtering. Equal or already-known goals retain their declaration positions.
pub(super) fn collect_loop_entry_goals(
    state: &CState,
    checks: &[CLoopInvariantCheck],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    declarations: &mut [Vec<ProofObligation>],
) -> ExecutionResult<Vec<ProofObligation>> {
    collect_invariant_check_obligations_with_mode(
        state,
        state,
        checks,
        InvariantPhase::Entry,
        assumptions,
        budget,
        true,
        Some(declarations),
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
    mut declarations: Option<&mut [Vec<ProofObligation>]>,
) -> ExecutionResult<Vec<ProofObligation>> {
    // Each context carries, beside its facts and obligations, the guards a
    // later declaration is wrapped with: the same list position for position,
    // except that an earlier declaration's own entry is its lowered
    // proposition rather than the member that proposition was wrapped into.
    // The member's guards are a prefix of every later member's guards, so the
    // bare proposition is equivalent there, and guarding with the wrapped
    // member instead would nest every earlier member inside every later one,
    // doubling the bundle with each declaration.
    let mut contexts = vec![(Vec::new(), Vec::new(), Vec::<ProofObligation>::new())];
    let mut all_obligations = Vec::new();
    for (declaration_index, check) in invariant_checks.iter().enumerate() {
        let mut next_contexts = Vec::new();
        for (facts, obligations, guards) in contexts {
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
                // `merge` keeps the earlier obligations as a prefix and
                // appends this path's own; those are their own guards.
                let mut guards = guards.clone();
                guards.extend(obligations.iter().skip(guards.len()).cloned());
                let obligation_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                // The guards this wrap inserts, then the head chain the
                // invariant's own lowering recorded: one record for the
                // obligation proposition, produced by the same wrap that
                // built it, so a consumer introducing its head never pairs
                // a hidden guard with a written connective.
                let (proposition, guard_introductions) =
                    wrap_path_context_with_introductions(path.proposition.clone(), &facts, &guards);
                let mut introductions = guard_introductions;
                introductions.extend(path.introductions.iter().cloned());
                let introductions = std::sync::Arc::new(introductions);
                if let Some(declarations) = declarations.as_deref_mut() {
                    let mut goal = ProofObligation::new(proposition.clone())
                        .with_shared_introductions(Some(&introductions));
                    if let Some(context) = invariant_context(check, phase) {
                        goal = goal.with_context(context);
                    }
                    declarations[declaration_index].push(goal);
                }
                let before = obligations.len();
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
                if obligations.len() > before {
                    guards.push(ProofObligation::new(path.proposition));
                }
                next_contexts.push((facts, obligations, guards));
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
///
/// A measure that reads memory has each read evaluated at both states by the
/// expression evaluator, under `assumptions`, as an invariant about the same
/// cell is. What those reads owe, their loadability, comes first and only
/// where it is not already an exact fact, so a measure over locals alone, or
/// over cells the context already shows loadable, has exactly the members
/// above.
pub(super) fn collect_loop_ranking_obligations(
    state: &CState,
    iteration_entry_state: &CState,
    ranking_measures: &[CRankingComponent],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Result<Vec<ProofObligation>, String> {
    if ranking_measures.is_empty() {
        return Ok(Vec::new());
    }
    let mut reader = crate::kernel::termination::CRankingMeasureReader {
        assumptions,
        budget,
        reads: Default::default(),
    };
    let mut pre = Vec::with_capacity(ranking_measures.len());
    let mut post = Vec::with_capacity(ranking_measures.len());
    for measure in ranking_measures {
        pre.push(crate::kernel::termination::c_ranking_measure_term(
            measure,
            iteration_entry_state,
            &mut reader,
        )?);
        post.push(crate::kernel::termination::c_ranking_measure_term(
            measure,
            state,
            &mut reader,
        )?);
    }
    let reads = reader.reads;
    let read_assumptions = assumptions_with_path_context(assumptions, &reads.facts, &[]);
    let mut obligations = Vec::with_capacity(ranking_measures.len() + 1);
    for obligation in &reads.obligations {
        add_required_proof_obligation_without_search(
            &mut obligations,
            &read_assumptions,
            obligation.proposition().clone(),
            Some("a loop ranking measure's read is viewable"),
            None,
        );
    }
    for (measure, post) in ranking_measures.iter().zip(post.iter()) {
        obligations.push(
            ProofObligation::verification_condition(
                crate::kernel::termination::ranking_nonnegative_proposition(post),
            )
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
    // A pivot arm compares one component's two readings, never two different
    // components, so a tuple whose components chose different carriers needs
    // no coercion: each arm is built in its own component's carrier.
    let arm = |pivot: usize| -> Result<Proposition, String> {
        let strict = crate::kernel::termination::ranking_decrease_proposition(
            &post[pivot],
            &pre[pivot],
            &ranking_measures[pivot],
        )?;
        (0..pivot).rev().try_fold(strict, |rest, index| {
            Ok(Proposition::And(
                Box::new(crate::kernel::termination::ranking_tie_proposition(
                    &post[index],
                    &pre[index],
                    &ranking_measures[index],
                )?),
                Box::new(rest),
            ))
        })
    };
    let decrease = (0..ranking_measures.len())
        .rev()
        .try_fold(None, |rest: Option<Proposition>, pivot| {
            Ok::<_, String>(match rest {
                None => Some(arm(pivot)?),
                Some(rest) => Some(Proposition::Or(Box::new(arm(pivot)?), Box::new(rest))),
            })
        })?
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
    ranking_measures: &[CRankingComponent],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Vec<ProofObligation> {
    match collect_loop_ranking_obligations(
        state,
        iteration_entry_state,
        ranking_measures,
        assumptions,
        budget,
    ) {
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
    /// The body paths that left through `break`, as exits at the states they
    /// reached. The rule joins them with the guard-false exit exactly as it
    /// joins the ones a checked preservation proof reports.
    pub(super) break_exits: Vec<CLoopBreakExit>,
}

pub(super) fn collect_loop_preservation_summary(
    loop_entry_state: &CState,
    head: &CLoopHead,
    condition: &CExpression,
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    resource_specs: &[CResourceSpec],
    ranking_measures: &[CRankingComponent],
    structural_measure: Option<&str>,
    composite_resource_definitions: &[CCompositeResourceDefinition],
    whole_loop_effect_summaries: &[Proposition],
    body: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    do_while: bool,
    backedge_target: Option<CControlTargetId>,
    natural_exit_target: Option<CControlTargetId>,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<LoopPreservationSummary> {
    let mut obligations = Vec::new();
    let mut final_exit_paths = Vec::new();
    let mut break_exits = Vec::new();
    // The body executes from the loop's own resource context; everything the
    // enclosing frame withheld is returned on the way out.
    let top_state = &head.body;
    let body_declared = scope_declared_names(body);
    let binders = c_loop_binders(resource_specs);
    let whole_loop_effect_facts = whole_loop_effect_summaries
        .iter()
        .cloned()
        .map(ExecutionPureFact::new)
        .collect::<Vec<_>>();
    for (invariant_facts, invariant_obligations, _) in assume_invariant_checks(
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
                composite_resource_definitions,
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
            // The body is a scope: the objects the summarized iteration
            // declares stop existing at the back edge and at every exit.
            for body_path in paths_after_scope_exit(
                execute_c_statement_verification_paths_with_prefix(
                    top_state,
                    body,
                    assumptions,
                    environment,
                    execution_semantics,
                    &condition_facts,
                    &condition_obligations,
                    budget,
                    variables,
                )?,
                &body_declared,
            ) {
                let outcome = body_path.outcome;
                let natural_backedge = matches!(
                    &outcome,
                    CStatementOutcome::Jump { target, .. }
                        if backedge_target == Some(*target)
                );
                if matches!(
                    &outcome,
                    CStatementOutcome::Normal(_) | CStatementOutcome::Continue(_)
                ) || natural_backedge
                {
                    let next_state = match outcome {
                        CStatementOutcome::Normal(state)
                        | CStatementOutcome::Continue(state)
                        | CStatementOutcome::Jump { state, .. } => state,
                        _ => unreachable!("classified loop back edge has another outcome"),
                    };
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
                    let (next_state, binder_failure) = match c_loop_state_with_loop_binders_rebound(
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
                        composite_resource_definitions,
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
                                &path_assumptions,
                                budget,
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
                                loop_invariant_correspondence: Default::default(),
                                outcome: CStatementOutcome::Normal(
                                    head.restored_exit_state(&next_state),
                                ),
                                facts: final_path_facts,
                                obligations: final_obligations,
                                loan_evidence: body_path.loan_evidence.clone(),
                            });
                        }
                    }
                } else {
                    match outcome {
                        CStatementOutcome::Break(next_state) => {
                            // A `break` is an exit: the invariants are not
                            // closed on it and no measure is required to
                            // decrease on it. What the body wrote on the way
                            // out is still checked against the loop's declared
                            // effects, and the path itself becomes one of the
                            // exits the rule joins into the loop's successor.
                            let effect_obligations = collect_loop_effect_check_obligations(
                                top_state,
                                &next_state,
                                effect_checks,
                                &body_path.facts,
                                &body_path.obligations,
                                assumptions,
                                budget,
                            )?;
                            let exit_facts = body_path.facts;
                            let exit_obligations = body_path.obligations;
                            let loan_evidence = body_path.loan_evidence;
                            append_required_proof_obligations(
                                &mut obligations,
                                assumptions,
                                &exit_obligations,
                            );
                            append_required_proof_obligations_under_path_context(
                                &mut obligations,
                                assumptions,
                                &effect_obligations,
                                &exit_facts,
                                &exit_obligations,
                            );
                            break_exits.push(
                                CLoopBreakExit::new(
                                    next_state,
                                    exit_facts
                                        .iter()
                                        .map(|fact| fact.proposition().clone())
                                        .collect(),
                                )
                                .with_loan_evidence(loan_evidence),
                            );
                        }
                        CStatementOutcome::Return { value, state } if backedge_target.is_some() => {
                            let effect_obligations = collect_loop_effect_check_obligations(
                                top_state,
                                &state,
                                effect_checks,
                                &body_path.facts,
                                &body_path.obligations,
                                assumptions,
                                budget,
                            )?;
                            let exit_facts = body_path.facts;
                            let exit_obligations = body_path.obligations;
                            let mut final_obligations = exit_obligations.clone();
                            append_required_proof_obligations_under_path_context(
                                &mut final_obligations,
                                assumptions,
                                &effect_obligations,
                                &exit_facts,
                                &exit_obligations,
                            );
                            final_exit_paths.push(CStatementExecutionPath {
                                loop_invariant_correspondence: Default::default(),
                                outcome: CStatementOutcome::Return {
                                    value,
                                    state: head.restored_exit_state(&state),
                                },
                                facts: exit_facts,
                                obligations: final_obligations,
                                loan_evidence: body_path.loan_evidence,
                            });
                        }
                        CStatementOutcome::Jump { target, state }
                            if natural_exit_target == Some(target) =>
                        {
                            let effect_obligations = collect_loop_effect_check_obligations(
                                top_state,
                                &state,
                                effect_checks,
                                &body_path.facts,
                                &body_path.obligations,
                                assumptions,
                                budget,
                            )?;
                            let exit_facts = body_path.facts;
                            let exit_obligations = body_path.obligations;
                            let mut final_obligations = exit_obligations.clone();
                            append_required_proof_obligations_under_path_context(
                                &mut final_obligations,
                                assumptions,
                                &effect_obligations,
                                &exit_facts,
                                &exit_obligations,
                            );
                            final_exit_paths.push(CStatementExecutionPath {
                                loop_invariant_correspondence: Default::default(),
                                outcome: CStatementOutcome::Jump {
                                    target,
                                    state: head.restored_exit_state(&state),
                                },
                                facts: exit_facts,
                                obligations: final_obligations,
                                loan_evidence: body_path.loan_evidence,
                            });
                        }
                        CStatementOutcome::Return { .. }
                        | CStatementOutcome::Normal(_)
                        | CStatementOutcome::Continue(_)
                        | CStatementOutcome::Throw { .. }
                        | CStatementOutcome::Jump { .. }
                        | CStatementOutcome::VerificationDiverges
                        | CStatementOutcome::UndefinedBehavior(_)
                        | CStatementOutcome::RuntimeError(_) => {
                            let mut path_obligations = body_path.obligations;
                            path_obligations.push(
                                ProofObligation::verification_condition(
                                    false_equals_true_proposition(),
                                )
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
    }
    Ok(LoopPreservationSummary {
        obligations,
        final_exit_paths,
        break_exits,
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
                if matches!(
                    check.origin(),
                    CLoopEffectOrigin::InheritedResourceDerived
                        | CLoopEffectOrigin::DeclaredResource
                ) {
                    // A resource-derived frame carries no segments of its
                    // own: it is authoritative only once the checked entry
                    // transition (for an inherited frame) or the loop's
                    // entry evaluation (for a declared one) has installed
                    // fixed ranges.
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
    /// The loop's effect checks with every declared-resource frame installed
    /// from the checked evaluation of the loop's own resource specs at entry.
    /// Every later check of this loop reads these, never the originals.
    pub(super) effect_checks: Vec<CLoopEffectCheck>,
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

/// Installs a loop's declared-resource frame from the kernel's own reading
/// of the loop's resource specs at entry: each owned spec evaluated against
/// the entering context, expanded through the composite definitions, and
/// its owned ranges canonicalized, the same derivation a function's
/// resource-derived frame gets. A check that already carries validated
/// ranges keeps them. When the specs do not evaluate, the checks stay
/// uninstalled and the loop's declaration failure is the verdict; the
/// declared frame then fails closed like an inherited one.
fn install_declared_loop_frames(
    entry_state: &CState,
    effect_checks: &[CLoopEffectCheck],
    resource_specs: &[CResourceSpec],
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CLoopEffectCheck>> {
    if !effect_checks.iter().any(|check| {
        check.origin() == CLoopEffectOrigin::DeclaredResource && check.validated_ranges().is_none()
    }) {
        return Ok(effect_checks.to_vec());
    }
    let Ok((_, checked)) = super::functions::evaluate_function_resource_context_with_metadata(
        entry_state,
        resource_specs,
        definitions,
        assumptions,
        budget,
    )?
    else {
        return Ok(effect_checks.to_vec());
    };
    let mut ranges = BTreeSet::new();
    for fact in checked.iter().filter(|checked| checked.fact.is_own()) {
        crate::instrumentation::record_deterministic_work(1);
        let Some(expanded) = super::functions::checked_owned_memory_ranges(
            &fact.fact,
            definitions,
            entry_state,
            assumptions,
        ) else {
            return Ok(effect_checks.to_vec());
        };
        ranges.extend(expanded);
    }
    let ranges = ranges.into_iter().collect::<Vec<_>>();
    Ok(effect_checks
        .iter()
        .map(|check| {
            if check.origin() == CLoopEffectOrigin::DeclaredResource
                && check.validated_ranges().is_none()
            {
                check.clone().with_validated_ranges(ranges.clone())
            } else {
                check.clone()
            }
        })
        .collect())
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
    let effect_checks = install_declared_loop_frames(
        entry_state,
        effect_checks,
        resource_specs,
        definitions,
        assumptions,
        budget,
    )?;
    let include_mutable_summaries = statement_may_write_memory(entry_state, body);
    let (effect_ranges, all_ranges_evaluable) = evaluate_whole_loop_effect_ranges(
        entry_state,
        &effect_checks,
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
    // The stable-loan barrier is checked below, after the loop's declared
    // ownership. A loop that declares a resource the function does not hold
    // also derives its havoc footprint from that bad declaration, so running
    // the barrier first would report the overlap it caused instead of the
    // ownership violation that is the real error.
    let havoc_loan_failure = entry_state
        .loan_ledger()
        .filter(|_| statement_may_write_memory(entry_state, body))
        .and_then(|ledger| {
            // An unevaluable declared write set is not yet unknown: a loop
            // body can only write memory the enclosing function owns, so the
            // checked owned entry footprint is a sound upper bound on what
            // the head abstraction erases. Only when that footprint cannot be
            // named either does the write set stay unknown and fail closed.
            let validated = loop_havoc_ranges
                .clone()
                .or_else(|| checked_owned_entry_footprint(entry_state.resources()));
            validate_loop_havoc_stable_loans(ledger, validated.as_deref(), assumptions).err()
        });
    let mut resource_failures = Vec::new();
    let mut top_state = havoc_loop_modified_locals(
        entry_state,
        body,
        variables,
        budget,
        loop_havoc_ranges.as_deref(),
    )?;
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
    let (entry_state, head_state, top_state, mut rebound_failures) =
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
                    variables,
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
    // A declaring loop's body does not hold the frame's iterated ownership
    // facts, so a guard cell it writes escapes the store rule; the frame
    // loses any fact whose guard cells the loop may write.
    let top_state = if resource_specs.is_empty() {
        top_state
    } else {
        super::iterated::frame_out_iterated_facts_written_by_loop(
            top_state,
            loop_havoc_ranges.as_deref(),
        )
    };
    resource_failures.append(&mut rebound_failures);
    resource_failures.extend(body_failures);
    resource_failures.extend(havoc_loan_failure);
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
        effect_checks,
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
    let [(facts, obligations, _)] = contexts.as_slice() else {
        return Ok(state.clone());
    };
    let head_assumptions = assumptions_with_path_context(assumptions, facts, obligations);
    let views = crate::kernel::publish_instance_arms(
        state.resources(),
        definitions,
        state,
        &head_assumptions,
    )
    .views;
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
    // Rebuilding a loop body context can allocate fresh resource occurrences.
    // If one denotes an inherited stable view, carry its exact checked
    // binding to the new occurrence instead of rediscovering it from the
    // ambient ledger at a later call boundary.
    let mut body_bindings = top_state.loan_view_bindings().clone();
    for fact in body_resources.facts().iter().filter(|fact| fact.is_view()) {
        let Some(binding) = entry_state
            .resources()
            .view_occurrences_for_fact(fact, assumptions)
            .into_iter()
            .find_map(|occurrence| entry_state.loan_view_bindings().get(&occurrence).cloned())
        else {
            continue;
        };
        if let Some(occurrence) = body_resources
            .view_occurrences_for_fact(fact, assumptions)
            .into_iter()
            .find(|occurrence| body_bindings.get(occurrence).is_none())
        {
            body_bindings = body_bindings.with_inserted(occurrence, binding);
        }
    }
    Ok((
        top_state
            .clone()
            .with_resource_context(body_resources)
            .with_loan_view_bindings(body_bindings),
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
            let mut budget = ExecutionBudget::beside_live_state();
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
/// The instance the binder ends holding must be a strict contained descendant,
/// in the exact resource definitions, of the instance it held at the loop head:
/// the loop head's model selects one arm, that arm names its children, and the
/// back-edge instance is one of them, or one of *their* children by the same
/// rule again, with the submodel that child carries. A model is a finite
/// inductive term, so a strictly deeper submodel at every back edge is
/// well-founded; no counter, size function, or automatic unfolding takes part.
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
    let AlgebraicTermNode::Constructor { variant, .. } = &constructor.node else {
        return Some(format!(
            "loop `decreases {measure}` selected a non-constructor model"
        ));
    };
    if body.arms.iter().all(|arm| &arm.variant != variant) {
        return Some(format!(
            "loop `decreases {measure}` selected the unknown constructor `{variant}`"
        ));
    }
    let mut seen = BTreeSet::new();
    if let AlgebraicTermNode::Variable(variable) = &model.node {
        seen.insert(*variable);
    }
    if structural_measure_reaches_instance(
        &constructor,
        definition,
        next,
        definitions,
        assumptions,
        &mut seen,
    ) {
        return None;
    }
    Some(format!(
        "loop `decreases {measure}` does not descend: the `{}` the binder holds at the back edge is not a contained child of the `{}` it held at the loop head, through the arms this path decided, starting at the `{variant}` arm of `{}`",
        next.name, head.name, head.name
    ))
}

/// Whether the back-edge instance is a contained child of this arm, or of a
/// child of it that the path has likewise decided.
///
/// A direct child is one step of this walk. The uncle-red case of
/// `__rb_insert` sets `node = gparent`, so the frame it hands to the next
/// iteration is `up.up`, two frames above the one the binder held — and the
/// body unfolded each frame it passed, which is exactly what decides that
/// frame's constructor here. The walk follows the evidence the body already
/// produced: it descends only into a child whose own constructor a premise
/// names, and stops the moment one is undecided. It never proves by cases,
/// never searches the resource context, and never unfolds anything itself, so
/// its cost is the constructors this path spelled out.
///
/// `seen` closes the walk over model variables: a premise set that equated a
/// variable with a term mentioning it cannot make this spin.
fn structural_measure_reaches_instance(
    constructor: &AlgebraicTerm,
    definition: &CCompositeResourceDefinition,
    next: &ResourceInstance,
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    seen: &mut BTreeSet<Variable>,
) -> bool {
    let Some(body) = definition.matched.as_ref() else {
        return false;
    };
    let AlgebraicTermNode::Constructor { variant, fields } = &constructor.node else {
        return false;
    };
    let Some(arm) = body.arms.iter().find(|arm| &arm.variant == variant) else {
        return false;
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
            .and_then(|source| match source {
                CResourceChildField::Constructor(index) => fields.get(*index),
                CResourceChildField::Parent(_) => None,
            })
        else {
            continue;
        };
        let Some(held) = next.fields.get(child_body.field_index) else {
            continue;
        };
        if crate::kernel::resource_arguments_proven_equal(held, submodel, assumptions) {
            return true;
        }
        let AlgebraicValue::Algebraic(submodel) = submodel else {
            continue;
        };
        if let AlgebraicTermNode::Variable(variable) = &submodel.node
            && !seen.insert(*variable)
        {
            continue;
        }
        let Some(ResourceModelArmSelection::Constructor(child_constructor)) =
            crate::kernel::select_resource_model_arm(submodel, assumptions)
        else {
            continue;
        };
        if structural_measure_reaches_instance(
            &child_constructor,
            child_definition,
            next,
            definitions,
            assumptions,
            seen,
        ) {
            return true;
        }
    }
    false
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
    variables: &mut KernelVariableGenerator,
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
        let fields = crate::kernel::functions::fresh_resource_instance_fields(
            &instance.schema,
            crate::kernel::functions::ModelFieldMintSite {
                identity,
                minted_by: &crate::kernel::model_fields::ModelMint::LoopHead,
            },
            variables,
            budget,
        )?;
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
        CResourceFact::Own(
            CResource::Token { .. } | CResource::Instance(_) | CResource::Iterated(_),
            _,
        ) => None,
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
        .map(|pointer| {
            let bytes = after_state
                .memory()
                .known_value(&pointer)
                .or_else(|| before_state.memory().known_value(&pointer))
                .map_or_else(
                    crate::kernel::resource_tracker::widest_scalar_access_bytes,
                    |value| value.byte_width(),
                );
            (pointer, bytes)
        })
        .collect::<BTreeMap<_, _>>();
    for (pointer, bytes) in facts
        .iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::CMemoryMutatesOnly { writes, .. } => Some(writes.as_slice()),
            _ => None,
        })
        .flatten()
    {
        writes
            .entry(pointer.clone())
            .and_modify(|known| *known = (*known).max(*bytes))
            .or_insert(*bytes);
    }
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
                } else if matches!(
                    check.origin(),
                    CLoopEffectOrigin::InheritedResourceDerived
                        | CLoopEffectOrigin::DeclaredResource
                ) {
                    segment_evaluation_failed = true;
                    push_false_loop_effect_obligation(
                        &mut obligations,
                        loop_effect_failure_context(
                            check,
                            "resource-derived loop frame was not established from the checked entry transition".to_string(),
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

        for (pointer, bytes) in &writes {
            if !segments.iter().any(|segment| {
                loop_effect_segment_contains_pointer(
                    segment,
                    pointer,
                    *bytes,
                    &effective_assumptions,
                )
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
        CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead) => {
            Ok(Err(format!(
                "{label} could not establish that the memory location contains an initialized value"
            )))
        }
        CExpressionOutcome::UndefinedBehavior(undefined_behavior) => Ok(Err(format!(
            "{label} produced undefined behavior: {}",
            undefined_behavior.description()
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
    bytes: u32,
    assumptions: &PureFactContext,
) -> bool {
    assumptions.pointer_access_in_range(
        pointer,
        bytes,
        &segment.base,
        &segment.start,
        &segment.end,
        segment.element_width,
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
) -> ExecutionResult<
    Vec<(
        Vec<ExecutionPureFact>,
        Vec<ProofObligation>,
        crate::kernel::proof::PersistentSequence<Proposition>,
    )>,
> {
    // Each lowering path forks this declaration history. Keep its prefix
    // persistent so a loop with many explicit invariants does not clone the
    // whole preceding clause vector at every declaration.
    let mut contexts = vec![(
        prefix_facts.to_vec(),
        prefix_obligations.to_vec(),
        crate::kernel::proof::PersistentSequence::default(),
    )];
    for check in invariant_checks {
        let mut next_contexts = Vec::new();
        for (facts, obligations, invariant_propositions) in contexts {
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
                let mut invariant_propositions = invariant_propositions.clone();
                invariant_propositions.push(path.proposition.clone());
                if assumptions.proves_exact(&path.proposition)
                    || facts
                        .iter()
                        .any(|fact| fact.proposition() == &path.proposition)
                {
                    if !facts
                        .iter()
                        .any(|fact| fact.proposition() == &path.proposition)
                    {
                        facts.push(ExecutionPureFact::new(path.proposition));
                    }
                    next_contexts.push((facts, obligations, invariant_propositions));
                } else if add_path_fact(&mut facts, assumptions, path.proposition).is_some() {
                    next_contexts.push((facts, obligations, invariant_propositions));
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
///
/// A guard that could not be evaluated is evaluated once more conjunct by
/// conjunct, because a short-circuit guard's later conjunct is read under the
/// truth of its earlier ones and that prefix may publish read authority (D7,
/// extended to the arms a prefix leaves possible). `parent != 0 &&
/// node == parent->rb_right` is the shape: the first conjunct refutes the
/// folded frame's `Top` arm, the `Left` and `Right` arms both own
/// `parent->rb_right`, and the second conjunct reads it. The second pass costs
/// one more evaluation of a guard that already failed, and it changes nothing
/// for a guard the ordinary evaluation decided.
pub(super) fn assume_condition_branches(
    state: &CState,
    condition: &CExpression,
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    prefix_facts: &[ExecutionPureFact],
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CConditionAssumption>> {
    let branches = assume_condition_branches_at_state(
        state,
        condition,
        assumptions,
        prefix_facts,
        prefix_obligations,
        budget,
    )?;
    if definitions.is_empty()
        || branches
            .iter()
            .all(|branch| branch.undecided_outcome().is_none())
    {
        return Ok(branches);
    }
    let mut conjuncts = Vec::new();
    guard_conjuncts(condition, &mut conjuncts);
    if conjuncts.len() < 2 {
        return Ok(branches);
    }
    assume_guard_conjunct_branches(
        state,
        &conjuncts,
        definitions,
        assumptions,
        prefix_facts,
        prefix_obligations,
        budget,
    )
}

/// The top-level conjuncts of a short-circuit guard, left to right.
///
/// `a && b && c` is one guard with three exit paths and three reading
/// positions; anything else is one conjunct, evaluated exactly as it is.
fn guard_conjuncts<'a>(condition: &'a CExpression, conjuncts: &mut Vec<&'a CExpression>) {
    match condition {
        CExpression::And(left, right) => {
            guard_conjuncts(left, conjuncts);
            guard_conjuncts(right, conjuncts);
        }
        _ => conjuncts.push(condition),
    }
}

/// Every way a short-circuit guard can leave `state`, evaluating conjunct `k`
/// under the truth of conjuncts `1..k-1` and under the read authority those
/// truths publish.
///
/// The C is unchanged: the guard is false as soon as one conjunct is false,
/// true when the last one is, and undecided wherever a conjunct produced no
/// value — which is the refusal S1 installed, kept here. What the second pass
/// adds is where each conjunct is read: a folded matched instance publishes the
/// cells every arm the prefix leaves possible owns, so a conjunct may read what
/// an earlier conjunct unlocked and nothing more.
///
/// Cost is one evaluation of each conjunct per live prefix, plus one arm-view
/// publication per conjunct: the arms of the instances held, evaluated once
/// each. No conjunct is revisited and no prefix is searched over.
fn assume_guard_conjunct_branches(
    state: &CState,
    conjuncts: &[&CExpression],
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    prefix_facts: &[ExecutionPureFact],
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CConditionAssumption>> {
    let mut branches = Vec::new();
    let mut live = vec![(prefix_facts.to_vec(), prefix_obligations.to_vec())];
    for (index, conjunct) in conjuncts.iter().enumerate() {
        let is_last = index + 1 == conjuncts.len();
        let mut next = Vec::new();
        for (facts, obligations) in live {
            let conjunct_state =
                with_guard_prefix_arm_views(state, definitions, assumptions, &facts, &obligations);
            for assumption in assume_condition_branches_at_state(
                &conjunct_state,
                conjunct,
                assumptions,
                &facts,
                &obligations,
                budget,
            )? {
                match assumption.branch {
                    // A true conjunct that is not the last decides nothing on
                    // its own; it is the premise the next one is read under.
                    CConditionBranch::Decided(true) if !is_last => {
                        next.push((assumption.facts, assumption.obligations));
                    }
                    _ => branches.push(assumption),
                }
            }
        }
        live = next;
    }
    budget.check_path_width(branches.len())?;
    Ok(branches)
}

/// `state` with the cells published that every arm the guard prefix in `facts`
/// leaves possible owns (D7).
///
/// The prefix's own conclusion comes first: a conjunct that contradicts an
/// arm's binding-free fact refutes that arm, which is the same refutation rule
/// the loop head, the back edge, and the exit already apply, and it is what
/// leaves a set of possible arms rather than a decided one. Ownership is
/// untouched; only read authority is published, and only for a cell every
/// possible arm owns.
fn with_guard_prefix_arm_views(
    state: &CState,
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    facts: &[ExecutionPureFact],
    obligations: &[ProofObligation],
) -> CState {
    let prefix_assumptions = assumptions_with_path_context(assumptions, facts, obligations);
    let views = crate::kernel::publish_instance_arms(
        state.resources(),
        definitions,
        state,
        &prefix_assumptions,
    )
    .views;
    if views.is_empty() {
        return state.clone();
    }
    state
        .clone()
        .with_resource_context(state.resources().clone().unchecked_with_facts(views))
}

/// One evaluation of a whole guard at one state.
fn assume_condition_branches_at_state(
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
        evaluate_c_condition_paths(state, condition, &effective_assumptions, budget)?
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
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    prefix_facts: &[ExecutionPureFact],
    prefix_obligations: &[ProofObligation],
    desired_truthiness: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CConditionAssumption>> {
    Ok(assume_condition_branches(
        state,
        condition,
        definitions,
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
    budget: &mut ExecutionBudget,
    mutable_ranges: Option<&[CMemoryRange]>,
) -> ExecutionResult<CState> {
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
        let Some(value) = fresh_loop_local_value(c_type, variables, budget)? else {
            continue;
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
        // Cells under an active stable-view loan are stable across the loop
        // by the loan itself; erasing them would only lose loan-supported
        // framing, never authority.
        let havoced_memory = state
            .memory
            .clone()
            .with_loop_memory_havoc_preserving_loans(
                variables.next_in(budget)?,
                &preserved_blocks,
                mutable_ranges,
                state.loan_ledger(),
            );
        state.set_memory(havoced_memory);
    }
    Ok(state)
}

/// The memory the enclosing function owns where the loop is entered.
///
/// A loop body can only write memory the function owns, so this is a checked
/// upper bound on the bytes the head abstraction may erase, usable as the
/// validated ranges when the loop's own declared write set did not evaluate.
/// `None` means the footprint itself is unknown: some owned fact names memory
/// this level cannot enumerate -- a folded composite, an instance, or a token
/// -- and the caller must keep failing closed rather than guess a smaller set.
fn checked_owned_entry_footprint(resources: &ResourceContext) -> Option<Vec<CMemoryRange>> {
    resources
        .facts()
        .iter()
        .filter(|fact| fact.is_own())
        .map(|fact| fact.memory_own_range().cloned())
        .collect()
}

/// Check the write set that the loop-head abstraction is about to erase
/// against the active stable-view footprint.  An unknown write set is a
/// barrier: silently turning it into a fresh snapshot would discard the only
/// evidence that a loan protects its bytes.
fn validate_loop_havoc_stable_loans(
    ledger: &super::loans::LoanLedger,
    mutable_ranges: Option<&[CMemoryRange]>,
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let Some(ranges) = mutable_ranges else {
        if ledger.has_active_memory_loans() {
            return Err(
                "loop memory havoc has no checked write set while a stable-view loan is active"
                    .to_string(),
            );
        }
        return Ok(());
    };
    for range in ranges {
        if let Err(error) = ledger.permits_memory_access_with_assumptions(range, assumptions) {
            return Err(format!(
                "loop memory havoc overlaps an active stable-view loan: {error:?}"
            ));
        }
    }
    Ok(())
}

pub(super) fn statement_may_write_memory(state: &CState, statement: &CStatement) -> bool {
    match statement {
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assert { .. }
        | CStatement::Throw(_)
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
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            statement_may_write_memory(state, try_body)
                || statement_may_write_memory(state, handler)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            statement_may_write_memory(state, then_branch)
                || statement_may_write_memory(state, else_branch)
        }
        CStatement::ForStep { step, .. } => statement_may_write_memory(state, step),
        CStatement::While { body, .. } => statement_may_write_memory(state, body),
        CStatement::Switch { cases, .. } => cases
            .iter()
            .any(|case| statement_may_write_memory(state, &case.body)),
    }
}

#[cfg(test)]
mod v10_tests {
    use super::*;

    fn memory_range(base: u32, end: u32) -> CMemoryRange {
        CMemoryRange::new(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            },
            Bitvector32Term::Constant(base),
            Bitvector32Term::Constant(end),
        )
    }

    #[test]
    fn loop_havoc_requires_a_checked_set_disjoint_from_active_loans() {
        let escrow = CResourceFact::own_memory(memory_range(0, 1));
        let support = ResourceContext::new()
            .unchecked_with_fact(escrow.clone())
            .unique_owned_occurrence_for_fact(&escrow)
            .expect("the test escrow has one backing occurrence")
            .0;
        let ledger = super::super::loans::LoanLedger::new();
        let owner = ledger.fresh_participant().unwrap();
        let opening = ledger.lend(owner, owner, support, escrow).unwrap();
        let ledger = ledger.apply(&opening.transition).unwrap();

        let assumptions = PureFactContext::new();
        assert!(validate_loop_havoc_stable_loans(&ledger, None, &assumptions).is_err());
        assert!(
            validate_loop_havoc_stable_loans(&ledger, Some(&[memory_range(0, 1)]), &assumptions)
                .is_err()
        );
        assert!(
            validate_loop_havoc_stable_loans(&ledger, Some(&[memory_range(2, 3)]), &assumptions)
                .is_ok()
        );
    }

    #[test]
    fn owned_entry_footprint_names_memory_owners_and_refuses_unnameable_ones() {
        let empty = ResourceContext::new();
        assert_eq!(checked_owned_entry_footprint(&empty), Some(Vec::new()));

        let owned = CResourceFact::own_memory(memory_range(2, 3));
        let viewed = CResourceFact::view_memory(memory_range(0, 1));
        let memory_only = ResourceContext::new()
            .unchecked_with_fact(owned)
            .unchecked_with_fact(viewed);
        // A view lends no write authority, so it is not part of the footprint.
        assert_eq!(
            checked_owned_entry_footprint(&memory_only),
            Some(vec![memory_range(2, 3)])
        );

        // An owned resource whose bytes this level cannot enumerate leaves the
        // write set unknown, so the barrier stays closed rather than shrinking
        // to the memory owners that happen to be nameable.
        let folded = ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own_memory(memory_range(2, 3)))
            .unchecked_with_fact(CResourceFact::own(CResource::Token {
                name: "tokens".to_string(),
                arguments: Vec::new().into(),
            }));
        assert_eq!(checked_owned_entry_footprint(&folded), None);
    }
}

pub(super) fn collect_loop_modified_locals(statement: &CStatement, names: &mut BTreeSet<String>) {
    match statement {
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assert { .. }
        | CStatement::Throw(_)
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
        CStatement::TryCatchInt32 {
            try_body,
            binding,
            handler,
            ..
        } => {
            collect_loop_modified_locals(try_body, names);
            names.insert(binding.clone());
            collect_loop_modified_locals(handler, names);
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_loop_modified_locals(then_branch, names);
            collect_loop_modified_locals(else_branch, names);
        }
        CStatement::ForStep { step, .. } => {
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
        | CStatement::Goto { .. }
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
        CStatement::Return(expression) | CStatement::Throw(expression) => {
            collect_address_taken_in_expression(expression, names)
        }
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
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            collect_address_taken_locals(try_body, names);
            collect_address_taken_locals(handler, names);
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
        CStatement::ForStep { step, .. } => {
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
