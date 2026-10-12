use super::*;

fn read_function(policy: CTypedAccessPolicy) -> CFunction {
    c_function(
        CType::Int32,
        "policy_read",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_load(c_variable("p"))),
    )
    .with_typed_access_policy(policy)
}

#[test]
fn nested_c_body_restores_native_source_policy_and_c_only_rows_remain_c_only() {
    let _session = crate::kernel::VerificationSession::enter();
    let identity = Variable(991_918);
    let pointer = CPointerValue::new(Pointer::symbolic(identity), CType::Int32Pointer)
        .with_designation(PointerDesignation::Unresolved(identity));
    let memory = CMemory::new()
        .with_block(pointer.block.clone(), 4)
        .store(pointer.pointer().clone(), int32(7))
        .with_typed_input_span(
            pointer.clone(),
            CType::Int32,
            IntegerTerm::constant_i64(1).into(),
            CTypedAccessPolicy::CAllocatedAccessAllowed,
        )
        .unwrap();
    let caller = CState::new()
        .with_typed_access_policy(CTypedAccessPolicy::NativeObjectOnly)
        .with_memory(memory)
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::own_memory(CMemoryRange::new(
                pointer.pointer().clone(),
                0u32.into(),
                1u32.into(),
            )),
        ));
    let arguments = [CExpression::Value(CValue::Pointer(pointer.clone()))];
    let execute = |state: &CState, function: &CFunction| {
        execute_c_function_paths(
            state,
            function,
            &arguments,
            &PureFactContext::new(),
            &CExecutionEnvironment::new(),
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::new(),
        )
        .unwrap()
    };
    let c_function = read_function(CTypedAccessPolicy::CAllocatedAccessAllowed);
    let paths = execute(&caller, &c_function);
    let [path] = paths.as_slice() else {
        panic!("one exact C read path");
    };
    let CFunctionOutcome::Return { value, state } = &path.outcome else {
        panic!(
            "the selected C body may use its C-only prefix: {:?}",
            path.outcome
        );
    };
    assert_eq!(value, &int32(7));
    assert_eq!(
        state.typed_access_policy(),
        CTypedAccessPolicy::NativeObjectOnly
    );
    assert_eq!(
        state.memory().native_input_span_policy(&pointer),
        Some(CTypedAccessPolicy::CAllocatedAccessAllowed),
    );
    let native = read_function(CTypedAccessPolicy::NativeObjectOnly);
    assert!(execute(state, &native).iter().all(|path| matches!(
        path.outcome,
        CFunctionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory)
    )));
    let native_entry = bind_c_contract_arguments(
        &caller
            .clone()
            .with_typed_access_policy(CTypedAccessPolicy::CAllocatedAccessAllowed),
        native.contract_interface(),
        &[CValue::Pointer(pointer)],
        None,
    )
    .unwrap();
    assert_eq!(
        native_entry.typed_access_policy(),
        CTypedAccessPolicy::NativeObjectOnly
    );
}

#[test]
fn typed_source_policy_is_checked_interface_and_state_identity() {
    let c = read_function(CTypedAccessPolicy::CAllocatedAccessAllowed);
    let native = read_function(CTypedAccessPolicy::NativeObjectOnly);
    assert_ne!(c.contract_interface(), native.contract_interface());
    assert!(
        !c.contract_interface()
            .exactly_matches(native.contract_interface())
    );
    assert!(
        !c.contract_interface()
            .has_compatible_signature_and_composite_vocabulary(native.contract_interface(),)
    );
    let contract = CFunctionContract::new("NativeRead", native.clone()).unwrap();
    assert!(!contract.exactly_matches(&c));
    assert!(contract.exactly_matches(&native));
    let state = CState::new().with_typed_access_policy(CTypedAccessPolicy::NativeObjectOnly);
    let c_state = CState::new();
    assert_ne!(state, c_state);
    assert!(!state.shares_non_memory_storage_with(&c_state));
    let native_outcome = CFunctionOutcome::Return {
        value: int32(7),
        state: Box::new(state),
    };
    let c_outcome = CFunctionOutcome::Return {
        value: int32(7),
        state: Box::new(c_state),
    };
    assert!(
        !crate::kernel::c_function_outcomes_program_state_definitionally_equal(
            &native_outcome,
            &c_outcome,
            &PureFactContext::new(),
        )
    );
    assert!(
        !crate::kernel::c_function_outcomes_program_state_equal_by_execution_provenance(
            &native_outcome,
            &Vec::<ExecutionPureFact>::new(),
            &c_outcome,
            &Vec::<ExecutionPureFact>::new(),
            &PureFactContext::new(),
        )
    );
}

#[test]
fn native_pure_numeric_function_refines_an_ordinary_named_numeric_contract() {
    let _session = crate::kernel::VerificationSession::enter();
    let numeric_interface = |parameter: &str| {
        c_function(
            CType::Int32,
            "native_numeric_identity",
            vec![c_parameter(parameter, CType::Int32)],
            c_return(c_variable(parameter)),
        )
        .with_contract(
            Vec::new(),
            vec![SpecProposition::Comparison {
                left: SpecExpression::CExpression(c_variable(C_CONTRACT_RESULT_NAME)),
                operator: CComparisonOperator::Equal,
                right: SpecExpression::CExpression(c_variable(parameter)),
            }],
            Vec::new(),
            vec![
                CFunctionContractClaim::body_safety(),
                CFunctionContractClaim::ensure_proposition(0, 0),
            ],
            true,
        )
    };
    let native =
        numeric_interface("x").with_typed_access_policy(CTypedAccessPolicy::NativeObjectOnly);
    let caller = CState::new()
        .with_population_creation_tracking()
        .with_typed_access_policy(CTypedAccessPolicy::NativeObjectOnly);
    let arguments = vec![CExpression::Value(CValue::Int32(
        Bitvector32Term::Variable(Variable(991_919)),
    ))];
    let bound = bind_c_function_arguments_with_assumptions(
        &caller,
        &native,
        &[int32(7)],
        &PureFactContext::new(),
    )
    .unwrap();
    assert_eq!(
        bound.typed_access_policy(),
        CTypedAccessPolicy::NativeObjectOnly
    );
    let semantics = CExecutionSemantics::EXECUTE_BODIES;
    let mode = CFunctionContractExecutionMode::VerifyLoops;
    let checked = crate::kernel::prove_checked_c_function_execution_with_environment(
        caller.clone(),
        native.clone(),
        arguments.clone(),
        PureFactContext::new(),
        CExecutionEnvironment::new(),
        semantics,
        mode,
    );
    let execution = crate::kernel::prove_c_function_contract_execution_paths_with_checked_artifacts(
        caller,
        native.clone(),
        arguments,
        CExecutionEnvironment::new(),
        semantics,
        mode,
        std::slice::from_ref(&checked),
    );
    let claims = crate::kernel::c_verified_function_contract_claims(&native, &execution)
        .expect("the actual native numeric body certifies its unchanged numeric interface");
    let rule = crate::kernel::c_verified_function_rule(native.clone(), &claims)
        .expect("the independently checked native body has a reusable rule");
    let ordinary = CFunctionContract::new("NumericIdentity", numeric_interface("n")).unwrap();
    assert_eq!(
        ordinary.interface().typed_access_policy(),
        CTypedAccessPolicy::CAllocatedAccessAllowed
    );
    assert!(!ordinary.exactly_matches(&native));
    let environment = CExecutionEnvironment::new()
        .with_verified_function_rule(rule)
        .with_function_contract(ordinary);
    let context = crate::kernel::c_function_contract_refinement_context(
        &environment,
        "NumericIdentity",
        native.name(),
    )
    .expect("a pure numeric native body must reach ordinary checked behavioral refinement");
    assert!(crate::kernel::c_function_contract_refinement_obligations(&context).is_some());
    assert!(
        function_refines_named_contract(
            environment
                .get_function_contract("NumericIdentity")
                .unwrap(),
            &native,
            &mut ExecutionBudget::new(),
        )
        .unwrap()
    );
    let false_numeric = CFunctionContract::new(
        "NumericZero",
        numeric_interface("n").with_contract(
            Vec::new(),
            vec![SpecProposition::Comparison {
                left: SpecExpression::CExpression(c_variable(C_CONTRACT_RESULT_NAME)),
                operator: CComparisonOperator::Equal,
                right: SpecExpression::Value(int32(0)),
            }],
            Vec::new(),
            Vec::new(),
            true,
        ),
    )
    .unwrap();
    assert!(
        !function_refines_named_contract(&false_numeric, &native, &mut ExecutionBudget::new(),)
            .unwrap(),
        "source policy compatibility cannot prove a false numeric ensure"
    );
    assert_eq!(
        native.contract_interface().typed_access_policy(),
        CTypedAccessPolicy::NativeObjectOnly
    );
}

#[test]
fn scalar_policy_refinement_does_not_erase_resource_or_memory_requirements() {
    let scalar = c_function(
        CType::Int32,
        "scalar",
        Vec::new(),
        c_return(c_int32_literal(0)),
    );
    let resource = scalar.clone().with_resource_summary(
        vec![CResourceSpec::composite(
            CResourceAccessMode::Own,
            "marker".into(),
            Vec::new(),
            Vec::new(),
        )],
        Vec::new(),
    );
    let memory = scalar.with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::MemoryLoad {
                memory: SpecMemory::Current,
                pointer: Box::new(SpecExpression::Value(CValue::typed_pointer(
                    Pointer::null(),
                    CType::Int32Pointer,
                ))),
                value_type: CType::Int32,
            },
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(0)),
        }],
        Vec::new(),
        Vec::new(),
        true,
    );
    for c in [resource, memory] {
        let native = c
            .clone()
            .with_typed_access_policy(CTypedAccessPolicy::NativeObjectOnly);
        assert!(!typed_access_policy_refinement_compatible(
            c.contract_interface(),
            native.contract_interface()
        ));
        assert!(
            !c.contract_interface()
                .has_compatible_signature_and_composite_vocabulary(native.contract_interface())
        );
        assert!(!native_record_refinement_obligations_match(
            c.contract_interface(),
            native.contract_interface()
        ));
    }
}
