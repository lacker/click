use super::*;

fn prefix(count: u32) -> CResourceSpec {
    CResourceSpec::owned_memory(CMemorySegment::new(
        c_variable("p"),
        c_int32_literal(0),
        c_int32_literal(count),
    ))
    .with_native_span_requirements(vec![CNativeSpanRequirement {
        access_policy: crate::kernel::CTypedAccessPolicy::NativeObjectOnly,
        carrier: c_variable("p"),
        element_type: CType::Int32,
        count: c_int32_literal(count),
    }])
}

fn declared_output(actual: CExpression, count: u32) -> (CFunction, CResourceSpec) {
    let body = prefix(count).with_guard(SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable("p")),
        operator: CComparisonOperator::NotEqual,
        right: SpecExpression::Value(int32(0)),
    });
    let head = CResourceSpec::composite(
        CResourceAccessMode::Own,
        "MaybeRaw".into(),
        vec![actual],
        vec![CType::Int32Pointer],
    );
    let definition = CCompositeResourceDefinition::new(
        "MaybeRaw",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![body.clone()],
        Vec::new(),
    );
    let function = c_function(
        CType::Int32Pointer,
        "acquire_declared_output",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_resource_summary(Vec::new(), vec![head])
    .with_composite_resource_definitions(vec![definition]);
    (function, body)
}

#[test]
fn declared_output_identity_requires_its_exact_result_head_and_selects_no_input() {
    let identity = Variable(9_898_701);
    let (function, _) = declared_output(c_variable(C_CONTRACT_RESULT_NAME), 1);
    let result = symbolic_contract_result(function.contract_interface(), identity);
    let CValue::Pointer(pointer) = &result else {
        panic!("pointer result");
    };
    assert_eq!(pointer.pointer(), &Pointer::symbolic(identity));
    assert_eq!(
        pointer.designation(),
        Some(&PointerDesignation::Unresolved(identity))
    );

    let unprofiled = function
        .clone()
        .with_resource_summary(Vec::new(), Vec::new());
    assert!(
        matches!(symbolic_contract_result(unprofiled.contract_interface(), identity),
        CValue::Pointer(pointer) if pointer.designation().is_none())
    );
    for actual in [
        c_variable("input"),
        CExpression::PointerOffsetBytes {
            pointer: Box::new(c_variable(C_CONTRACT_RESULT_NAME)),
            bytes: 0,
        },
    ] {
        let (function, _) = declared_output(actual, 1);
        assert!(
            matches!(symbolic_contract_result(function.contract_interface(), identity),
            CValue::Pointer(pointer) if pointer.designation().is_none())
        );
    }
    let mut wrong_type = function.contract_interface().clone();
    wrong_type.return_type = CType::UInt32Pointer;
    assert!(matches!(symbolic_contract_result(&wrong_type, identity),
        CValue::Pointer(pointer) if pointer.designation().is_none()));

    let input_identity = Variable(9_898_702);
    let input = CValue::Pointer(
        CPointerValue::new(Pointer::symbolic(input_identity), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(input_identity)),
    );
    let effect = CPointerResultEffect::FromParameter {
        parameter: 0,
        child_path: Default::default(),
    };
    let transported = instantiate_pointer_result_effect(
        result,
        &[effect],
        std::slice::from_ref(&input),
        &CMemory::new(),
    );
    assert!(matches!(transported, CValue::Pointer(pointer)
        if pointer.designation() == Some(&PointerDesignation::Unresolved(input_identity))
            && pointer.pointer() == &Pointer::symbolic(identity)));
    assert!(matches!(input, CValue::Pointer(pointer)
        if pointer.designation() == Some(&PointerDesignation::Unresolved(input_identity))
            && pointer.pointer() == &Pointer::symbolic(input_identity)));
}

#[test]
fn declared_output_identity_admits_only_its_selected_nonempty_body() {
    let _session = crate::kernel::VerificationSession::enter();
    let identity = Variable(9_898_711);
    let (function, body) = declared_output(c_variable(C_CONTRACT_RESULT_NAME), 1);
    let CValue::Pointer(pointer) =
        symbolic_contract_result(function.contract_interface(), identity)
    else {
        panic!("pointer result");
    };
    let state = CState::new().with_local("p", CValue::Pointer(pointer.clone()));
    assert_eq!(state.memory(), &CMemory::new());
    assert!(state.memory().native_input_span(&pointer).is_none());
    let nonnull = PureFactContext::new()
        .assume_condition(pointer_is_null_condition(pointer.pointer().clone()), false);
    let assumed = assume_native_record_specs(&state, std::slice::from_ref(&body), &nonnull)
        .expect("selected declared output body");
    assert!(assumed.memory().native_input_span(&pointer).is_some());
    assert!(assumed.resources().facts().is_empty());
    assert_eq!(assumed.memory().cells.representation_len(), 0);
    assert!(
        !assumed
            .memory()
            .has_initialized_bytes_under(pointer.pointer(), 4, &nonnull)
    );
    assert!(check_native_record_specs(&assumed, std::slice::from_ref(&body), &nonnull).is_ok());

    let null = PureFactContext::new()
        .assume_condition(pointer_is_null_condition(pointer.pointer().clone()), true);
    let inactive = assume_native_record_specs(&state, &[body], &null).unwrap();
    assert_eq!(inactive, state);
    assert!(inactive.memory().native_input_span(&pointer).is_none());
    let (empty_function, empty_body) = declared_output(c_variable(C_CONTRACT_RESULT_NAME), 0);
    let empty_result = symbolic_contract_result(empty_function.contract_interface(), identity);
    assert_eq!(empty_result, CValue::Pointer(pointer));
    let empty = assume_native_record_specs(&state, &[empty_body], &nonnull).unwrap();
    assert_eq!(empty, state);
}
