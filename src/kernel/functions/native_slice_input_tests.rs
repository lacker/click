use super::*;

fn function() -> CFunction {
    c_function(
        CType::Void,
        "slice_input",
        vec![
            c_parameter("bytes", CType::UInt8Pointer).with_native_pointer_input(true),
            c_parameter("len", CType::UInt64),
        ],
        c_return(CExpression::Value(CValue::Void)),
    )
    .with_typed_access_policy(CTypedAccessPolicy::NativeObjectOnly)
    .with_native_span_inputs(vec![CNativeSpanInput {
        parameter_index: 0,
        length_parameter_index: 1,
        element_type: CType::UInt8,
    }])
}

fn pointer() -> CPointerValue {
    let identity = Variable(940_890);
    CPointerValue::new(Pointer::symbolic(identity), CType::UInt8Pointer)
        .with_designation(PointerDesignation::Unresolved(identity))
}

fn entry(length: Bitvector32Term) -> (CState, Vec<CValue>) {
    let mut arguments = vec![
        CExpression::Value(CValue::Pointer(pointer())),
        CExpression::Value(CValue::UInt64(length)),
    ];
    let state = assume_scalar_object_inputs(
        CState::new(),
        function().contract_interface(),
        &mut arguments,
    )
    .unwrap();
    let values = arguments
        .into_iter()
        .map(|argument| match argument {
            CExpression::Value(value) => value,
            _ => panic!(),
        })
        .collect();
    (state, values)
}

#[test]
fn source_slice_interface_retains_geometry_without_permission_or_initialization() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = function();
    let ordinary = source.clone().with_native_span_inputs(vec![]);
    assert!(
        !source
            .contract_interface()
            .exactly_matches(ordinary.contract_interface())
    );
    assert!(
        !source
            .contract_interface()
            .has_compatible_signature_and_composite_vocabulary(ordinary.contract_interface())
    );
    let (state, values) = entry(Bitvector32Term::UInt64Constant(8));
    assert_eq!(state.memory().cells.representation_len(), 0);
    assert!(!state.memory().has_block(&pointer().block));
    assert_eq!(state.resources(), CState::new().resources());
    assert!(bind_c_function_arguments(&state, &source, &values).is_some());
    assert!(
        bind_c_contract_arguments(&state, source.contract_interface(), &values, None).is_some()
    );
    let mut raw = values.clone();
    raw[0] = CValue::typed_pointer(pointer().pointer().clone(), CType::UInt8Pointer);
    assert!(bind_c_function_arguments(&state, &source, &raw).is_none());
    let mut longer = values.clone();
    longer[1] = CValue::UInt64(Bitvector32Term::UInt64Constant(9));
    assert!(bind_c_function_arguments(&state, &source, &longer).is_none());
}

#[test]
fn empty_source_slice_allows_only_identity_formation_and_never_access() {
    let _session = crate::kernel::VerificationSession::enter();
    let (state, values) = entry(Bitvector32Term::UInt64Constant(0));
    assert!(bind_c_function_arguments(&state, &function(), &values).is_some());
    let context = PureFactContext::new();
    let checked = |result| {
        matches!(result,
        Ok(crate::kernel::eval::pointer_domains::PointerDomainCheck::Checked(guards))
        if guards.iter().all(|guard| context.decide(guard) == Some(true)))
    };
    let p = pointer();
    use crate::kernel::eval::pointer_domains::*;
    assert!(checked(checked_pointer_formation(
        &state,
        &p,
        p.pointer(),
        1,
        PointerDomainView::Typed,
        &context
    )));
    let shifted = p.pointer().offset_by_bytes(1);
    assert!(!checked(checked_pointer_formation(
        &state,
        &p,
        &shifted,
        1,
        PointerDomainView::Typed,
        &context
    )));
    assert!(!checked(checked_pointer_access(
        &state,
        &p,
        CType::UInt8,
        1,
        PointerDomainView::Typed,
        &context
    )));
    let prefix = CState::new().with_memory(
        CMemory::new()
            .with_native_input_span(p.clone(), CType::UInt8, IntegerTerm::constant_i64(0).into())
            .unwrap(),
    );
    assert!(bind_c_function_arguments(&prefix, &function(), &values).is_none());
}

#[test]
fn source_slice_rejects_unbounded_actual_c_only_span_and_invalid_metadata() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = pointer();
    let count = Bitvector32Term::Variable(Variable(940_891));
    let observed = crate::kernel::eval::pointer_domains::native_count_observation(
        MachineIntegerType::UInt64,
        count.clone(),
    )
    .unwrap();
    let prefix = CState::new().with_memory(
        CMemory::new()
            .with_native_input_span(p.clone(), CType::UInt8, observed.into())
            .unwrap(),
    );
    let values = vec![CValue::Pointer(p.clone()), CValue::UInt64(count)];
    assert!(bind_c_function_arguments(&prefix, &function(), &values).is_none());
    let c_only = CState::new().with_memory(
        CMemory::new()
            .with_typed_input_span(
                p.clone(),
                CType::UInt8,
                IntegerTerm::constant_i64(8).into(),
                CTypedAccessPolicy::CAllocatedAccessAllowed,
            )
            .unwrap(),
    );
    let literal = vec![
        CValue::Pointer(p.clone()),
        CValue::UInt64(Bitvector32Term::UInt64Constant(8)),
    ];
    assert!(bind_c_function_arguments(&c_only, &function(), &literal).is_none());
    assert!(
        CMemory::new()
            .with_native_slice_input(
                p,
                CType::UInt8,
                IntegerTerm::constant(u64::MAX.into()).into()
            )
            .is_err()
    );
    let malformed = function().with_native_span_inputs(vec![CNativeSpanInput {
        parameter_index: 0,
        length_parameter_index: 0,
        element_type: CType::UInt8,
    }]);
    assert!(bind_c_function_arguments(&prefix, &malformed, &values).is_none());
}

#[test]
fn source_slice_metadata_requires_native_interface_policy_at_entry_and_calls() {
    let _session = crate::kernel::VerificationSession::enter();
    let (state, values) = entry(Bitvector32Term::UInt64Constant(8));
    let c_only = function().with_typed_access_policy(CTypedAccessPolicy::CAllocatedAccessAllowed);
    let mut arguments = values
        .iter()
        .cloned()
        .map(CExpression::Value)
        .collect::<Vec<_>>();
    assert!(
        assume_scalar_object_inputs(CState::new(), c_only.contract_interface(), &mut arguments)
            .is_err()
    );
    assert!(bind_c_function_arguments(&state, &c_only, &values).is_none());
    assert!(
        bind_c_contract_arguments(&state, c_only.contract_interface(), &values, None).is_none()
    );
}
