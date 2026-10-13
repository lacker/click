use super::*;

fn normal(state: CState, statement: CStatement) -> CState {
    let theorem = prove_c_statement_execution(state, statement).unwrap();
    let Proposition::CStatementExecutes {
        outcome: CStatementOutcome::Normal(after),
        ..
    } = theorem.proposition()
    else {
        panic!("{:?}", theorem.proposition());
    };
    *after.clone()
}

fn outcome(state: &CState, expression: CExpression) -> CExpressionOutcome {
    let theorem = prove_c_expression_evaluation(state.clone(), expression).unwrap();
    let Proposition::CExpressionEvaluates { outcome, .. } = theorem.proposition() else {
        unreachable!()
    };
    outcome.clone()
}

fn value(state: &CState, expression: CExpression) -> CValue {
    match outcome(state, expression) {
        CExpressionOutcome::Value(value) => value,
        other => panic!("expected a value: {other:?}"),
    }
}

fn element_address(index: u32) -> CExpression {
    CExpression::AddressOf(Box::new(c_index(
        c_variable("items"),
        c_int32_literal(index),
    )))
}

#[test]
fn wide_address_scalar_address_and_pointer_slot_preserve_type_and_payload() {
    for (ty, pointer_ty, slot_ty, literal) in [
        (
            CType::Int128,
            CType::Int128Pointer,
            CType::Int128PointerPointer,
            c_int128_literal(i128::MIN),
        ),
        (
            CType::UInt128,
            CType::UInt128Pointer,
            CType::UInt128PointerPointer,
            c_uint128_literal(u128::MAX),
        ),
    ] {
        let expected = value(&CState::new(), literal.clone());
        let state = normal(
            CState::new(),
            c_seq(
                c_declare("wide", ty),
                c_seq(
                    c_assign("wide", literal),
                    c_seq(c_declare("p", pointer_ty), c_assign("p", c_addr_of("wide"))),
                ),
            ),
        );
        let pointer = value(&state, c_variable("p"));
        assert_eq!(pointer.c_type(), pointer_ty);
        assert_eq!(pointer.byte_width(), 8);
        assert_eq!(value(&state, c_load(c_variable("p"))), expected);
        let slot = value(&state, c_addr_of("p"));
        assert_eq!(slot.c_type(), slot_ty);
        assert_eq!(
            value(&state, c_typed_load(CExpression::Value(slot), pointer_ty)),
            pointer
        );
        assert_eq!(pointer_ty.pointer_to(), Some(slot_ty));
        assert_eq!(slot_ty.pointer_to(), None);
        assert_eq!(ty.pointer_to(), Some(pointer_ty));
        assert_eq!(ty.abi_alignment(), 16);
        assert_eq!(pointer_ty.abi_alignment(), 8);
        assert_eq!(slot_ty.abi_alignment(), 8);
        let other = if ty == CType::Int128 {
            CType::UInt128Pointer
        } else {
            CType::Int128Pointer
        };
        assert!(!other.accepts(&pointer));
        assert!(CType::VoidPointer.accepts(&pointer));
        assert_eq!(
            CType::function_pointer_signature(ty, &[pointer_ty]),
            CallbackSignature::UNSPECIFIED
        );
    }
}

#[test]
fn wide_address_arrays_use_sixteen_byte_stride_and_preserve_endpoint_values() {
    for (array_ty, ty, literal) in [
        (
            CType::Int128Array(3),
            CType::Int128,
            c_int128_literal(i128::MIN),
        ),
        (
            CType::UInt128Array(3),
            CType::UInt128,
            c_uint128_literal(u128::MAX),
        ),
    ] {
        let state = normal(CState::new(), c_declare("items", array_ty));
        let expected = value(&CState::new(), literal.clone());
        let base = value(&state, c_variable("items"));
        assert_eq!(base.c_type(), ty.pointer_to().unwrap());
        let CValue::Pointer(base) = base else {
            unreachable!()
        };
        assert_eq!(
            state.memory.block_size(&base.block).unwrap().as_const(),
            Some(48)
        );
        assert_eq!(array_ty.abi_alignment(), 16);
        let state = normal(state, c_typed_store(element_address(2), literal, ty));
        let last = value(&state, element_address(2));
        let CValue::Pointer(last) = last else {
            unreachable!()
        };
        assert_eq!(last.offset, PointerOffsetTerm::Constant(32));
        assert_eq!(
            value(&state, c_index(c_variable("items"), c_int32_literal(2))),
            expected
        );
        assert!(matches!(
            outcome(&state, c_index(c_variable("items"), c_int32_literal(1))),
            CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead)
        ));
        // Forming the one-past pointer is valid; dereferencing it is not.
        let past = value(&state, c_add(c_variable("items"), c_int32_literal(3)));
        let CValue::Pointer(past) = past else {
            unreachable!()
        };
        assert_eq!(past.offset, PointerOffsetTerm::Constant(48));
        let read_past = c_typed_load(CExpression::Value(CValue::Pointer(past)), ty);
        let paths = evaluate_c_expression_paths(
            &state,
            &read_past,
            &PureFactContext::new(),
            &mut ExecutionBudget::for_c_expression(&read_past),
        )
        .unwrap();
        assert!(
            !paths
                .iter()
                .any(|path| matches!(path.outcome, CExpressionOutcome::Value(_))
                    && path.obligations.is_empty())
        );
        let theorem = prove_c_expression_evaluation(state, read_past)
            .expect("the invalid one-past read has a concrete checked outcome");
        assert!(matches!(
            theorem.proposition(),
            Proposition::CExpressionEvaluates {
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
                ..
            }
        ));
    }
}

#[test]
fn wide_address_pointer_arrays_scale_slots_by_eight_and_pointees_by_sixteen() {
    for (element, pointer_ty, ty, literal) in [
        (
            CPointerArrayElement::Int128,
            CType::Int128Pointer,
            CType::Int128,
            c_int128_literal(i128::MAX),
        ),
        (
            CPointerArrayElement::UInt128,
            CType::UInt128Pointer,
            CType::UInt128,
            c_uint128_literal(1u128 << 100),
        ),
    ] {
        let state = normal(
            CState::new(),
            c_seq(
                c_declare("wide", ty),
                c_seq(
                    c_assign("wide", literal.clone()),
                    c_declare("items", CType::PointerArray(element, 2)),
                ),
            ),
        );
        let state = normal(
            state,
            c_typed_store(element_address(1), c_addr_of("wide"), pointer_ty),
        );
        let CValue::Pointer(slot) = value(&state, element_address(1)) else {
            unreachable!()
        };
        assert_eq!(slot.c_type(), pointer_ty.pointer_to().unwrap());
        assert_eq!(slot.offset, PointerOffsetTerm::Constant(8));
        assert_eq!(
            value(
                &state,
                c_load(c_index(c_variable("items"), c_int32_literal(1)))
            ),
            value(&CState::new(), literal)
        );
        assert_eq!(
            CPointerArrayElement::from_pointer_type(pointer_ty),
            Some(element)
        );
        assert_eq!(element.pointer_type(), pointer_ty);
        assert_eq!(CType::PointerArray(element, 2).byte_width(), 16);
    }
}

#[test]
fn wide_address_pointer_slot_read_needs_eight_bytes_but_pointee_read_needs_sixteen() {
    let slot = Pointer {
        block: "wide-slot-external".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let pointee = Pointer {
        block: "wide-pointee-external".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new()
        .with_block(slot.block.clone(), 8)
        .with_block(pointee.block.clone(), 16)
        .store(
            slot.clone(),
            CValue::typed_pointer(pointee.clone(), CType::UInt128Pointer),
        )
        .store(
            pointee.clone(),
            value(&CState::new(), c_uint128_literal(u128::MAX)),
        );
    for bytes in [8, 16] {
        let range = |p| CMemoryRange::new_with_element_width(p, 0u32.into(), 1u32.into(), bytes);
        let state = CState::new()
            .with_memory(memory.clone())
            .with_resource_context(ResourceContext::new().unchecked_with_facts([
                CResourceFact::view_memory(CMemoryRange::new_with_element_width(
                    slot.clone(),
                    0u32.into(),
                    1u32.into(),
                    8,
                )),
                CResourceFact::view_memory(range(pointee.clone())),
            ]));
        let pointer = value(
            &state,
            c_typed_load(
                c_typed_pointer_value(slot.clone(), CType::UInt128PointerPointer),
                CType::UInt128Pointer,
            ),
        );
        assert_eq!(pointer.c_type(), CType::UInt128Pointer);
        let read = outcome(
            &state,
            c_typed_load(CExpression::Value(pointer), CType::UInt128),
        );
        assert_eq!(matches!(read, CExpressionOutcome::Value(_)), bytes == 16);
        if bytes == 8 {
            assert!(matches!(
                read,
                CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
            ));
        }
    }
}

#[test]
fn wide_address_symbolic_array_runs_keep_typed_loads_and_bounded_work() {
    for ty in [CType::Int128, CType::UInt128] {
        let mut samples = Vec::new();
        for count in [16, 64, 256, 1024, 1_000_000] {
            let _session = crate::kernel::VerificationSession::enter();
            let base = CMemory::global_pointer("wide-run");
            let at = |index| base.offset_by_bytes(index * 16);
            let zero = value(
                &CState::new(),
                if ty == CType::Int128 {
                    c_int128_literal(0)
                } else {
                    c_uint128_literal(0)
                },
            );
            let function = c_function(
                CType::Int32,
                "wide_array",
                vec![],
                c_return(c_int32_literal(0)),
            )
            .with_global_arrays(vec![CGlobalArray::new_with_kernel_name(
                "wide-run",
                "wide-run",
                ty,
                count,
                CArrayContents::new(count, zero, []),
            )]);
            let (entry, setup_work) = crate::instrumentation::measure_deterministic_work(|| {
                initialize_c_function_globals(&CState::new(), &function)
            });
            let memory = entry.memory.clone();
            assert_eq!(memory.cells.representation_len(), 1);
            let (loaded, read_work) = crate::instrumentation::measure_deterministic_work(|| {
                memory.known_value(&at(count - 1)).unwrap()
            });
            assert_eq!(loaded.c_type(), ty);
            let machine = MachineIntegerType::from_c_type(ty).unwrap();
            assert!(machine.accepts_wide_term(&c_value_bitvector_term(&loaded).unwrap()));
            assert_eq!(loaded, memory.known_value(&at(count - 1)).unwrap());
            let state = CState::new()
                .with_memory(memory.clone())
                .with_resource_context(ResourceContext::new().unchecked_with_facts([
                    CResourceFact::view_memory(CMemoryRange::new_with_element_width(
                        at(count - 1),
                        0u32.into(),
                        1u32.into(),
                        16,
                    )),
                ]));
            assert_eq!(
                value(
                    &state,
                    c_typed_load(
                        c_typed_pointer_value(at(count - 1), ty.pointer_to().unwrap()),
                        ty
                    )
                ),
                loaded
            );
            let replacement = value(
                &CState::new(),
                if ty == CType::Int128 {
                    c_int128_literal(i128::MIN)
                } else {
                    c_uint128_literal(u128::MAX)
                },
            );
            let changed = memory
                .without_possible_aliasing_cells(&at(count - 1), 16, &PureFactContext::new())
                .store(at(count - 1), replacement.clone());
            assert_eq!(changed.known_value(&at(count - 1)), Some(replacement));
            assert!(changed.known_value(&at(count - 2)).is_some());
            samples.push(setup_work + read_work);
        }
        assert!(samples.iter().all(|work| *work < 4096), "{samples:?}");
        assert!(
            samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 128,
            "{samples:?}"
        );
    }
}

#[test]
fn wide_address_symbolic_pointer_slot_reads_keep_eight_byte_access_identity() {
    for pointer_ty in [CType::Int128Pointer, CType::UInt128Pointer] {
        let slot = Pointer {
            block: "wide-symbolic-slot".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        for bytes in [7, 8] {
            let state = CState::new()
                .with_memory(CMemory::new().with_block(slot.block.clone(), 8))
                .with_resource_context(ResourceContext::new().unchecked_with_facts([
                    CResourceFact::view_memory(CMemoryRange::new_with_element_width(
                        slot.clone(),
                        0u32.into(),
                        bytes.into(),
                        1,
                    )),
                ]));
            let expression = c_typed_load(
                c_typed_pointer_value(slot.clone(), pointer_ty.pointer_to().unwrap()),
                pointer_ty,
            );
            let first = outcome(&state, expression.clone());
            assert_eq!(first, outcome(&state, expression));
            if bytes == 7 {
                assert!(matches!(
                    first,
                    CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
                ));
            } else {
                let CExpressionOutcome::Value(pointer) = first else {
                    panic!("pointer read")
                };
                assert_eq!(pointer.c_type(), pointer_ty);
                assert_eq!(pointer.byte_width(), 8);
                assert_eq!(pointer_ty.pointee_type().unwrap().byte_width(), 16);
            }
        }
    }
}

#[test]
fn wide_address_static_array_startup_and_entry_keep_initializer_authority_separate() {
    for (ty, zero_literal, endpoint_literal) in [
        (
            CType::Int128,
            c_int128_literal(0),
            c_int128_literal(i128::MIN),
        ),
        (
            CType::UInt128,
            c_uint128_literal(0),
            c_uint128_literal(u128::MAX),
        ),
    ] {
        let zero = value(&CState::new(), zero_literal);
        let endpoint = value(&CState::new(), endpoint_literal);
        let function = c_function(
            CType::Int32,
            "wide_static",
            vec![],
            c_return(c_int32_literal(0)),
        )
        .with_static_arrays(vec![CStaticArray::new(
            "items",
            "items",
            ty,
            3,
            CArrayContents::new(3, zero.clone(), [(2, endpoint.clone())]),
        )]);
        let at = |index: u32| {
            CMemory::static_pointer("wide_static", "items").offset_by_bytes(index * 16)
        };
        let startup = crate::kernel::initialize_c_program_storage([function.clone()]).unwrap();
        assert_eq!(startup.memory.known_value(&at(0)), Some(zero));
        assert_eq!(startup.memory.known_value(&at(2)), Some(endpoint.clone()));
        assert_eq!(
            value(
                &startup,
                c_typed_load(c_typed_pointer_value(at(2), ty.pointer_to().unwrap()), ty)
            ),
            endpoint.clone()
        );
        let entry = initialize_c_function_globals(&CState::new(), &function);
        assert_ne!(entry.memory.known_value(&at(2)), Some(endpoint.clone()));
        assert!(entry.resources.facts().is_empty());
        // Nested entry retains a caller's writes; it cannot restore an initializer.
        let changed = startup.with_memory(entry.memory.clone().store(at(2), endpoint.clone()));
        let nested = initialize_c_function_globals(&changed, &function);
        assert_eq!(nested.memory.known_value(&at(2)), Some(endpoint));
    }
}

#[test]
fn wide_address_narrow_array_copy_refuses_a_wide_cell_overlapping_its_prefix() {
    let at = |offset| Pointer {
        block: "local:wide-prefix".into(),
        offset: PointerOffsetTerm::Constant(offset),
    };
    let mut memory = CMemory::new()
        .with_block("local:wide-prefix", 16)
        .with_block("local:wide-target", 8)
        .with_initialized_object(&at(0), 16)
        .store(at(0), value(&CState::new(), c_uint128_literal(u128::MAX)));
    for offset in 8..16 {
        memory = memory.store(at(offset), uint8(1));
    }
    // Compact copies require a homogeneous source region. Its indexed prefix check
    // must see the wide cell starting eight bytes before this byte region.
    assert!(
        memory
            .write_scalar_array_region(
                &Pointer {
                    block: "local:wide-target".into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                CType::UInt8,
                8,
                CValue::typed_pointer(at(8), CType::UInt8Pointer),
                true,
                false,
                &PureFactContext::new()
            )
            .is_err()
    );
}

#[test]
fn checked_object_address_accepts_uninitialized_storage_without_reading_it() {
    let state = normal(CState::new(), c_declare("items", CType::Int32Array(2)));
    let pointer = c_checked_object_address(c_index(c_variable("items"), c_int32_literal(1)));
    let address = value(&state, pointer);
    assert_eq!(address, value(&state, element_address(1)));
    assert!(matches!(
        outcome(
            &state,
            c_typed_load(CExpression::Value(address), CType::Int32)
        ),
        CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead)
    ));
}

#[test]
fn checked_object_address_rejects_one_past_while_c_address_cancellation_preserves_it() {
    let state = normal(CState::new(), c_declare("items", CType::Int32Array(2)));
    assert!(matches!(
        outcome(&state, element_address(2)),
        CExpressionOutcome::Value(CValue::Pointer(_))
    ));
    assert!(matches!(
        outcome(
            &state,
            c_checked_object_address(c_index(c_variable("items"), c_int32_literal(2)))
        ),
        CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory)
    ));
    assert!(matches!(
        outcome(
            &state,
            c_checked_object_address(c_typed_load(
                CExpression::Value(CValue::typed_pointer(Pointer::null(), CType::Int32Pointer)),
                CType::Int32
            ))
        ),
        CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory)
    ));
}

#[test]
fn checked_object_address_rejects_storage_after_its_local_lifetime_ends() {
    let state = normal(CState::new(), c_declare("items", CType::Int32Array(2)));
    let address = value(&state, element_address(0));
    let CValue::Pointer(pointer) = &address else {
        unreachable!()
    };
    let retired = state
        .clone()
        .with_memory(state.memory().without_local_block(&pointer.pointer().block));
    assert!(matches!(
        outcome(
            &retired,
            c_checked_object_address(c_typed_load(CExpression::Value(address), CType::Int32))
        ),
        CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory)
    ));
}

#[test]
fn wide_pointer_subtraction_preserves_unsigned_magnitude_and_bounds() {
    let state = CState::new().with_memory(CMemory::new().with_block("offsets", 16));
    let at = |offset| Pointer {
        block: "offsets".into(),
        offset: PointerOffsetTerm::Constant(offset),
    };
    for ty in [CType::VoidPointer, CType::UInt8Pointer, CType::Int32Pointer] {
        let stride = if ty == CType::Int32Pointer { 4 } else { 1 };
        for offset in [c_uint32_literal(1), c_uint64_literal(1), c_int64_literal(1)] {
            let result = value(
                &state,
                c_subtract(c_cast(c_typed_pointer_value(at(8), ty), ty), offset),
            );
            assert_eq!(result, CValue::typed_pointer(at(8 - stride), ty));
        }
        let result = value(
            &state,
            c_subtract(
                c_cast(c_typed_pointer_value(at(8), ty), ty),
                c_int64_literal(-1),
            ),
        );
        assert_eq!(result, CValue::typed_pointer(at(8 + stride), ty));
        for offset in [
            c_uint64_literal(17),
            c_uint64_literal(u64::MAX),
            c_int64_literal(i64::MIN),
        ] {
            assert!(matches!(
                outcome(
                    &state,
                    c_subtract(c_cast(c_typed_pointer_value(at(8), ty), ty), offset)
                ),
                CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic)
            ));
        }
        for offset in [c_uint32_literal(0), c_uint64_literal(0), c_int64_literal(0)] {
            assert_eq!(
                value(
                    &state,
                    c_subtract(c_cast(c_typed_pointer_value(at(0), ty), ty), offset)
                ),
                CValue::typed_pointer(at(0), ty)
            );
        }
    }
}

#[test]
fn native_reference_binding_uses_geometry_without_byte_permission_or_initialization() {
    let _session = crate::kernel::VerificationSession::enter();
    let input = CPointerValue::new(Pointer::symbolic(Variable(989_831)), CType::Int32Pointer)
        .with_designation(PointerDesignation::Unresolved(Variable(989_831)));
    let memory = CMemory::new()
        .with_native_input_span(
            input.clone(),
            CType::Int32,
            IntegerTerm::constant_i64(3).into(),
        )
        .unwrap();
    let state = CState::new()
        .with_memory(memory)
        .with_typed_access_policy(CTypedAccessPolicy::NativeObjectOnly);
    let selected = input
        .clone()
        .with_pointer(input.pointer().offset_by_bytes(4));
    let expression = c_checked_object_address(c_typed_load(
        CExpression::Value(CValue::Pointer(selected.clone())),
        CType::Int32,
    ));
    assert_eq!(value(&state, expression), CValue::Pointer(selected.clone()));
    assert!(state.resources().facts().is_empty());
    assert!(!state.memory().has_initialized_bytes_under(
        selected.pointer(),
        4,
        &PureFactContext::new()
    ));
    assert!(!matches!(
        outcome(
            &state,
            c_typed_load(CExpression::Value(CValue::Pointer(selected)), CType::Int32)
        ),
        CExpressionOutcome::Value(_)
    ));
    let one_past = input
        .clone()
        .with_pointer(input.pointer().offset_by_bytes(12));
    assert!(
        prove_c_expression_evaluation(
            state.clone(),
            c_checked_object_address(c_typed_load(
                CExpression::Value(CValue::Pointer(one_past)),
                CType::Int32
            ))
        )
        .is_none()
    );
    let forged = CPointerValue::new(input.pointer().clone(), input.c_type());
    assert!(
        prove_c_expression_evaluation(
            state,
            c_checked_object_address(c_typed_load(
                CExpression::Value(CValue::Pointer(forged)),
                CType::Int32
            ))
        )
        .is_none()
    );
}
