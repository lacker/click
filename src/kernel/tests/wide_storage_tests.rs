use super::*;

fn address(offset: i64) -> Pointer {
    Pointer {
        block: "local:wide-storage".into(),
        offset: PointerOffsetTerm::Constant(offset),
    }
}

fn literal(value: CExpression) -> CValue {
    let CExpression::Value(value) = value else {
        unreachable!()
    };
    value
}

fn load(pointer: Pointer, ty: CType) -> CExpression {
    c_typed_load(c_typed_pointer_value(pointer, CType::VoidPointer), ty)
}

fn paths(state: &CState, expression: &CExpression) -> Vec<CExpressionPath> {
    evaluate_c_expression_paths(
        state,
        expression,
        &PureFactContext::new(),
        &mut ExecutionBudget::for_c_expression(expression),
    )
    .unwrap()
}

#[test]
fn wide_storage_exact_typed_store_and_load_preserve_all_bits() {
    for value in [
        literal(c_int128_literal(i128::MIN)),
        literal(c_int128_literal(i128::MAX)),
        literal(c_uint128_literal(u128::MAX)),
        literal(c_uint128_literal((1u128 << 127) | (1u128 << 65) | 1)),
        CValue::Int128(Bitvector32Term::Variable(Variable(152_001))),
    ] {
        let ty = value.c_type();
        let state = CState::new().with_memory(
            CMemory::new()
                .with_block("local:wide-storage", 32)
                .with_initialized_object(&address(0), 32),
        );
        let statement = c_typed_store(
            c_typed_pointer_value(address(0), CType::VoidPointer),
            CExpression::Value(value.clone()),
            ty,
        );
        let theorem = prove_c_statement_execution(state, statement).unwrap();
        let Proposition::CStatementExecutes {
            outcome: CStatementOutcome::Normal(after),
            ..
        } = theorem.proposition()
        else {
            panic!("{:?}", theorem.proposition());
        };
        let result = paths(after, &load(address(0), ty));
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].outcome, CExpressionOutcome::Value(value.clone()));
        assert!(result[0].obligations.is_empty());
        assert_eq!(after.memory.known_value(&address(0)), Some(value));
    }
}

#[test]
fn wide_storage_symbolic_loads_keep_kind_width_and_defining_identity() {
    let state = CState::new().with_memory(
        CMemory::new()
            .with_block("local:wide-storage", 32)
            .with_initialized_object(&address(0), 32),
    );
    let mut identities = Vec::new();
    for (ty, machine, kind) in [
        (CType::Int128, MachineIntegerType::Int128, LoadKind::Int128),
        (
            CType::UInt128,
            MachineIntegerType::UInt128,
            LoadKind::UInt128,
        ),
    ] {
        let expression = load(address(0), ty);
        let first = paths(&state, &expression);
        let second = paths(&state, &expression);
        assert_eq!(first.len(), 1);
        assert_eq!(first[0].outcome, second[0].outcome);
        let CExpressionOutcome::Value(value) = &first[0].outcome else {
            panic!("symbolic load")
        };
        assert_eq!(value.c_type(), ty);
        let term = c_value_bitvector_term(value).unwrap();
        let Bitvector32Term::Variable(variable) = term else {
            panic!("load variable")
        };
        let raw = crate::kernel::eval::registered_load_term_for_variable(&variable).unwrap();
        assert!(
            matches!(&raw, Bitvector32Term::MemoryLoad(_, pointer, actual) if **pointer == address(0) && *actual == kind)
        );
        assert_eq!(kind.byte_width(), 16);
        assert!(machine.accepts_wide_term(&raw));
        assert!(IntegerTerm::from_machine(machine, raw.clone()).is_some());
        assert_eq!(
            crate::kernel::eval::registered_load_bytes_for_variable(&variable),
            Some(16)
        );
        assert!(!first[0].facts.is_empty());
        assert!(first[0].obligations.is_empty());
        identities.push(variable);
    }
    assert_ne!(identities[0], identities[1]);
}

#[test]
fn wide_storage_refuses_wrong_load_kind_and_typed_reinterpretation() {
    let memory = CMemory::new()
        .with_block("local:wide-storage", 32)
        .store(address(0), literal(c_uint128_literal(u128::MAX)));
    let state = CState::new().with_memory(memory.clone());
    for ty in [CType::Int128, CType::Int64, CType::UInt8] {
        let result = paths(&state, &load(address(0), ty));
        assert_eq!(result.len(), 1);
        assert!(matches!(
            result[0].outcome,
            CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch { .. })
        ));
    }
    for (machine, wrong) in [
        (MachineIntegerType::Int128, LoadKind::UInt128),
        (MachineIntegerType::UInt128, LoadKind::Int128),
        (MachineIntegerType::Int128, LoadKind::Bits64),
    ] {
        let raw = Bitvector32Term::MemoryLoad(
            intern_c_memory(memory.clone()),
            Box::new(address(0)),
            wrong,
        );
        assert!(!machine.accepts_wide_term(&raw));
        assert!(IntegerTerm::from_machine(machine, raw.clone()).is_none());
        let wrapped = if machine == MachineIntegerType::Int128 {
            CValue::Int128(raw)
        } else {
            CValue::UInt128(raw)
        };
        assert!(matches!(
            paths(&state, &CExpression::Value(wrapped))[0].outcome,
            CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch)
        ));
    }
    assert_eq!(CType::Int128.pointer_to(), Some(CType::Int128Pointer));
    assert_eq!(CType::UInt128.pointer_to(), Some(CType::UInt128Pointer));
}

#[test]
fn wide_storage_symbolic_load_requires_full_extent_and_local_initialization() {
    for (size, offset) in [(15, 0), (16, 1), (32, 17)] {
        let state =
            CState::new().with_memory(CMemory::new().with_block("local:wide-storage", size));
        let result = paths(&state, &load(address(offset), CType::Int128));
        assert!(
            !result
                .iter()
                .any(|path| matches!(path.outcome, CExpressionOutcome::Value(_))
                    && path.obligations.is_empty())
        );
        assert!(
            prove_c_expression_evaluation(state, load(address(offset), CType::Int128)).is_none()
        );
    }
    let pointer = Pointer {
        block: "local:wide-storage".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("local:wide-storage", 16);
    let state = CState::new().with_memory(memory);
    assert_eq!(
        paths(&state, &load(pointer, CType::Int128))[0].outcome,
        CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead)
    );
}

#[test]
fn wide_storage_frame_transport_uses_all_sixteen_bytes() {
    let before = CMemory::new().with_block("local:wide-storage", 48);
    let condition = |memory: &CMemory| {
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                intern_c_memory(memory.clone()),
                Box::new(address(0)),
                LoadKind::Int128,
            ),
            Bitvector32Term::Variable(Variable(152_003)),
        )
    };
    let assumptions = PureFactContext::new();
    for offset in [16, 32] {
        let after = before
            .clone()
            .store(address(offset), literal(c_uint8_literal(3)));
        assert!(
            assumptions
                .conditions_equal_modulo_proven_snapshots(&condition(&before), &condition(&after)),
            "disjoint {offset}"
        );
    }
    for offset in [0, 7, 8, 15] {
        let after = before
            .clone()
            .store(address(offset), literal(c_uint8_literal(3)));
        assert!(
            !assumptions
                .conditions_equal_modulo_proven_snapshots(&condition(&before), &condition(&after)),
            "overlap {offset}"
        );
    }
}

/// A 64-bit order over a load matches across a disjoint store just as a
/// 32-bit one does: the comparison operator is compared, not its width.
#[test]
fn wide_order_frame_transport_matches_across_a_disjoint_store() {
    let before = CMemory::new().with_block("local:wide-storage", 16);
    let after = before
        .clone()
        .store(address(8), literal(c_uint8_literal(3)));
    let condition = |memory: &CMemory| {
        ConditionTerm::uint64_less_than(
            Bitvector32Term::MemoryLoad(
                intern_c_memory(memory.clone()),
                Box::new(address(0)),
                LoadKind::Bits64,
            ),
            Bitvector32Term::Variable(Variable(152_004)),
        )
    };
    assert!(
        PureFactContext::new()
            .conditions_equal_modulo_proven_snapshots(&condition(&before), &condition(&after))
    );
}

#[test]
fn wide_storage_exact_load_and_validation_work_ignore_unrelated_memory() {
    let value = literal(c_uint128_literal(u128::MAX));
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut memory = CMemory::new()
            .with_block("local:wide-storage", 16)
            .store(address(0), value.clone());
        for index in 0..size {
            let pointer = Pointer {
                block: format!("wide-unrelated-{index}").into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            memory = memory
                .with_block(pointer.block.clone(), 4)
                .store(pointer, literal(c_int32_literal(index)));
        }
        let raw = Bitvector32Term::MemoryLoad(
            intern_c_memory(memory.clone()),
            Box::new(address(0)),
            LoadKind::UInt128,
        );
        let state = CState::new().with_memory(memory);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(MachineIntegerType::UInt128.accepts_wide_term(&raw));
            paths(&state, &load(address(0), CType::UInt128))
        });
        assert_eq!(result[0].outcome, CExpressionOutcome::Value(value.clone()));
        assert!(work < 4096, "{size}: {work}");
        samples.push(work);
    }
    assert!(
        samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 64,
        "{samples:?}"
    );
}

#[test]
fn wide_storage_overlapping_store_invalidates_high_bytes_and_gap_skip() {
    let before = CMemory::new()
        .with_block("local:wide-storage", 48)
        .store(address(0), literal(c_uint128_literal(u128::MAX)));
    for offset in [0, 7, 8, 15] {
        let after = before
            .clone()
            .without_possible_aliasing_cells(&address(offset), 1, &PureFactContext::new())
            .store(address(offset), literal(c_uint8_literal(3)));
        assert!(
            !matches!(after.known_value(&address(0)), Some(CValue::UInt128(_))),
            "overlap {offset}"
        );
    }
    for offset in [16, 32] {
        let after = before
            .clone()
            .without_possible_aliasing_cells(&address(offset), 1, &PureFactContext::new())
            .store(address(offset), literal(c_uint8_literal(3)));
        assert_eq!(
            after.known_value(&address(0)),
            before.known_value(&address(0)),
            "disjoint {offset}"
        );
    }
    for offset in [8, 15, 16, 32] {
        let write =
            CMemoryRange::new_with_element_width(address(offset), 0u32.into(), 1u32.into(), 1);
        let after = before.clone().with_call_memory_havoc(
            Variable(152_004),
            &[write],
            &PureFactContext::new(),
            None,
        );
        assert_eq!(
            after.known_value(&address(0)).is_some(),
            offset >= 16,
            "call write at {offset} must use the retained cell's full width"
        );
    }
    assert_eq!(
        crate::kernel::resource_tracker::widest_scalar_access_bytes(),
        16
    );
}

#[test]
fn wide_storage_external_access_needs_sixteen_bytes_of_authority() {
    let pointer = Pointer {
        block: "wide-external".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    for bytes in [8, 16] {
        let range =
            CMemoryRange::new_with_element_width(pointer.clone(), 0u32.into(), bytes.into(), 1);
        let memory = CMemory::new().with_block("wide-external", 16);
        let read_state = CState::new()
            .with_memory(memory.clone())
            .with_resource_context(
                ResourceContext::new()
                    .unchecked_with_facts([CResourceFact::view_memory(range.clone())]),
            );
        let result = paths(&read_state, &load(pointer.clone(), CType::UInt128));
        assert_eq!(result.len(), 1);
        assert_eq!(
            matches!(
                result[0].outcome,
                CExpressionOutcome::Value(CValue::UInt128(_))
            ),
            bytes == 16
        );
        if bytes == 8 {
            assert!(matches!(
                result[0].outcome,
                CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
            ));
        }
        let write_state = CState::new().with_memory(memory).with_resource_context(
            ResourceContext::new().unchecked_with_facts([CResourceFact::own_memory(range)]),
        );
        let statement = c_typed_store(
            c_typed_pointer_value(pointer.clone(), CType::VoidPointer),
            c_uint128_literal(u128::MAX),
            CType::UInt128,
        );
        let theorem = prove_c_statement_execution(write_state, statement).unwrap();
        let Proposition::CStatementExecutes { outcome, .. } = theorem.proposition() else {
            unreachable!()
        };
        assert_eq!(matches!(outcome, CStatementOutcome::Normal(_)), bytes == 16);
        if bytes == 8 {
            assert!(matches!(
                outcome,
                CStatementOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
            ));
        }
    }
}
