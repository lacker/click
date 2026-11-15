use super::*;

fn address(offset: i64) -> Pointer {
    Pointer {
        block: "local:wide-storage".into(),
        offset: PointerOffsetTerm::Constant(offset),
    }
}

fn literal(value: ProgramExpression) -> ProgramValue {
    let ProgramExpression::Value(value) = value else {
        unreachable!()
    };
    value
}

fn load(pointer: Pointer, ty: ProgramType) -> ProgramExpression {
    crate::kernel::program_expression::typed_load(
        crate::kernel::program_expression::typed_pointer_value(pointer, ProgramType::VoidPointer),
        ty,
    )
}

fn paths(state: &ExecutionState, expression: &ProgramExpression) -> Vec<ExpressionPath> {
    evaluate_program_expression_paths(
        state,
        expression,
        &PureFactContext::new(),
        &mut ExecutionBudget::for_program_expression(expression),
    )
    .unwrap()
}

#[test]
fn wide_storage_exact_typed_store_and_load_preserve_all_bits() {
    for value in [
        literal(crate::kernel::program_expression::int128_literal(i128::MIN)),
        literal(crate::kernel::program_expression::int128_literal(i128::MAX)),
        literal(crate::kernel::program_expression::uint128_literal(
            u128::MAX,
        )),
        literal(crate::kernel::program_expression::uint128_literal(
            (1u128 << 127) | (1u128 << 65) | 1,
        )),
        ProgramValue::Int128(MachineTerm::Variable(Variable(152_001))),
    ] {
        let ty = value.program_type();
        let state = ExecutionState::new().with_memory(
            Memory::new()
                .with_block("local:wide-storage", 32)
                .with_initialized_object(&address(0), 32),
        );
        let statement = program_typed_store(
            crate::kernel::program_expression::typed_pointer_value(
                address(0),
                ProgramType::VoidPointer,
            ),
            ProgramExpression::Value(value.clone()),
            ty,
        );
        let theorem = prove_execution_statement_execution(state, statement).unwrap();
        let Proposition::ProgramStatementExecutes {
            outcome: StatementOutcome::Normal(after),
            ..
        } = theorem.proposition()
        else {
            panic!("{:?}", theorem.proposition());
        };
        let result = paths(after, &load(address(0), ty));
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].outcome, ExpressionOutcome::Value(value.clone()));
        assert!(result[0].obligations.is_empty());
        assert_eq!(after.memory.known_value(&address(0)), Some(value));
    }
}

#[test]
fn wide_storage_symbolic_loads_keep_kind_width_and_defining_identity() {
    let state = ExecutionState::new().with_memory(
        Memory::new()
            .with_block("local:wide-storage", 32)
            .with_initialized_object(&address(0), 32),
    );
    let mut identities = Vec::new();
    for (ty, machine, kind) in [
        (
            ProgramType::Int128,
            MachineIntegerType::Int128,
            LoadKind::Int128,
        ),
        (
            ProgramType::UInt128,
            MachineIntegerType::UInt128,
            LoadKind::UInt128,
        ),
    ] {
        let expression = load(address(0), ty);
        let first = paths(&state, &expression);
        let second = paths(&state, &expression);
        assert_eq!(first.len(), 1);
        assert_eq!(first[0].outcome, second[0].outcome);
        let ExpressionOutcome::Value(value) = &first[0].outcome else {
            panic!("symbolic load")
        };
        assert_eq!(value.program_type(), ty);
        let term = program_value_bitvector_term(value).unwrap();
        let raw = term;
        assert!(
            matches!(&raw, MachineTerm::MemoryLoad(_, pointer, actual) if **pointer == address(0) && *actual == kind)
        );
        assert_eq!(kind.byte_width(), 16);
        assert!(machine.accepts_wide_term(&raw));
        assert!(IntegerTerm::from_machine(machine, raw.clone()).is_some());
        assert_eq!(
            crate::kernel::eval::scalar_read_observation(
                crate::kernel::MachineOperandView::Legacy(&raw)
            )
            .unwrap()
            .bytes,
            16
        );
        assert!(first[0].facts.is_empty());
        assert!(first[0].obligations.is_empty());
        identities.push(raw);
    }
    assert_ne!(identities[0], identities[1]);
}

#[test]
fn wide_storage_refuses_wrong_load_kind_and_typed_reinterpretation() {
    let memory = Memory::new().with_block("local:wide-storage", 32).store(
        address(0),
        literal(crate::kernel::program_expression::uint128_literal(
            u128::MAX,
        )),
    );
    let state = ExecutionState::new().with_memory(memory.clone());
    for ty in [ProgramType::Int128, ProgramType::Int64, ProgramType::UInt8] {
        let result = paths(&state, &load(address(0), ty));
        assert_eq!(result.len(), 1);
        assert!(matches!(
            result[0].outcome,
            ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch { .. })
        ));
    }
    for (machine, wrong) in [
        (MachineIntegerType::Int128, LoadKind::UInt128),
        (MachineIntegerType::UInt128, LoadKind::Int128),
        (MachineIntegerType::Int128, LoadKind::Bits64),
    ] {
        let raw =
            MachineTerm::MemoryLoad(intern_memory(memory.clone()), Box::new(address(0)), wrong);
        assert!(!machine.accepts_wide_term(&raw));
        assert!(IntegerTerm::from_machine(machine, raw.clone()).is_none());
        let wrapped = if machine == MachineIntegerType::Int128 {
            ProgramValue::Int128(raw)
        } else {
            ProgramValue::UInt128(raw)
        };
        assert!(matches!(
            paths(&state, &ProgramExpression::Value(wrapped))[0].outcome,
            ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch)
        ));
    }
    assert_eq!(
        ProgramType::Int128.pointer_to(),
        Some(ProgramType::Int128Pointer)
    );
    assert_eq!(
        ProgramType::UInt128.pointer_to(),
        Some(ProgramType::UInt128Pointer)
    );
}

#[test]
fn wide_storage_symbolic_load_requires_full_extent_and_local_initialization() {
    for (size, offset) in [(15, 0), (16, 1), (32, 17)] {
        let state =
            ExecutionState::new().with_memory(Memory::new().with_block("local:wide-storage", size));
        let result = paths(&state, &load(address(offset), ProgramType::Int128));
        assert!(
            !result
                .iter()
                .any(|path| matches!(path.outcome, ExpressionOutcome::Value(_))
                    && path.obligations.is_empty())
        );
        assert!(
            prove_program_expression_evaluation(state, load(address(offset), ProgramType::Int128))
                .is_none()
        );
    }
    let pointer = Pointer {
        block: "local:wide-storage".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new().with_block("local:wide-storage", 16);
    let state = ExecutionState::new().with_memory(memory);
    assert_eq!(
        paths(&state, &load(pointer, ProgramType::Int128))[0].outcome,
        ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead)
    );
}

#[test]
fn wide_storage_frame_transport_uses_all_sixteen_bytes() {
    let before = Memory::new().with_block("local:wide-storage", 48);
    let condition = |memory: &Memory| {
        ConditionTerm::equal(
            MachineTerm::MemoryLoad(
                intern_memory(memory.clone()),
                Box::new(address(0)),
                LoadKind::Int128,
            ),
            MachineTerm::Variable(Variable(152_003)),
        )
    };
    let assumptions = PureFactContext::new();
    for offset in [16, 32] {
        let after = before.clone().store(
            address(offset),
            literal(crate::kernel::program_expression::uint8_literal(3)),
        );
        assert!(
            assumptions
                .conditions_equal_modulo_proven_states(&condition(&before), &condition(&after)),
            "disjoint {offset}"
        );
    }
    for offset in [0, 7, 8, 15] {
        let after = before.clone().store(
            address(offset),
            literal(crate::kernel::program_expression::uint8_literal(3)),
        );
        assert!(
            !assumptions
                .conditions_equal_modulo_proven_states(&condition(&before), &condition(&after)),
            "overlap {offset}"
        );
    }
}

/// A 64-bit order over a load matches across a disjoint store just as a
/// 32-bit one does: the comparison operator is compared, not its width.
#[test]
fn wide_order_frame_transport_matches_across_a_disjoint_store() {
    let before = Memory::new().with_block("local:wide-storage", 16);
    let after = before.clone().store(
        address(8),
        literal(crate::kernel::program_expression::uint8_literal(3)),
    );
    let condition = |memory: &Memory| {
        ConditionTerm::uint64_less_than(
            MachineTerm::MemoryLoad(
                intern_memory(memory.clone()),
                Box::new(address(0)),
                LoadKind::Bits64,
            ),
            MachineTerm::Variable(Variable(152_004)),
        )
    };
    assert!(
        PureFactContext::new()
            .conditions_equal_modulo_proven_states(&condition(&before), &condition(&after))
    );
}

#[test]
fn wide_storage_overlapping_store_invalidates_high_bytes_and_gap_skip() {
    let before = Memory::new().with_block("local:wide-storage", 48).store(
        address(0),
        literal(crate::kernel::program_expression::uint128_literal(
            u128::MAX,
        )),
    );
    for offset in [0, 7, 8, 15] {
        let after = before
            .clone()
            .without_possible_aliasing_cells(&address(offset), 1, &PureFactContext::new())
            .store(
                address(offset),
                literal(crate::kernel::program_expression::uint8_literal(3)),
            );
        assert!(
            !matches!(
                after.known_value(&address(0)),
                Some(ProgramValue::UInt128(_))
            ),
            "overlap {offset}"
        );
    }
    for offset in [16, 32] {
        let after = before
            .clone()
            .without_possible_aliasing_cells(&address(offset), 1, &PureFactContext::new())
            .store(
                address(offset),
                literal(crate::kernel::program_expression::uint8_literal(3)),
            );
        assert_eq!(
            after.known_value(&address(0)),
            before.known_value(&address(0)),
            "disjoint {offset}"
        );
    }
    for offset in [8, 15, 16, 32] {
        let write =
            MemoryRange::new_with_element_width(address(offset), 0u32.into(), 1u32.into(), 1);
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
            MemoryRange::new_with_element_width(pointer.clone(), 0u32.into(), bytes.into(), 1);
        let memory = Memory::new().with_block("wide-external", 16);
        let read_state = ExecutionState::new()
            .with_memory(memory.clone())
            .with_resource_context(
                ResourceContext::new()
                    .unchecked_with_facts([ResourceFact::view_memory(range.clone())]),
            );
        let result = paths(&read_state, &load(pointer.clone(), ProgramType::UInt128));
        assert_eq!(result.len(), 1);
        assert_eq!(
            matches!(
                result[0].outcome,
                ExpressionOutcome::Value(ProgramValue::UInt128(_))
            ),
            bytes == 16
        );
        if bytes == 8 {
            assert!(matches!(
                result[0].outcome,
                ExpressionOutcome::RuntimeError(RuntimeError::MissingResource { .. })
            ));
        }
        let write_state = ExecutionState::new()
            .with_memory(memory)
            .with_resource_context(
                ResourceContext::new().unchecked_with_facts([ResourceFact::own_memory(range)]),
            );
        let statement = program_typed_store(
            crate::kernel::program_expression::typed_pointer_value(
                pointer.clone(),
                ProgramType::VoidPointer,
            ),
            crate::kernel::program_expression::uint128_literal(u128::MAX),
            ProgramType::UInt128,
        );
        let theorem = prove_execution_statement_execution(write_state, statement).unwrap();
        let Proposition::ProgramStatementExecutes { outcome, .. } = theorem.proposition() else {
            unreachable!()
        };
        assert_eq!(matches!(outcome, StatementOutcome::Normal(_)), bytes == 16);
        if bytes == 8 {
            assert!(matches!(
                outcome,
                StatementOutcome::RuntimeError(RuntimeError::MissingResource { .. })
            ));
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/wide_storage_tests.rs");
}
