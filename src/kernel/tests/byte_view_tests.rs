//! The little-endian byte view of integer cells: one-byte C loads and stores
//! inside a wider integer cell, and every case that must stay refused.

use super::*;
use crate::kernel::eval::{ContainingIntegerCell, containing_integer_cell, integer_cell_byte};

fn word(offset: i64) -> Pointer {
    Pointer {
        block: PointerBlock::from("global:word"),
        offset: PointerOffsetTerm::Constant(offset),
    }
}

fn load_byte(
    memory: &CMemory,
    offset: i64,
    value_type: CType,
    byte_order: Option<ByteOrder>,
) -> CExpressionOutcome {
    let paths = evaluate_c_memory_load_paths(
        memory,
        word(offset),
        value_type,
        Vec::new().into(),
        Vec::new(),
        &PureFactContext::new(),
        false,
        false,
        None,
        byte_order,
    );
    assert_eq!(paths.len(), 1, "{paths:?}");
    paths[0].outcome.clone()
}

fn store_byte(memory: CMemory, offset: i64, byte: CValue, byte_order: ByteOrder) -> CMemory {
    let state = CState::new().with_memory(memory.clone());
    let state = if memory.requires_explicit_scalar_ownership(&word(0)) {
        state.with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                word(0),
                0.into(),
                memory.block_size(&word(0).block).unwrap().clone(),
                1,
            )),
        ))
    } else {
        state
    };
    let value_type = if matches!(byte, CValue::Int8(_)) {
        CType::Int8
    } else {
        CType::UInt8
    };
    let statement = CStatement::TypedStore {
        pointer: CExpression::Value(CValue::typed_pointer(
            word(offset),
            if value_type == CType::Int8 {
                CType::Int8Pointer
            } else {
                CType::UInt8Pointer
            },
        )),
        value: CExpression::Value(byte),
        value_type,
        volatile: false,
        pointee_constant: false,
    };
    let paths = execute_c_statement_paths(
        &state,
        &statement,
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(
            &CExecutionEnvironment::new().with_byte_order(byte_order),
        ),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    let CStatementOutcome::Normal(state) = &paths[0].outcome else {
        panic!("byte store should execute: {:?}", paths[0].outcome);
    };
    state.memory().clone()
}

fn uint8_constant(value: u32) -> CExpressionOutcome {
    CExpressionOutcome::Value(CValue::UInt8(Bitvector32Term::Constant(value)))
}

#[test]
fn byte_stores_complete_declared_uint32_and_preserve_byte_observations() {
    let mut memory = CMemory::new().with_declared_scalar_block(word(0).block, 4, CType::UInt32);
    // Out-of-order stores must not treat a partial representation as a word.
    for (offset, byte) in [(3, 0xFF), (1, 0x80), (0, 0x11)] {
        memory = store_byte(
            memory,
            offset,
            CValue::UInt8(byte.into()),
            ByteOrder::Little,
        );
        assert!(!matches!(
            memory.known_value(&word(0)),
            Some(CValue::UInt32(_))
        ));
    }
    memory = store_byte(
        memory,
        2,
        CValue::Int8(0xFFFF_FFEEu32.into()),
        ByteOrder::Little,
    );
    assert_eq!(
        memory.known_value(&word(0)),
        Some(CValue::UInt32(0xFFEE_8011u32.into()))
    );
    assert_eq!(memory.cells.len(), 1);
    for (offset, byte) in [(0, 0x11), (1, 0x80), (2, 0xEE), (3, 0xFF)] {
        assert_eq!(
            load_byte(&memory, offset, CType::UInt8, Some(ByteOrder::Little)),
            uint8_constant(byte)
        );
    }
    memory = store_byte(memory, 1, CValue::UInt8(7u32.into()), ByteOrder::Little);
    assert_eq!(
        memory.known_value(&word(0)),
        Some(CValue::UInt32(0xFFEE_0711u32.into()))
    );
}

#[test]
fn byte_assembly_refuses_untyped_other_types_missing_bytes_and_other_orders() {
    use crate::kernel::eval::assemble_declared_uint32_after_byte_store as assemble;
    let prefix = |mut memory: CMemory| {
        for byte in 0..3 {
            memory = memory.store(word(byte), CValue::UInt8(1u32.into()));
        }
        memory
    };
    let typed = prefix(CMemory::new().with_declared_scalar_block(word(0).block, 4, CType::UInt32));
    let incoming = CValue::UInt8(2u32.into());
    assert!(assemble(&typed, &word(3), &incoming, Some(ByteOrder::Little)).is_some());
    for order in [None, Some(ByteOrder::Big)] {
        assert!(assemble(&typed, &word(3), &incoming, order).is_none());
    }
    for memory in [
        prefix(CMemory::new().with_block(word(0).block, 4)),
        prefix(CMemory::new().with_declared_scalar_block(word(0).block, 4, CType::Int32)),
        prefix(CMemory::new().with_declared_scalar_block(word(0).block, 8, CType::UInt64)),
        CMemory::new()
            .with_declared_scalar_block(word(0).block, 4, CType::UInt32)
            .store(word(0), CValue::UInt8(1u32.into())),
        typed.without_local_block(&word(0).block),
    ] {
        assert!(assemble(&memory, &word(3), &incoming, Some(ByteOrder::Little)).is_none());
    }
    assert!(assemble(&typed, &word(4), &incoming, Some(ByteOrder::Little)).is_none());
    assert!(
        assemble(
            &typed,
            &word(3),
            &CValue::UInt32(2u32.into()),
            Some(ByteOrder::Little)
        )
        .is_none()
    );
}

#[test]
fn byte_assembly_masks_symbolic_bytes_and_ignores_unrelated_memory() {
    use crate::kernel::eval::assemble_declared_uint32_after_byte_store as assemble;
    let mut samples = Vec::new();
    for size in [0, 64, 128, 512] {
        let mut memory = CMemory::new().with_declared_scalar_block(word(0).block, 4, CType::UInt32);
        for byte in 0..3 {
            memory = memory.store(
                word(byte),
                CValue::UInt8(Bitvector32Term::Variable(Variable(8000 + byte as u64))),
            );
        }
        for index in 0..size {
            memory = memory.with_block(format!("global:other{index}"), 4).store(
                Pointer {
                    block: format!("global:other{index}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                CValue::UInt32(index.into()),
            );
        }
        let incoming = CValue::UInt8(Bitvector32Term::Variable(Variable(8003)));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            assemble(&memory, &word(3), &incoming, Some(ByteOrder::Little))
        });
        let mut expected = Bitvector32Term::Constant(0);
        for byte in 0u32..4 {
            expected = Bitvector32Term::bitwise_or(
                expected,
                Bitvector32Term::unsigned_shift_left(
                    Bitvector32Term::bitwise_and(
                        Bitvector32Term::Variable(Variable(8000 + u64::from(byte))),
                        0xFFu32.into(),
                    ),
                    (8 * byte).into(),
                ),
            );
        }
        assert_eq!(result, Some((word(0), CValue::UInt32(expected))));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

/// Whether a load produced a constant byte, which only the byte view (or an
/// exact one-byte cell) can do in these memories.
fn is_constant_byte(outcome: &CExpressionOutcome) -> bool {
    matches!(
        outcome,
        CExpressionOutcome::Value(CValue::UInt8(Bitvector32Term::Constant(_)))
    )
}

fn is_load_type_mismatch(outcome: &CExpressionOutcome) -> bool {
    matches!(
        outcome,
        CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch { .. })
    )
}

#[test]
fn byte_loads_read_each_little_endian_byte_of_a_constant_uint32_cell() {
    let memory = CMemory::new().store(word(0), CValue::UInt32(0x4433_2211.into()));
    for (offset, expected) in [(0, 0x11), (1, 0x22), (2, 0x33), (3, 0x44)] {
        assert_eq!(
            load_byte(&memory, offset, CType::UInt8, Some(ByteOrder::Little)),
            uint8_constant(expected),
            "byte {offset}"
        );
    }
}

#[test]
fn byte_loads_read_each_little_endian_byte_of_constant_64_bit_cells() {
    let bits = 0x8877_6655_4433_2211_u64;
    for cell in [
        CValue::UInt64(Bitvector32Term::UInt64Constant(bits)),
        CValue::Int64(Bitvector32Term::Int64Constant(bits as i64)),
    ] {
        let memory = CMemory::new().store(word(0), cell.clone());
        for offset in 0..8 {
            assert_eq!(
                load_byte(&memory, offset, CType::UInt8, Some(ByteOrder::Little)),
                uint8_constant(((bits >> (8 * offset)) & 0xFF) as u32),
                "{cell:?} byte {offset}"
            );
        }
    }
}

#[test]
fn byte_loads_of_symbolic_cells_extract_the_shifted_masked_byte() {
    let value = Bitvector32Term::Variable(Variable(7301));
    let memory = CMemory::new().store(word(0), CValue::UInt32(value.clone()));
    assert_eq!(
        load_byte(&memory, 2, CType::UInt8, Some(ByteOrder::Little)),
        CExpressionOutcome::Value(CValue::UInt8(Bitvector32Term::BitwiseAnd(
            Box::new(Bitvector32Term::LogicalShiftRight(
                Box::new(value.clone()),
                Box::new(Bitvector32Term::Constant(16)),
            )),
            Box::new(Bitvector32Term::Constant(0xFF)),
        )))
    );

    let wide = Bitvector32Term::Variable(Variable(7302));
    let memory = CMemory::new().store(word(0), CValue::UInt64(wide.clone()));
    assert_eq!(
        load_byte(&memory, 5, CType::UInt8, Some(ByteOrder::Little)),
        CExpressionOutcome::Value(CValue::UInt8(Bitvector32Term::UInt32From64(Box::new(
            Bitvector32Term::UInt64BitwiseAnd(
                Box::new(Bitvector32Term::UInt64LogicalShiftRight(
                    Box::new(wide),
                    Box::new(Bitvector32Term::UInt64Constant(40)),
                )),
                Box::new(Bitvector32Term::UInt64Constant(0xFF)),
            )
        ))))
    );

    // The same extraction folds to the byte once the value is known.
    let cell = ContainingIntegerCell {
        pointer: word(0),
        value: CValue::UInt32(0xA1B2_C3D4.into()),
        byte: 1,
    };
    assert_eq!(
        integer_cell_byte(&cell.value, cell.byte),
        Some(Bitvector32Term::Constant(0xC3))
    );
}

#[test]
fn signed_byte_loads_sign_extend_a_constant_byte_and_refuse_a_symbolic_one() {
    let memory = CMemory::new().store(word(0), CValue::UInt32(0x0000_7F80.into()));
    assert_eq!(
        load_byte(&memory, 0, CType::Int8, Some(ByteOrder::Little)),
        CExpressionOutcome::Value(CValue::Int8(Bitvector32Term::Constant(0xFFFF_FF80)))
    );
    assert_eq!(
        load_byte(&memory, 1, CType::Int8, Some(ByteOrder::Little)),
        CExpressionOutcome::Value(CValue::Int8(Bitvector32Term::Constant(0x7F)))
    );
    let symbolic = CMemory::new().store(
        word(0),
        CValue::UInt32(Bitvector32Term::Variable(Variable(7303))),
    );
    assert!(is_load_type_mismatch(&load_byte(
        &symbolic,
        1,
        CType::Int8,
        Some(ByteOrder::Little)
    )));
}

#[test]
fn byte_stores_update_the_containing_uint32_cell_in_place() {
    for (offset, expected) in [
        (0, 0x4433_22AB_u32),
        (1, 0x4433_AB11),
        (2, 0x44AB_2211),
        (3, 0xAB33_2211),
    ] {
        let memory = CMemory::new().store(word(0), CValue::UInt32(0x4433_2211.into()));
        let after = store_byte(
            memory,
            offset,
            CValue::UInt8(0xAB.into()),
            ByteOrder::Little,
        );
        assert_eq!(
            after.known_value(&word(0)),
            Some(CValue::UInt32(Bitvector32Term::Constant(expected))),
            "byte {offset}"
        );
        // The updated cell is the only description of this storage.
        for other in 1..4 {
            assert_eq!(after.known_value(&word(other)), None, "byte {offset}");
        }
        assert_eq!(
            load_byte(&after, offset, CType::UInt8, Some(ByteOrder::Little)),
            uint8_constant(0xAB)
        );
    }
}

#[test]
fn byte_stores_update_the_containing_uint64_cell_in_place() {
    let bits = 0x8877_6655_4433_2211_u64;
    for offset in 0..8 {
        let memory = CMemory::new().store(
            word(0),
            CValue::UInt64(Bitvector32Term::UInt64Constant(bits)),
        );
        let after = store_byte(memory, offset, CValue::UInt8(0.into()), ByteOrder::Little);
        assert_eq!(
            after.known_value(&word(0)),
            Some(CValue::UInt64(Bitvector32Term::UInt64Constant(
                bits & !(0xFF << (8 * offset))
            ))),
            "byte {offset}"
        );
    }
}

#[test]
fn byte_stores_into_a_symbolic_uint32_cell_keep_the_other_bytes() {
    let value = Bitvector32Term::Variable(Variable(7304));
    let memory = CMemory::new().store(word(0), CValue::UInt32(value.clone()));
    let after = store_byte(memory, 1, CValue::UInt8(0x5A.into()), ByteOrder::Little);
    assert_eq!(
        after.known_value(&word(0)),
        Some(CValue::UInt32(Bitvector32Term::BitwiseOr(
            Box::new(Bitvector32Term::BitwiseAnd(
                Box::new(value),
                Box::new(Bitvector32Term::Constant(0xFFFF_00FF)),
            )),
            Box::new(Bitvector32Term::Constant(0x5A00)),
        )))
    );
}

#[test]
fn big_endian_and_uninstalled_byte_orders_have_no_byte_view() {
    let memory = CMemory::new().store(word(0), CValue::UInt32(0x4433_2211.into()));
    for byte_order in [Some(ByteOrder::Big), None] {
        assert!(is_load_type_mismatch(&load_byte(
            &memory,
            0,
            CType::UInt8,
            byte_order
        )));
        assert!(
            !is_constant_byte(&load_byte(&memory, 1, CType::UInt8, byte_order)),
            "{byte_order:?}"
        );
        assert_eq!(containing_integer_cell(&memory, &word(1), byte_order), None);
    }
    // A big-endian store keeps today's behavior: the wider cell is forgotten.
    let after = store_byte(memory, 1, CValue::UInt8(0xAB.into()), ByteOrder::Big);
    assert_eq!(after.known_value(&word(0)), None);
    assert_eq!(
        after.known_value(&word(1)),
        Some(CValue::UInt8(Bitvector32Term::Constant(0xAB)))
    );
}

#[test]
fn pointer_cells_have_no_byte_view() {
    let target = Pointer {
        block: PointerBlock::from("global:target"),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().store(word(0), CValue::typed_pointer(target, CType::Int32Pointer));
    for offset in [0, 1, 7] {
        assert_eq!(
            containing_integer_cell(&memory, &word(offset), Some(ByteOrder::Little)),
            None
        );
        let outcome = load_byte(&memory, offset, CType::UInt8, Some(ByteOrder::Little));
        assert!(!is_constant_byte(&outcome), "byte {offset}: {outcome:?}");
        if offset == 0 {
            assert!(is_load_type_mismatch(&outcome), "{outcome:?}");
        }
    }
    let after = store_byte(memory, 1, CValue::UInt8(0.into()), ByteOrder::Little);
    assert_eq!(after.known_value(&word(0)), None);
}

#[test]
fn a_one_byte_cell_is_read_as_its_own_access() {
    let memory = CMemory::new().store(word(1), CValue::UInt8(9.into()));
    assert_eq!(
        containing_integer_cell(&memory, &word(1), Some(ByteOrder::Little)),
        None
    );
    assert_eq!(
        load_byte(&memory, 1, CType::UInt8, Some(ByteOrder::Little)),
        uint8_constant(9)
    );
}

#[test]
fn containing_cell_lookup_work_is_independent_of_unrelated_cells() {
    let mut works = Vec::new();
    for unrelated in [8_u32, 32, 128, 512] {
        let mut memory = CMemory::new().store(
            word(0),
            CValue::UInt64(Bitvector32Term::UInt64Constant(0x0102_0304_0506_0708)),
        );
        for index in 0..unrelated {
            memory = memory.store(
                Pointer {
                    block: PointerBlock::from(format!("global:unrelated{index}").as_str()),
                    offset: PointerOffsetTerm::Constant(0),
                },
                CValue::UInt32(index.into()),
            );
            // Cells after the access in the same block are outside the range.
            memory = memory.store(word(8 + 4 * i64::from(index)), CValue::UInt32(index.into()));
        }
        let (cell, work) = crate::instrumentation::measure_deterministic_work(|| {
            containing_integer_cell(&memory, &word(6), Some(ByteOrder::Little))
        });
        assert_eq!(cell.map(|cell| cell.byte), Some(6));
        works.push(work);
    }
    assert!(
        works.windows(2).all(|pair| pair[0] == pair[1]),
        "containing-cell lookup work grew with unrelated cells: {works:?}"
    );
}

#[test]
fn initialized_range_checks_all_bytes_and_cannot_reuse_an_expired_snapshot() {
    let base = Pointer {
        block: "local:output".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut memory = CMemory::new().with_uninitialized_block(base.block.clone(), 4);
    let facts = PureFactContext::new();
    let claim = |memory: &CMemory, bytes| Proposition::CMemoryInitialized {
        memory: memory.clone(),
        base: base.clone(),
        bytes,
    };
    assert!(!facts.proves(&claim(&memory, 4)));
    for index in 0..3 {
        memory = memory.store(base.offset_by_bytes(index), CValue::UInt8(index.into()));
    }
    assert!(facts.proves(&claim(&memory, 3)));
    assert!(!facts.proves(&claim(&memory, 4)));
    memory = memory.store(base.offset_by_bytes(3), CValue::UInt8(18.into()));
    assert!(facts.proves(&claim(&memory, 4)));
    let old = claim(&memory, 4);
    let retired = memory.without_local_block(&base.block);
    assert!(!facts.assume_proposition(old).proves(&claim(&retired, 4)));
}

#[test]
fn initialized_range_work_is_independent_of_unrelated_memory() {
    let mut samples = Vec::new();
    for count in [8u32, 32, 128, 512] {
        let base = Pointer {
            block: "local:output".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut memory = CMemory::new()
            .with_uninitialized_block(base.block.clone(), 4)
            .store(base.clone(), CValue::UInt32(7.into()));
        for index in 0..count {
            let block: PointerBlock = format!("global:unrelated{index}").into();
            memory = memory.with_block(block.clone(), 4).store(
                Pointer {
                    block,
                    offset: PointerOffsetTerm::Constant(0),
                },
                CValue::UInt32(index.into()),
            );
        }
        let (holds, work) = crate::instrumentation::measure_deterministic_work(|| {
            PureFactContext::new().proves(&Proposition::CMemoryInitialized {
                memory: memory.clone(),
                base,
                bytes: 4,
            })
        });
        assert!(holds);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
}

#[test]
fn initialized_output_is_not_a_bodyless_external_guarantee() {
    let function = c_function(
        CType::Void,
        "external_output",
        vec![c_parameter("p", CType::UInt8Pointer)],
        c_return(c_void_value()),
    );
    let claims = vec![
        CFunctionContractClaim::body_safety(),
        CFunctionContractClaim::ensure_proposition(0, 0),
    ];
    let ordinary = function.clone().with_contract(
        vec![],
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_int32_literal(0)),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_int32_literal(0)),
        }],
        vec![],
        claims.clone(),
        true,
    );
    assert!(c_external_function_rule(ordinary).is_some());
    let function = function.with_contract(
        vec![],
        vec![SpecProposition::MemoryInitialized {
            memory: SpecMemory::Current,
            base: SpecExpression::LoopEntrySnapshot(Box::new(SpecExpression::CExpression(
                c_variable("p"),
            ))),
            bytes: 1,
        }],
        vec![],
        claims,
        true,
    );
    assert_eq!(
        function.contract_interface().initialization_outputs(),
        Some(vec![(0, 1)])
    );
    assert!(CFunctionContract::new("OutputCallback", function.clone()).is_none());
    assert!(c_external_function_rule(function).is_none());
}

#[test]
fn proof_entry_naming_preserves_a_large_unwritten_output_without_enumeration() {
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(7430)),
    };
    let memory = CMemory::new().with_uninitialized_object(base.clone(), u32::MAX);
    let source = crate::kernel::intern_c_memory(memory.clone());
    let (named, work) = crate::instrumentation::measure_deterministic_work(|| {
        memory.with_proof_entry_cells(base.clone(), 1, CType::UInt8, 0, u32::MAX, source)
    });
    assert!(named.known_value(&base).is_none());
    assert!(!named.has_initialized_bytes_at(&base, 1));
    assert!(
        work < 20,
        "unwritten output naming enumerated bytes: {work}"
    );
}

#[test]
fn raw_output_overlap_respects_checked_input_separation() {
    let output = Pointer::symbolic(Variable(7431));
    let input = Pointer::symbolic(Variable(7432));
    let memory = CMemory::new().with_uninitialized_object(output.clone(), 4);
    let facts = PureFactContext::new();
    assert!(memory.may_read_uninitialized_object_under(&input, 4, &facts));
    let range = |base| {
        CResource::Memory(CMemoryRange::new_with_element_width(
            base,
            0u32.into(),
            4u32.into(),
            1,
        ))
    };
    let facts = facts.assume_proposition(Proposition::CResourceSeparate {
        left: Box::new(range(output.clone())),
        right: Box::new(range(input.clone())),
    });
    assert!(!memory.may_read_uninitialized_object_under(&input, 4, &facts));
    assert!(memory.may_read_uninitialized_object_under(&output, 4, &facts));
    assert!(!memory.has_initialized_bytes_under(&output, 4, &facts));
    assert!(memory.may_read_uninitialized_object_under(&input.offset_by_bytes(4), 1, &facts));
}

#[test]
fn raw_padding_is_not_separated_by_field_ownership() {
    let output = Pointer::symbolic(Variable(7433));
    let input = Pointer::symbolic(Variable(7434));
    let memory = CMemory::new().with_uninitialized_object(output.clone(), 16);
    let owner = |base, width| {
        CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            base,
            0u32.into(),
            1u32.into(),
            width,
        ))
    };
    let fields = ResourceContext::new().unchecked_with_facts([
        owner(output.clone(), 8),
        owner(output.offset_by_bytes(8), 4),
        owner(input.clone(), 4),
    ]);
    let fields =
        PureFactContext::new().assume_proposition(Proposition::CResourceComposition(fields));
    assert!(memory.may_read_uninitialized_object_under(&input, 4, &fields));
    assert!(memory.may_read_uninitialized_object_under(&output.offset_by_bytes(12), 4, &fields));
    assert!(!memory.has_initialized_bytes_under(&output.offset_by_bytes(12), 4, &fields));
}

#[test]
fn checked_entry_naming_preserves_raw_output_and_scales_with_selected_input() {
    let _session = crate::kernel::VerificationSession::enter();
    let external = |variable| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(variable)),
    };
    let output = external(7435);
    let input = external(7436);
    let mut costs = Vec::new();
    for count in [16u32, 64, 256, 1024] {
        let owner = |base, width, count: u32| {
            CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                base,
                0u32.into(),
                count.into(),
                width,
            ))
        };
        let mut facts = PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                output.clone(),
                0u32.into(),
                1u32.into(),
                4,
            ))),
            right: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                input.clone(),
                0u32.into(),
                count.into(),
                4,
            ))),
        });
        let mut memory = CMemory::new();
        for index in 0..count {
            let unrelated = external(7500 + u64::from(index));
            let resources =
                ResourceContext::new().unchecked_with_fact(owner(unrelated.clone(), 4, 1));
            facts = facts.assume_proposition(Proposition::CResourceComposition(resources));
            memory = memory.materialize_named_cell_under(
                unrelated.clone(),
                CValue::Int32(index.into()),
                &PureFactContext::new(),
            );
        }
        memory = memory
            .with_named_cell_run(
                external(10000),
                4,
                CType::Int32,
                0,
                count * count,
                crate::kernel::intern_c_memory(CMemory::new()),
            )
            .unwrap_or_else(|_| panic!("unrelated named run"));
        let memory = memory.with_uninitialized_object(output.clone(), 4);
        let source = crate::kernel::intern_c_memory(memory.clone());
        let (named, cost) = crate::instrumentation::measure_deterministic_work(|| {
            memory.with_proof_entry_cells_under(
                input.clone(),
                4,
                CType::Int32,
                0,
                count,
                source,
                &facts,
            )
        });
        assert!(matches!(named.load(&input), CExpressionOutcome::Value(_)));
        assert!(matches!(
            named.load(&input.offset_by_bytes(4 * (count - 1))),
            CExpressionOutcome::Value(_)
        ));
        assert!(named.known_value(&output).is_none());
        assert!(!named.has_initialized_bytes_under(&output, 4, &facts));
        let output_named = named.clone().materialize_named_cell_under(
            output.clone(),
            CValue::Int32(7u32.into()),
            &facts,
        );
        assert!(output_named.known_value(&output).is_none());
        costs.push(cost);
    }
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

#[test]
fn checked_entry_naming_preserves_selected_cells_and_intersecting_runs() {
    let _session = crate::kernel::VerificationSession::enter();
    let output = Pointer::symbolic(Variable(7437));
    let input = Pointer::symbolic(Variable(7438));
    let facts = PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
            output.clone(),
            0u32.into(),
            1u32.into(),
            4,
        ))),
        right: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
            input.clone(),
            0u32.into(),
            4u32.into(),
            4,
        ))),
    });
    for (shift, stride) in [(8, 4), (4, 8)] {
        let memory = CMemory::new()
            .with_named_cell_run(
                input.offset_by_bytes(shift),
                stride,
                CType::Int32,
                0,
                1_000_000,
                crate::kernel::intern_c_memory(CMemory::new()),
            )
            .unwrap_or_else(|_| panic!("existing run"))
            .materialize_named_cell(input.clone(), CValue::Int32(9u32.into()))
            .with_uninitialized_object(output.clone(), 4);
        let selected_value = memory.load(&input.offset_by_bytes(shift));
        let last_value = memory.load(&input.offset_by_bytes(12));
        let source = crate::kernel::intern_c_memory(memory.clone());
        let (named, cost) = crate::instrumentation::measure_deterministic_work(|| {
            memory.with_proof_entry_cells_under(
                input.clone(),
                4,
                CType::Int32,
                0,
                4,
                source,
                &facts,
            )
        });
        assert_eq!(
            named.load(&input),
            CExpressionOutcome::Value(CValue::Int32(9u32.into()))
        );
        assert_eq!(named.load(&input.offset_by_bytes(shift)), selected_value);
        assert_eq!(named.load(&input.offset_by_bytes(12)), last_value);
        assert!(
            cost < 100,
            "enumerated the remainder of the existing run: {cost}"
        );
        assert!(!named.has_initialized_bytes_under(&output, 4, &facts));
    }
}

#[test]
fn checked_entry_naming_ignores_run_holes_before_selected_start() {
    let _session = crate::kernel::VerificationSession::enter();
    let input = Pointer::symbolic(Variable(7439));
    let output = Pointer::symbolic(Variable(7440));
    let first = 900_000u32;
    let end = first + 4;
    let selected = input.offset_by_bytes(first * 4);
    let facts = PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
            output.clone(),
            0u32.into(),
            1u32.into(),
            4,
        ))),
        right: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
            input.clone(),
            first.into(),
            end.into(),
            4,
        ))),
    });
    let mut costs = Vec::new();
    for holes in [16u32, 64, 256, 1024] {
        let mut memory = CMemory::new()
            .with_named_cell_run(
                input.clone(),
                4,
                CType::Int32,
                0,
                1_000_000,
                crate::kernel::intern_c_memory(CMemory::new()),
            )
            .unwrap_or_else(|_| panic!("existing run"));
        for index in 0..holes {
            memory = memory.without_cell(&input.offset_by_bytes(index * 8));
        }
        let memory = memory.with_uninitialized_object(output.clone(), 4);
        let expected = memory.load(&selected);
        let source = crate::kernel::intern_c_memory(memory.clone());
        let (named, cost) = crate::instrumentation::measure_deterministic_work(|| {
            memory.with_proof_entry_cells_under(
                input.clone(),
                4,
                CType::Int32,
                first,
                end,
                source,
                &facts,
            )
        });
        assert_eq!(named.load(&selected), expected);
        assert!(named.known_value(&input).is_none());
        assert!(!named.has_initialized_bytes_under(&output, 4, &facts));
        costs.push(cost);
    }
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

#[test]
fn checked_entry_naming_preserves_distinct_nested_slot_spellings() {
    let _session = crate::kernel::VerificationSession::enter();
    let input = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(7441)),
    };
    let output = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(7442)),
    };
    let canonical = input.offset_by_bytes(8);
    let nested = Pointer {
        block: input.block.clone(),
        offset: PointerOffsetTerm::Add(
            Box::new(input.offset_by_bytes(4).offset),
            Box::new(PointerOffsetTerm::Constant(4)),
        ),
    };
    let cancellation = Pointer {
        block: input.block.clone(),
        offset: PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Add(
                Box::new(input.offset_by_bytes(2).offset),
                Box::new(PointerOffsetTerm::Constant(2)),
            )),
            Box::new(PointerOffsetTerm::Constant(-4)),
        ),
    };
    for (old, selected) in [
        (&nested, &canonical),
        (&canonical, &nested),
        (&cancellation, &input),
    ] {
        let memory = CMemory::new()
            .with_named_cell_run(
                old.clone(),
                4,
                CType::Int32,
                0,
                1_000_000,
                crate::kernel::intern_c_memory(CMemory::new()),
            )
            .unwrap_or_else(|_| panic!("existing run"))
            .with_uninitialized_object(output.clone(), 4);
        assert!(memory.known_value(selected).is_none());
        let old_first = memory.load(old);
        let old_second = memory.load(&old.offset_by_bytes(4));
        let next = memory.load(&selected.offset_by_bytes(4));
        let facts = PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                output.clone(),
                0u32.into(),
                1u32.into(),
                4,
            ))),
            right: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                selected.clone(),
                0u32.into(),
                3u32.into(),
                4,
            ))),
        });
        let source = crate::kernel::intern_c_memory(memory.clone());
        let (named, cost) = crate::instrumentation::measure_deterministic_work(|| {
            memory.with_proof_entry_cells_under(
                selected.clone(),
                4,
                CType::Int32,
                0,
                3,
                source,
                &facts,
            )
        });
        assert!(
            named.known_value(selected).is_some(),
            "the selected spelling needs its own name"
        );
        assert_eq!(named.load(old), old_first);
        assert_eq!(named.load(&old.offset_by_bytes(4)), old_second);
        if matches!(next, CExpressionOutcome::Value(_)) {
            assert_eq!(named.load(&selected.offset_by_bytes(4)), next);
        } else {
            assert!(named.known_value(&selected.offset_by_bytes(4)).is_some());
        }
        assert!(!named.has_initialized_bytes_under(&output, 4, &facts));
        assert!(cost < 100, "enumerated unrelated run slots: {cost}");
    }
    for (selected, index) in [(&nested, 0), (&cancellation, 1)] {
        let point = selected.offset_by_bytes(index * 4);
        let value = CValue::Int32(9u32.into());
        let memory = CMemory::new()
            .materialize_named_cell(point.clone(), value.clone())
            .with_uninitialized_object(output.clone(), 4);
        let facts = PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                output.clone(),
                0u32.into(),
                1u32.into(),
                4,
            ))),
            right: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                selected.clone(),
                0u32.into(),
                3u32.into(),
                4,
            ))),
        });
        let source = crate::kernel::intern_c_memory(memory.clone());
        let named = memory.with_proof_entry_cells_under(
            selected.clone(),
            4,
            CType::Int32,
            0,
            3,
            source,
            &facts,
        );
        assert_eq!(named.known_value(&point), Some(value));
        assert_eq!(
            named.cells.len(),
            3,
            "existing concrete slots must not be named again"
        );
        assert!(!named.has_initialized_bytes_under(&output, 4, &facts));
    }
}
/// C11 6.5p7: a character load of a one-byte cell of the other signedness
/// reads the same eight bits. Constants fold to the reinterpreted value in
/// both directions; a symbolic cell keeps an explicit modular conversion of
/// its own term, never a fresh unrelated value.
#[test]
fn character_loads_read_a_one_byte_cell_of_the_other_signedness_as_its_bits() {
    let int8 = |value: i8| CValue::Int8(Bitvector32Term::Constant(value as i32 as u32));
    let uint8 = |value: u8| CValue::UInt8(Bitvector32Term::Constant(u32::from(value)));
    for byte in [0u8, 1, 0x7F, 0x80, 0xC8, 0xFF] {
        assert_eq!(CType::UInt8.read_cell(&int8(byte as i8)), Some(uint8(byte)));
        assert_eq!(CType::Int8.read_cell(&uint8(byte)), Some(int8(byte as i8)));
        assert_eq!(
            CType::Int8.read_cell(&int8(byte as i8)),
            Some(int8(byte as i8))
        );
        assert_eq!(
            LoadKind::UInt8.read_cell(&int8(byte as i8)),
            Some(uint8(byte))
        );
        assert_eq!(
            LoadKind::Int8.read_cell(&uint8(byte)),
            Some(int8(byte as i8))
        );
    }
    let variable = Bitvector32Term::Variable(Variable(613_001));
    assert_eq!(
        CType::UInt8.read_cell(&CValue::Int8(variable.clone())),
        Some(CValue::UInt8(Bitvector32Term::machine_integer_cast(
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            variable.clone(),
        )))
    );
    // Reading back through the original signedness is the original term.
    let Some(CValue::Int8(round_trip)) = CType::UInt8
        .read_cell(&CValue::Int8(variable.clone()))
        .and_then(|value| CType::Int8.read_cell(&value))
    else {
        panic!("a character round trip reads a signed byte");
    };
    assert_eq!(round_trip, variable);
    // No other cell gains a character view: wider integers go through the
    // byte view, and bool, pointer, and float cells stay refused.
    for (load, stored) in [
        (CType::UInt8, CValue::Int16(Bitvector32Term::Constant(1))),
        (CType::Int8, CValue::Bool(Bitvector32Term::Constant(1))),
        (CType::UInt8, CValue::Float32(Bitvector32Term::Constant(0))),
        (CType::Int16, CValue::UInt16(Bitvector32Term::Constant(1))),
        (CType::UInt16, CValue::Int8(Bitvector32Term::Constant(1))),
    ] {
        assert_eq!(load.read_cell(&stored), None, "{load:?} of {stored:?}");
    }
}

/// The execution load path applies the rule: a cell stored as `signed char`
/// is read through `unsigned char` as its bits, and the reverse.
#[test]
fn execution_loads_read_character_cells_of_the_other_signedness() {
    let memory = CMemory::new()
        .store(
            word(0),
            CValue::Int8(Bitvector32Term::Constant(-56i32 as u32)),
        )
        .store(word(1), CValue::UInt8(Bitvector32Term::Constant(200)));
    assert_eq!(
        load_byte(&memory, 0, CType::UInt8, Some(ByteOrder::Little)),
        CExpressionOutcome::Value(CValue::UInt8(Bitvector32Term::Constant(200)))
    );
    assert_eq!(
        load_byte(&memory, 1, CType::Int8, Some(ByteOrder::Little)),
        CExpressionOutcome::Value(CValue::Int8(Bitvector32Term::Constant(-56i32 as u32)))
    );
}
