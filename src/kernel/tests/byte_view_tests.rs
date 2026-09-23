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
        Vec::new(),
        Vec::new(),
        &PureFactContext::new(),
        false,
        None,
        byte_order,
    );
    assert_eq!(paths.len(), 1, "{paths:?}");
    paths[0].outcome.clone()
}

fn store_byte(memory: CMemory, offset: i64, byte: CValue, byte_order: ByteOrder) -> CMemory {
    let state = CState::new().with_memory(memory);
    let statement = CStatement::TypedStore {
        pointer: CExpression::Value(CValue::typed_pointer(word(offset), CType::UInt8Pointer)),
        value: CExpression::Value(byte),
        value_type: CType::UInt8,
        volatile: false,
        pointee_constant: false,
    };
    let paths = execute_c_statement_paths(
        &state,
        &statement,
        &PureFactContext::new(),
        &CExecutionEnvironment::new().with_byte_order(byte_order),
        CExecutionSemantics::EXECUTE_BODIES,
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
