use super::*;
use crate::kernel::{KernelTermExport, KernelType, MachineBinaryOp};

fn retained(ty: MachineIntegerType, term: &MachineTerm) -> SharedMachineIntegerTerm {
    MachineOperandView::Shared(&KernelTerm::retained_machine_operand(
        ty,
        MachineOperandView::Legacy(term),
    ))
    .retain(ty)
}

#[test]
fn exact_coordinate_reconstruction_preserves_native_signed_shapes() {
    let _session = crate::kernel::VerificationSession::enter();
    use MachineIntegerType as T;
    let variable = MachineTerm::Variable(Variable(993100));
    for ty in [T::Int32, T::Int64, T::UInt64] {
        let constant = |n| match ty {
            T::Int32 => MachineTerm::constant(n as u32),
            T::Int64 => MachineTerm::int64_constant(n),
            T::UInt64 => MachineTerm::uint64_constant(n as u64),
            _ => unreachable!(),
        };
        let raw = |a, b| MachineTerm::Binary {
            format: ty,
            op: MachineBinaryOp::Add,
            left: Box::new(a),
            right: Box::new(b),
        };
        for value in [
            variable.clone(),
            constant(0),
            constant(1),
            constant(-1),
            raw(constant(2), constant(3)),
            raw(variable.clone(), constant(0)),
            raw(
                MachineTerm::If {
                    condition: Box::new(ConditionTerm::Constant(true)),
                    then_term: Box::new(constant(2)),
                    else_term: Box::new(constant(3)),
                },
                constant(5),
            ),
            raw(
                MachineTerm::If {
                    condition: Box::new(ConditionTerm::Variable(Variable(993102))),
                    then_term: Box::new(constant(2)),
                    else_term: Box::new(constant(3)),
                },
                constant(5),
            ),
        ] {
            for stride in [-4, 0, 1, 4] {
                let offset = if ty == T::Int32 {
                    PointerOffsetTerm::Int32Scaled {
                        value: retained(ty, &value),
                        byte_width: stride,
                    }
                } else {
                    PointerOffsetTerm::Int64Scaled {
                        value: retained(ty, &value),
                        byte_width: stride,
                        unsigned: ty == T::UInt64,
                    }
                };
                let mut guards = vec![];
                let exports = KernelTermExport::machine_export_count();
                let actual = exact_pointer_offset_i64_with_guards(&offset, &mut guards);
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                if ty == T::UInt64 && stride < 0 {
                    assert!(actual.is_none());
                    continue;
                }
                let expected = if ty != T::Int32 && stride == 0 {
                    MachineTerm::int64_constant(0)
                } else {
                    MachineTerm::int64_multiply(
                        if ty == T::Int32 {
                            MachineTerm::int64_from_32(value.clone())
                        } else {
                            value.clone()
                        },
                        MachineTerm::int64_constant(stride),
                    )
                };
                assert_eq!(
                    actual.unwrap().structural_value(),
                    &expected,
                    "{ty:?} {value:?} * {stride}"
                );
                assert!(
                    guards
                        .iter()
                        .all(|guard| !matches!(guard.condition, ConditionTerm::Overflows { .. }))
                );
            }
        }
    }
    assert!(
        exact_pointer_offset_i64_with_guards(
            &PointerOffsetTerm::Variable(Variable(993101)),
            &mut vec![],
        )
        .is_none()
    );
}

#[test]
fn exact_coordinate_guards_keep_full_width_and_overflow_refusals() {
    let _session = crate::kernel::VerificationSession::enter();
    use MachineIntegerType as T;
    let root = PureFactContext::new();
    for (value, stride, accepted) in [
        (i64::MAX as u64, 1, true),
        (1 << 32, 4, true),
        (1 << 63, 1, false),
        (i64::MAX as u64, 2, false),
    ] {
        let offset = PointerOffsetTerm::Int64Scaled {
            value: retained(T::UInt64, &MachineTerm::uint64_constant(value)),
            byte_width: stride,
            unsigned: true,
        };
        let mut guards = vec![];
        assert!(exact_pointer_offset_i64_with_guards(&offset, &mut guards).is_some());
        assert_eq!(
            guards
                .iter()
                .all(|g| root.decide(&g.condition) == Some(g.value)),
            accepted,
            "guards: {:?}",
            guards
                .iter()
                .map(|g| (&g.condition, g.value, root.decide(&g.condition)))
                .collect::<Vec<_>>()
        );
    }
    for (left, right, accepted) in [(i64::MAX, 1, false), (i64::MIN, -1, false), (17, 4, true)] {
        let offset = PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Constant(left)),
            Box::new(PointerOffsetTerm::Constant(right)),
        );
        let mut guards = vec![];
        let _ = exact_pointer_offset_i64_with_guards(&offset, &mut guards).unwrap();
        assert_eq!(
            guards
                .iter()
                .all(|g| root.decide(&g.condition) == Some(g.value)),
            accepted,
            "guards: {:?}",
            guards
                .iter()
                .map(|g| (&g.condition, g.value, root.decide(&g.condition)))
                .collect::<Vec<_>>()
        );
    }
}

#[test]
fn retained_block_bounds_require_the_full_index_and_preserve_missing_bounds() {
    let _session = crate::kernel::VerificationSession::enter();
    use MachineIntegerType as T;
    for ty in [T::Int64, T::UInt64] {
        let base = Pointer {
            block: PointerBlock::Concrete("retained-formation".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let state =
            ExecutionState::new().with_memory(Memory::new().with_block(base.block.clone(), 64));
        let variable = MachineTerm::Variable(Variable(993200));
        let pointer = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Int64Scaled {
                value: retained(ty, &variable),
                byte_width: 4,
                unsigned: ty == T::UInt64,
            },
        };
        let root = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let guards = pointer_block_bounds(&state, &pointer, 4, &root).unwrap();
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(guards.iter().any(|g| root.decide(&g.condition).is_none()));
        for n in [-1, 0, 16, 17, 1 << 32] {
            let literal = if ty == T::UInt64 {
                MachineTerm::uint64_constant(n as u64)
            } else {
                MachineTerm::int64_constant(n)
            };
            let context = root.clone().assume_condition(
                ConditionTerm::machine_compare(
                    ty,
                    CompareRelation::Equal,
                    variable.clone(),
                    literal,
                ),
                true,
            );
            assert_eq!(
                guards
                    .iter()
                    .all(|g| context.decide(&g.condition) == Some(g.value)),
                (0..=16).contains(&n)
            );
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/eval/operators/retained_formation_tests.rs");
}

#[test]
fn coordinate_reconstruction_keeps_the_selected_read_state() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer {
        block: PointerBlock::Concrete("coordinate-retained_state".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = Memory::new().with_block(pointer.block.clone(), 8).store(
        pointer.clone(),
        ProgramValue::Int64(MachineTerm::int64_constant(2)),
    );
    let after = before.clone().store(
        pointer.clone(),
        ProgramValue::Int64(MachineTerm::int64_constant(3)),
    );
    let mut results = vec![];
    for memory in [before, after] {
        let memory = crate::kernel::intern_memory(memory);
        let read =
            MachineTerm::MemoryLoad(memory.clone(), Box::new(pointer.clone()), LoadKind::Bits64);
        let offset = PointerOffsetTerm::Int64Scaled {
            value: retained(MachineIntegerType::Int64, &read),
            byte_width: 4,
            unsigned: false,
        };
        let exports = KernelTermExport::machine_export_count();
        let result = exact_pointer_offset_i64_with_guards(&offset, &mut vec![]).unwrap();
        let (_, _, [operand, _]) = result.operand_view().binary().unwrap();
        assert_eq!(operand.read().unwrap().0, &memory);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        results.push(result);
    }
    assert_ne!(results[0], results[1]);
}

#[test]
fn wide_block_bounds_keep_signed_extension_and_opaque_offset_refusals() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = MachineIntegerType::Int32;
    let extent = HeapExtent::new(MachineTerm::uint64_constant(64), HeapExtentKind::UInt64);
    let index = MachineTerm::Variable(Variable(993400));
    let offset = PointerOffsetTerm::Int32Scaled {
        value: retained(ty, &index),
        byte_width: 4,
    };
    let exports = KernelTermExport::machine_export_count();
    let guards = wide_block_bounds_of_32_bit_offset(&offset, &extent).unwrap();
    assert_eq!(KernelTermExport::machine_export_count(), exports);
    for n in [-1, 0, 16, 17] {
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::equal(index.clone(), MachineTerm::constant(n as u32)),
            true,
        );
        assert_eq!(
            guards
                .iter()
                .all(|g| context.decide(&g.condition) == Some(g.value)),
            (0..=16).contains(&n)
        );
    }
    assert!(wide_block_bounds_of_32_bit_offset(
        &PointerOffsetTerm::Variable(Variable(993401)), &extent,
    ).is_none());
}

#[test]
fn extension_constant_readings_keep_native_literal_requirements() {
    use MachineCastSpelling as E;
    use MachineIntegerType as T;
    let _session = crate::kernel::VerificationSession::enter();
    for (encoding, source, destination) in [
        (E::Int64From32, T::Int32, T::Int64),
        (E::Int64FromUInt32, T::UInt32, T::Int64),
        (E::UInt64From32, T::UInt32, T::UInt64),
        (E::UInt64FromInt32, T::Int32, T::UInt64),
        (E::UInt64FromInt64, T::Int64, T::UInt64),
    ] {
        let constant = |n| match source {
            T::Int64 => MachineTerm::int64_constant(n),
            T::UInt32 => MachineTerm::uint32_constant(n as u32),
            _ => MachineTerm::constant(n as u32),
        };
        for operand in [
            constant(3),
            MachineTerm::Binary {
                format: source,
                op: MachineBinaryOp::Add,
                left: Box::new(constant(1)),
                right: Box::new(constant(2)),
            },
        ] {
            let native = encoding.unary(source, destination).build_raw(operand);
            let shared = retained(destination, &native);
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(
                shared.operand_view().int64_constant(),
                native.int64_as_const()
            );
            assert_eq!(
                shared.operand_view().uint64_constant(),
                native.uint64_as_const()
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}

#[test]
fn widened_index_order_keeps_its_common_format_with_separate_bounds() {
    let _session = crate::kernel::VerificationSession::enter();
    use crate::kernel::machine_integer::comparison::comparison_view;
    use MachineIntegerType as T;
    let i = MachineTerm::Variable(Variable(993120));
    let n = MachineTerm::Variable(Variable(993121));
    let wide_i = retained(T::Int32, &i).checking_cast_operand(T::Int64);
    let query = formation_comparison(
        T::Int64,
        CompareRelation::LessEqual,
        wide_i.operand_view(),
        MachineOperandView::Legacy(&n),
    );
    assert_eq!(comparison_view(&query, true).unwrap().format, T::Int64);
    let native =
        ConditionTerm::int64_signed_less_equal(MachineTerm::int64_from_32(i.clone()), n.clone());
    let bounds = [
        ConditionTerm::signed_less_equal(MachineTerm::constant(0), i.clone()),
        ConditionTerm::signed_less_than(i, MachineTerm::constant(10)),
        ConditionTerm::machine_compare(
            T::UInt64,
            CompareRelation::LessEqual,
            MachineTerm::uint64_constant(10),
            n.clone(),
        ),
        ConditionTerm::machine_compare(
            T::UInt64,
            CompareRelation::LessEqual,
            n,
            MachineTerm::uint64_constant(100),
        ),
    ];
    let mut context = PureFactContext::new();
    for bound in bounds {
        context = context.assume_condition(bound, true);
    }
    let exports = KernelTermExport::machine_export_count();
    assert_eq!(context.decide(&native), Some(true));
    assert_eq!(context.decide(&query), Some(true));
    assert_eq!(KernelTermExport::machine_export_count(), exports);
    assert_eq!(PureFactContext::new().decide(&query), None);
}
