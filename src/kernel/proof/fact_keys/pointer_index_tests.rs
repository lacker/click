use super::*;
use crate::kernel::{
    KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, MachineOperandView as V,
    SharedMachineIntegerTerm, VerificationSession,
};

fn retained(ty: MachineIntegerType, term: &MachineTerm) -> SharedMachineIntegerTerm {
    SharedMachineIntegerTerm::from_shared(
        ty,
        KernelTerm::retained_machine_operand(ty, V::Legacy(term)),
    )
    .unwrap()
}
fn offset(value: SharedMachineIntegerTerm, width: i64, unsigned: bool) -> PointerOffsetTerm {
    if matches!(
        value.ty(),
        MachineIntegerType::Int32 | MachineIntegerType::UInt32
    ) {
        PointerOffsetTerm::Int32Scaled {
            value,
            byte_width: width,
        }
    } else {
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width: width,
            unsigned,
        }
    }
}
fn fact(offset: PointerOffsetTerm) -> Proposition {
    Proposition::ConditionIs(
        ConditionTerm::PointerOffsetEqual(
            Box::new(offset),
            Box::new(PointerOffsetTerm::Constant(0)),
        ),
        true,
    )
}
fn quantified(variable: Variable, offset: PointerOffsetTerm) -> Proposition {
    Proposition::ForAll {
        var: variable,
        name: crate::kernel::BinderName::written("index"),
        sort: Sort::ProgramInteger(MachineIntegerType::Int32),
        body: Box::new(fact(offset)),
    }
}
fn bindings() -> AlphaBindings {
    AlphaBindings {
        integer: BTreeMap::new(),
        bitvector: BTreeMap::new(),
        algebraic: BTreeMap::new(),
        integer_scope: 0,
        bitvector_scope: 0,
        next_scope_id: 1,
        state_aware: false,
        raw_state_load_seen: false,
        registered_load_stack: BTreeSet::new(),
        registered_load_memo: HashMap::new(),
        pointer_load_stack: BTreeSet::new(),
        pointer_load_memo: HashMap::new(),
        load_interner: None,
        work_units: 0,
    }
}

#[test]
fn pointer_index_keys_match_native_arithmetic_and_opaque_binders() {
    let _session = VerificationSession::enter();
    let x = MachineTerm::Variable(Variable(1019001));
    let fold = MachineTerm::RangeFold {
        start: MachineTerm::constant(0).into(),
        end: MachineTerm::constant(2).into(),
        initial: x.clone().into(),
        accumulator: Variable(1019002),
        item: Variable(1019003),
        body: MachineTerm::Variable(Variable(1019002)).into(),
    };
    for ty in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        for leaf in [
            x.clone(),
            fold.clone(),
            MachineTerm::If {
                condition: ConditionTerm::Variable(Variable(1019004)).into(),
                then_term: x.clone().into(),
                else_term: MachineTerm::constant(3).into(),
            },
        ] {
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::BitwiseAnd,
            ] {
                let term = MachineTerm::Binary {
                    format: ty,
                    op,
                    left: leaf.clone().into(),
                    right: leaf.clone().into(),
                };
                let leaf_root = KernelTerm::retained_machine_operand(ty, V::Legacy(&leaf));
                let root =
                    KernelTerm::machine_binary_shared(ty, op, [leaf_root.clone(), leaf_root]);
                let value = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
                let native = value.structural_value();
                let expected_state = memory_erased_bitvector_key(native);
                let expected_alpha =
                    alpha_machine_key::<true>(V::Legacy(native), &mut bindings(), &mut 0);
                let exports = KernelTermExport::machine_export_count();
                let actual_alpha =
                    alpha_machine_key::<true>(value.operand_view(), &mut bindings(), &mut 0);
                assert_eq!(expected_alpha, actual_alpha, "{term:?}");
                let key = memory_erased_pointer_offset_key(&offset(
                    value.clone(),
                    4,
                    ty == MachineIntegerType::UInt64,
                ));
                let (MemoryErasedPointerOffsetNode::Int32Scaled { value: actual, .. }
                | MemoryErasedPointerOffsetNode::Int64Scaled { value: actual, .. }) = key.node()
                else {
                    panic!("scaled key")
                };
                assert_eq!(actual, &expected_state);
                assert!(
                    proposition_identity_key(&fact(offset(
                        value,
                        4,
                        ty == MachineIntegerType::UInt64
                    )))
                    .is_some()
                );
                assert_eq!(exports, KernelTermExport::machine_export_count());
            }
        }
    }
}

#[test]
fn pointer_index_keys_preserve_quantifiers_free_variables_and_stride() {
    let _session = VerificationSession::enter();
    let build = |bound, free, width, unsigned, ty| {
        let term = MachineTerm::Binary {
            format: ty,
            op: MachineBinaryOp::Add,
            left: MachineTerm::Variable(Variable(bound)).into(),
            right: MachineTerm::Variable(Variable(free)).into(),
        };
        quantified(
            Variable(bound),
            offset(retained(ty, &term), width, unsigned),
        )
    };
    for ty in [
        MachineIntegerType::Int32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let a = build(1019010, 1019012, 4, false, ty);
        let b = build(1019011, 1019012, 4, false, ty);
        let exports = KernelTermExport::machine_export_count();
        assert!(propositions_are_alpha_equal(&a, &b));
        let facts = crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&a));
        assert_eq!(facts.matching_quantified_fact(&b), Some(a.clone()));
        for different in [
            build(1019011, 1019013, 4, false, ty),
            build(1019011, 1019012, 8, false, ty),
        ] {
            assert!(!propositions_are_alpha_equal(&a, &different));
            assert!(facts.matching_quantified_fact(&different).is_none());
        }
        if ty != MachineIntegerType::Int32 {
            assert!(!propositions_are_alpha_equal(
                &a,
                &build(1019011, 1019012, 4, true, ty)
            ));
        }
        assert_eq!(exports, KernelTermExport::machine_export_count());
    }
}

#[test]
fn pointer_index_keys_erase_states_only_for_candidate_selection() {
    let _session = VerificationSession::enter();
    let pointer = crate::kernel::Memory::global_pointer("key-read");
    let before = crate::kernel::Memory::new().with_block("key-read", 16);
    let after = before.clone().store(
        pointer.clone(),
        ProgramValue::Int32(MachineTerm::constant(7)),
    );
    let make = |memory, kind| {
        let load = MachineTerm::MemoryLoad(
            crate::kernel::intern_memory(memory),
            Box::new(pointer.clone()),
            kind,
        );
        let sum = MachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Add,
            left: load.clone().into(),
            right: load.into(),
        };
        fact(offset(retained(MachineIntegerType::Int32, &sum), 4, false))
    };
    let a = make(before.clone(), LoadKind::Int32);
    let b = make(after, LoadKind::Int32);
    let different_kind = make(before, LoadKind::UInt8);
    let exports = KernelTermExport::machine_export_count();
    let key = memory_erased_proposition_key(&a);
    assert_eq!(key, memory_erased_proposition_key(&b));
    assert!(key.requires_checked_match());
    assert_ne!(key, memory_erased_proposition_key(&different_kind));
    assert_ne!(
        proposition_identity_key(&a).unwrap(),
        proposition_identity_key(&b).unwrap()
    );
    assert!(alpha_proposition_key::<false>(&a, &mut BTreeMap::new(), &mut 0).is_none());
    assert_eq!(exports, KernelTermExport::machine_export_count());
}

#[test]
fn pointer_index_fold_keys_restore_shadowed_binders_and_keep_free_variables() {
    let _session = VerificationSession::enter();
    let make = |bound, item, free| {
        let ty = MachineIntegerType::Int32;
        let fold = MachineTerm::RangeFold {
            start: MachineTerm::constant(0).into(),
            end: MachineTerm::constant(2).into(),
            initial: MachineTerm::Variable(Variable(bound)).into(),
            accumulator: Variable(bound),
            item: Variable(item),
            body: MachineTerm::Binary {
                format: ty,
                op: MachineBinaryOp::Add,
                left: MachineTerm::Variable(Variable(bound)).into(),
                right: MachineTerm::Variable(Variable(free)).into(),
            }
            .into(),
        };
        let leaf = KernelTerm::retained_machine_operand(ty, V::Legacy(&fold));
        let repeated =
            KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [leaf.clone(), leaf]);
        let root = KernelTerm::machine_binary_shared(
            ty,
            MachineBinaryOp::Add,
            [
                repeated,
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(bound)),
            ],
        );
        quantified(
            Variable(bound),
            offset(
                SharedMachineIntegerTerm::from_shared(ty, root).unwrap(),
                4,
                false,
            ),
        )
    };
    let a = make(1019030, 1019031, 1019032);
    let b = make(1019033, 1019034, 1019032);
    let different = make(1019033, 1019034, 1019035);
    let exports = KernelTermExport::machine_export_count();
    assert!(propositions_are_alpha_equal(&a, &b));
    assert!(!propositions_are_alpha_equal(&a, &different));
    assert_eq!(exports, KernelTermExport::machine_export_count());
}

mod scaling_tests {
    use super::*;
    include!("../../../scaling_tests/kernel/proof/fact_keys/pointer_index_tests.rs");
}
