use super::*;
use crate::kernel::{
    KernelTerm, KernelTermExport, MachineBinaryOp, MachineCastSpelling, VerificationSession,
};

fn shared(value: &MachineTerm) -> KernelTerm {
    KernelTerm::retained_machine_operand(
        MachineIntegerType::Int32,
        MachineOperandView::Legacy(value),
    )
}
fn binary(
    format: MachineIntegerType,
    op: MachineBinaryOp,
    a: MachineTerm,
    b: MachineTerm,
) -> MachineTerm {
    MachineTerm::Binary {
        format,
        op,
        left: Box::new(a),
        right: Box::new(b),
    }
}
fn reads() -> [MachineTerm; 3] {
    let pointer = Pointer {
        block: "retained-retained_state".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new().with_block(pointer.block.clone(), 64).store(
        pointer.clone(),
        ProgramValue::Int32(MachineTerm::constant(2)),
    );
    let other = Pointer {
        block: pointer.block.clone(),
        offset: PointerOffsetTerm::Constant(32),
    };
    let separate = memory
        .clone()
        .store(other, ProgramValue::Int32(MachineTerm::constant(3)));
    let overlap = memory.clone().store(
        pointer.clone(),
        ProgramValue::Int32(MachineTerm::constant(3)),
    );
    [memory, separate, overlap].map(|memory| {
        MachineTerm::MemoryLoad(
            crate::kernel::intern_memory(memory),
            Box::new(pointer.clone()),
            LoadKind::Int32,
        )
    })
}
fn scaled(root: &KernelTerm) -> PointerOffsetTerm {
    PointerOffsetTerm::Int32Scaled {
        value: MachineOperandView::Shared(root).retain(MachineIntegerType::Int32),
        byte_width: 4,
    }
}

#[test]
fn state_indices_preserve_native_syntax_and_frame_limits() {
    let _session = VerificationSession::enter();
    let context = PureFactContext::new();
    let [before, separate, overlap] = reads();
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
    ] {
        for op in [
            MachineBinaryOp::Add,
            MachineBinaryOp::Subtract,
            MachineBinaryOp::Multiply,
            MachineBinaryOp::BitwiseAnd,
        ] {
            let left = binary(format, op, before.clone(), MachineTerm::constant(1));
            for (read, allowed) in [
                (&before, true),
                (
                    &separate,
                    format.format().bits() == 32 && op != MachineBinaryOp::BitwiseAnd,
                ),
                (&overlap, false),
            ] {
                let right = binary(format, op, read.clone(), MachineTerm::constant(1));
                assert_eq!(
                    context.bitvector_terms_state_equivalent(&left, &right),
                    allowed,
                    "native {format:?} {op:?}"
                );
                let (a, b) = (shared(&left), shared(&right));
                let exports = KernelTermExport::machine_export_count();
                for (a, b) in [
                    (
                        MachineOperandView::Shared(&a),
                        MachineOperandView::Shared(&b),
                    ),
                    (
                        MachineOperandView::Shared(&a),
                        MachineOperandView::Legacy(&right),
                    ),
                    (
                        MachineOperandView::Legacy(&left),
                        MachineOperandView::Shared(&b),
                    ),
                ] {
                    assert_eq!(
                        context.operands_state_equivalent(a, b),
                        allowed,
                        "{format:?} {op:?}"
                    );
                }
                assert_eq!(KernelTermExport::machine_export_count(), exports);
            }
        }
    }
    let cast = |value| MachineTerm::legacy_cast(MachineCastSpelling::Int64From32, Box::new(value));
    for (a, b, expected) in [
        (cast(before.clone()), cast(before.clone()), true),
        (cast(before.clone()), cast(separate.clone()), false),
        (
            MachineTerm::constant(1),
            MachineTerm::uint32_constant(1),
            false,
        ),
        (MachineTerm::Variable(Variable(994100)), before, false),
    ] {
        assert_eq!(context.bitvector_terms_state_equivalent(&a, &b), expected);
        assert_eq!(
            context.operands_state_equivalent(
                MachineOperandView::Shared(&shared(&a)),
                MachineOperandView::Shared(&shared(&b))
            ),
            expected
        );
    }
}

#[test]
fn state_source_index_matches_retained_signed_and_unsigned_ring_terms() {
    let _session = VerificationSession::enter();
    let [before, separate, overlap] = reads();
    for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
        let offsets = [before.clone(), separate.clone(), overlap.clone()].map(|read| {
            let native = binary(format, MachineBinaryOp::Add, read, MachineTerm::constant(1));
            let root = shared(&native);
            assert_eq!(
                operand_fingerprint(
                    MachineOperandView::Legacy(&native),
                    OperandFingerprintPolicy::MemoryState(true)
                ),
                operand_fingerprint(
                    MachineOperandView::Shared(&root),
                    OperandFingerprintPolicy::MemoryState(true)
                ),
            );
            scaled(&root)
        });
        let [source, target, changed] = offsets;
        assert_eq!(offset_state_shape(&source), offset_state_shape(&target));
        let end = PointerOffsetTerm::Constant(12);
        let fact = Proposition::ConditionIs(
            ConditionTerm::pointer_offset_equal(source.clone(), end.clone()),
            true,
        );
        let parent = PureFactContext::new();
        let context = parent.clone().assume_proposition(fact.clone());
        let exports = KernelTermExport::machine_export_count();
        assert!(context.has_pointer_offset_state_fact(&target, &end));
        assert!(context.has_pointer_offset_state_fact(&end, &target));
        assert!(!context.has_pointer_offset_state_fact(&changed, &end));
        assert!(!parent.has_pointer_offset_state_fact(&target, &end));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[test]
fn cached_state_syntax_never_caches_context_authority() {
    let _session = VerificationSession::enter();
    let memory = crate::kernel::intern_memory(Memory::new().with_block("retained_state-alias", 16));
    let pointers = [994110, 994111].map(|id| Pointer {
        block: "retained_state-alias".into(),
        offset: PointerOffsetTerm::Variable(Variable(id)),
    });
    let roots = pointers.each_ref().map(|pointer| {
        shared(&MachineTerm::MemoryLoad(
            memory.clone(),
            Box::new(pointer.clone()),
            LoadKind::Int32,
        ))
    });
    let fact = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(pointers[0].offset.clone(), pointers[1].offset.clone()),
        true,
    );
    let parent = PureFactContext::new();
    let child = parent.clone().assume_proposition(fact.clone());
    for (context, expected) in [(&child, true), (&parent, false), (&child, true)] {
        assert_eq!(
            context.operands_state_equivalent(
                MachineOperandView::Shared(&roots[0]),
                MachineOperandView::Shared(&roots[1])
            ),
            expected
        );
    }
}

mod scaling_tests {
    use super::*;
    include!(
        "../../../scaling_tests/kernel/assumptions/proposition_reasoning/retained_memory_indices.rs"
    );
}
