use super::*;
use crate::kernel::{KernelFoldIndex, KernelIntegerOperator, KernelTermExport, KernelTermImport};

#[test]
fn common_fold_read_dependencies_visit_shared_bodies_once_and_recheck_states() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let current = Memory::new();
        let pointer = Pointer::symbolic(Variable(972000));
        let later = current.clone().store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(1)),
        );
        let read = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory_ref(&current),
                Box::new(pointer.clone()),
                LoadKind::Int32,
            ),
        ));
        let mut body = KernelTermImport::default().integer(&read.into());
        for _ in 0..size {
            body =
                KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![body.clone(), body])
                    .unwrap();
        }
        let zero = KernelTerm::integer_literal(0.into());
        let fold = KernelFold::new(
            KernelFoldIndex::Integer,
            Variable(972001),
            Variable(972002),
            [zero.clone(), zero.clone(), zero, body],
        )
        .unwrap();
        let exports = KernelTermExport::machine_export_count();
        for memory in [&current, &later, &current] {
            let mut loads = Vec::new();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                collect_fold_memory_loads(&fold, memory, &mut loads, None, &mut BTreeSet::new())
            });
            result.unwrap();
            assert!(work <= 8 * (size + 1) + 64, "size={size}, work={work}");
            if std::ptr::eq(memory, &current) {
                assert_eq!(loads, vec![(pointer.clone(), 4)]);
            } else {
                assert!(loads.is_empty());
            }
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[test]
fn nested_machine_fold_dependencies_share_initial_and_body_subgraphs() {
    use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, MachineOperandView};
    for size in [4, 8, 16] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = Memory::new();
        let pointer = Pointer::symbolic(Variable(972010));
        let read = MachineTerm::MemoryLoad(
            crate::kernel::intern_memory_ref(&memory),
            Box::new(pointer.clone()),
            LoadKind::Int32,
        );
        let format = MachineIntegerType::Int32;
        let mut child =
            KernelTerm::retained_machine_operand(format, MachineOperandView::Legacy(&read));
        let zero = KernelTerm::retained_machine_operand(
            format,
            MachineOperandView::Legacy(&MachineTerm::constant(0)),
        );
        let bound = KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(972011));
        let mut last = None;
        for _ in 0..size {
            let initial = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [child.clone(), zero.clone()],
            );
            let body = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Subtract,
                [child, zero.clone()],
            );
            let fold = KernelFold::new(
                KernelFoldIndex::Int32,
                Variable(972012),
                Variable(972013),
                [zero.clone(), bound.clone(), initial, body],
            )
            .unwrap();
            child = fold.clone().into_term();
            last = Some(fold);
        }
        let before = KernelTermExport::machine_export_count();
        let mut loads = Vec::new();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            collect_fold_memory_loads(
                last.as_ref().unwrap(),
                &memory,
                &mut loads,
                None,
                &mut BTreeSet::new(),
            )
        });
        result.unwrap();
        // The two distinct leaf arithmetic parents each report the same read,
        // as existing dependency collection permits. Nested sharing must not
        // multiply these reports or the work.
        assert_eq!(loads, vec![(pointer.clone(), 4), (pointer, 4)]);
        assert_eq!(KernelTermExport::machine_export_count(), before);
        assert!(work <= 150 * size + 100, "size={size}, work={work}");
    }
}
