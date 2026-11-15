use super::*;

#[test]
fn boolean_reads_keep_shared_indices_through_rewrites_and_observations() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut index =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(999330));
        for _ in 0..size {
            index = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [index.clone(), index],
            );
        }
        let address = SharedPointerAddress::new(
            SharedPointerBlock::import(&PointerBlock::Symbolic(Variable(999331))),
            KernelPointerOffset::Int32Scaled {
                value: index,
                byte_width: 4,
            }
            .into_shared()
            .unwrap(),
        );
        let memory = intern_memory(Memory::new());
        let root = KernelTerm::boolean_read(memory.clone(), address.clone());
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                crate::kernel::reasoning::substitute_bitvector_variable_in_common_condition(
                    &root,
                    Variable(999332),
                    &MachineTerm::constant(1)
                ),
                Some(root.clone())
            );
            assert_eq!(
                crate::kernel::reasoning::substitute_pointer_variable_in_common_condition(
                    &root,
                    Variable(999332),
                    &Pointer::null()
                ),
                Some(root.clone())
            );
            assert!(
                crate::kernel::memory_provenance::transport_framed_common_condition(
                    &root,
                    memory.memory(),
                    None
                )
                .is_none()
            );
            let native = root.boolean_read_native().unwrap();
            assert!(std::ptr::eq(native, root.boolean_read_native().unwrap()));
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 200 * size + 2000, "size={size}, work={work}");
    }
}

#[test]
fn boolean_reads_admit_states_without_comparing_unrelated_contents() {
    for size in [16, 64, 256] {
        let memory = (0..size).fold(Memory::new(), |memory, i| {
            memory.with_block(format!("bool-unrelated-{i}"), 4)
        });
        let first = {
            let _session = crate::kernel::VerificationSession::enter();
            intern_memory(memory.clone())
        };
        let _session = crate::kernel::VerificationSession::enter();
        let second = intern_memory(memory);
        let address = SharedPointerAddress::import(&Pointer::symbolic(Variable(999340)));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let a = KernelTerm::boolean_read(first, address.clone());
            let b = KernelTerm::boolean_read(second, address);
            assert_ne!(a, b);
        });
        assert!(work <= 16, "size={size}, work={work}");
    }
}
