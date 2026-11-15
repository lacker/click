use super::*;
use crate::kernel::{
    KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, MachineOperandView as V,
};

#[test]
fn state_operand_keys_share_prefixes_in_linear_work() {
    let samples = [16usize, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(998211));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                );
                let key = operand(V::Shared(&root));
                assert_eq!(key, operand(V::Shared(&root)));
                assert!(!key.requires_checked_match());
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        (size, work)
    });
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}

#[test]
fn conditional_state_keys_reuse_growing_shared_arms() {
    let samples = [16usize, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(998221));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                let guard =
                    crate::kernel::KernelTermImport::default().condition(&ConditionTerm::equal(
                        MachineTerm::Variable(Variable(998222 + index as u64)),
                        MachineTerm::constant(0),
                    ));
                root = KernelTerm::machine_if_shared(format, [guard, root.clone(), root.clone()]);
                let key = operand(V::Shared(&root));
                assert_eq!(key, operand(V::Shared(&root)));
                assert!(!key.requires_checked_match());
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        (size, work)
    });
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}
