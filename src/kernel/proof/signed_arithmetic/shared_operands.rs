//! Shared/native certificate operands use the same retained structural key.
use super::*;
use crate::kernel::MachineOperandView;
#[cfg(test)]
use crate::kernel::{KernelTerm, KernelType};

pub(crate) fn clear_shared_operand_keys() {
    atom_keys::clear();
}

pub(super) fn operands_equal(left: MachineOperandView<'_>, right: MachineOperandView<'_>) -> bool {
    match (
        SignedArithmeticAtom::from_operand(left),
        SignedArithmeticAtom::from_operand(right),
    ) {
        (Some(left), Some(right)) => charge_atom_pair_work(&left, &right) && left == right,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structural_keys_survive_state_restore_but_clear_for_a_new_session() {
        {
            let _session = crate::kernel::VerificationSession::enter();
            let retained_state = crate::kernel::VerificationSession::capture_state();
            let format = MachineIntegerType::Int32;
            let mut term = KernelTerm::variable(
                KernelType::Program(crate::kernel::ProgramType::Int32),
                Variable(982501),
            );
            for _ in 0..32 {
                term = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [term.clone(), term.clone()],
                );
            }
            let view = MachineOperandView::Shared(&term);
            assert!(operands_equal(view, view));
            let count = atom_keys::cache_len();
            assert!(crate::kernel::VerificationSession::restore_state(
                &retained_state
            ));
            crate::kernel::eval::begin_load_origin_epoch();
            let (same, work) =
                crate::instrumentation::measure_deterministic_work(|| operands_equal(view, view));
            assert!(same);
            assert!(
                work <= 4,
                "a restored context rewalked structural operands: {work}"
            );
            assert_eq!(atom_keys::cache_len(), count);
        }
        let _session = crate::kernel::VerificationSession::enter();
        assert!(atom_keys::cache_len() == 0);
    }
}
