use super::*;
use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm, Variable};

#[test]
fn arithmetic_guard_classification_keeps_shared_prefixes() {
    for format in [MachineIntegerType::Int32, MachineIntegerType::Int64] {
        let mut samples = Vec::new();
        for size in [8, 32, 96] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut term =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(982200));
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    term = KernelTerm::arithmetic_binary(
                        format,
                        MachineBinaryOp::Add,
                        [term.clone(), term.clone()],
                    )
                    .unwrap();
                    let observation =
                        SharedMachineIntegerTerm::from_shared(format, term.clone()).unwrap();
                    let exact = Operation::Add.exact(
                        IntegerTerm::Machine(observation.clone()),
                        IntegerTerm::constant(1.into()),
                    );
                    let [upper, lower] = ordinary_bounds(format, exact);
                    let roots = [&upper, &lower].map(|bound| {
                        let Proposition::ConditionIs(condition, true) = bound else {
                            unreachable!()
                        };
                        condition.root().unwrap().clone()
                    });
                    let guard = Proposition::And(Box::new(upper.clone()), Box::new(lower));
                    let exports = crate::kernel::KernelTermExport::machine_export_count();
                    let fact = definedness_of_integer_bound(&upper).unwrap();
                    let Proposition::ConditionIs(condition, false) = fact else {
                        unreachable!()
                    };
                    let result = ordinary_arithmetic_guard(&guard).unwrap();
                    assert_eq!(condition.root().unwrap(), result.root().unwrap());
                    let (_, _, [crate::kernel::MachineOperandView::Shared(left), _]) =
                        result.operand_view().overflow().unwrap()
                    else {
                        unreachable!()
                    };
                    assert_eq!(left, &term);
                    assert_eq!(
                        crate::kernel::KernelTermExport::machine_export_count(),
                        exports
                    );
                    let query = ordinary_arithmetic_guard_view(&guard).unwrap();
                    assert_eq!(query.format, format);
                    assert_eq!(query.operation, Operation::Add);
                    assert!(crate::kernel::proof::is_definedness_guard(&guard));
                    let incomplete = Proposition::And(Box::new(upper.clone()), Box::new(upper));
                    assert!(ordinary_arithmetic_guard_view(&incomplete).is_none());
                    assert!(!crate::kernel::proof::is_definedness_guard(&incomplete));
                    assert!(roots.iter().all(|root| !root.has_cached_native_argument()));
                    assert!(!observation.has_boxed_operand());
                }
            });
            samples.push((size, work));
        }
        for pair in samples.windows(2) {
            let [(small, sw), (large, lw)] = pair else {
                unreachable!()
            };
            assert!(lw * small * 4 <= sw * large * 5, "{samples:?}");
        }
    }
}
