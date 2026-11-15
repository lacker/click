use super::*;

#[test]
fn growing_shared_state_comparisons_reuse_syntax_but_recheck_loads() {
    for conditional in [false, true] {
        for structural in [false, true] {
            let mut samples = Vec::new();
            for size in [8, 32, 128] {
                let _session = crate::kernel::VerificationSession::enter();
                let ty = MachineIntegerType::Int32;
                let (left_read, right_read, a, b) = load_pair(ty);
                let leaf = |read: &MachineTerm, variable| {
                    if structural {
                        crate::kernel::KernelTermImport::default()
                            .machine_arithmetic(ty, read)
                            .unwrap()
                    } else {
                        KernelTerm::variable(KernelType::Program(ty.program_type()), variable)
                    }
                };
                let mut left = leaf(&left_read, a);
                let mut right = leaf(&right_read, b);
                let zero = crate::kernel::KernelTermImport::default()
                    .machine(ty, &MachineTerm::constant(0));
                let guard = |read, variable| {
                    crate::kernel::KernelTermImport::default().condition(&ConditionTerm::Compare {
                        format: ty,
                        relation: CompareRelation::GreaterThan,
                        left: Box::new(if structural {
                            read
                        } else {
                            MachineTerm::Variable(variable)
                        }),
                        right: Box::new(MachineTerm::constant(0)),
                    })
                };
                let guards = [guard(left_read.clone(), a), guard(right_read.clone(), b)];
                if conditional {
                    left = zero.clone();
                    right = zero.clone();
                }
                let condition = |root| {
                    ConditionTerm::integer_less_equal(
                        IntegerTerm::Machine(
                            SharedMachineIntegerTerm::from_shared(ty, root).unwrap(),
                        ),
                        IntegerTerm::constant_i64(7),
                    )
                };
                let exports = KernelTermExport::machine_export_count();
                let calls = std::cell::Cell::new(0);
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..size {
                        for (root, guard) in [(&mut left, &guards[0]), (&mut right, &guards[1])] {
                            *root = if conditional {
                                KernelTerm::machine_if_shared(
                                    ty,
                                    [guard.clone(), root.clone(), root.clone()],
                                )
                            } else {
                                KernelTerm::machine_binary_shared(
                                    ty,
                                    MachineBinaryOp::Add,
                                    [root.clone(), zero.clone()],
                                )
                            };
                        }
                        let (l, r) = (condition(left.clone()), condition(right.clone()));
                        assert!(conditions_equal_with_load_atoms(&l, &r, &|_, _| {
                            calls.set(calls.get() + 1);
                            true
                        }));
                        assert!(!conditions_equal_with_load_atoms(&l, &r, &|_, _| {
                            calls.set(calls.get() + 1);
                            false
                        }));
                    }
                });
                // Guard imports carry structural read descriptors. A bare named
                // pair additionally retries its raw origins on refusal. Every
                // query checks authority again even when syntax is cached.
                assert_eq!(
                    calls.get(),
                    size * if structural || conditional { 2 } else { 3 }
                );
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                samples.push(work);
            }
            assert!(
                samples.windows(2).all(|p| p[1] <= p[0] * 5 + 100),
                "conditional={conditional}, structural={structural}: {samples:?}"
            );
        }
    }
}
