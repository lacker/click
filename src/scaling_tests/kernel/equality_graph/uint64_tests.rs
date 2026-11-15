// Scaling tests of `src/kernel/equality_graph/uint64_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn integer_address_queries_ignore_unrelated_equations_and_reuse_definitions() {
    let _session = VerificationSession::enter();
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_uint64_equality(
                &MachineTerm::Variable(Variable(i)),
                &MachineTerm::Variable(Variable(i + 10_000)),
            );
        }
        let bits = MachineTerm::Variable(Variable(960_004));
        let decoded = Pointer::integer_address(bits.clone());
        assert!(graph.are_uint64_equal(&raw_address(&decoded), &bits));
        let (((), work), maps) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..16 {
                    assert!(graph.are_uint64_equal(&raw_address(&decoded), &bits));
                }
            })
        });
        samples.push((work, maps));
    }
    assert!(
        samples
            .windows(2)
            .all(|p| p[0].0 == p[1].0 && p[1].1 <= p[0].1 * 2),
        "{samples:?}"
    );
}

#[test]
fn wide_congruence_queries_do_not_scan_unrelated_equalities() {
    let mut previous = None;
    for size in [16_u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let p = Pointer::symbolic(Variable(940_001));
        let q = Pointer::symbolic(Variable(940_002));
        let a = MachineTerm::Variable(Variable(940_003));
        let b = MachineTerm::Variable(Variable(940_004));
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_uint64_equality(
                &MachineTerm::Variable(Variable(i)),
                &MachineTerm::Variable(Variable(i + 10_000)),
            );
        }
        graph.add_uint64_equality(&a, &packed(&b, &p));
        graph.add_equality(&p, &q);
        let (ok, work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.are_uint64_equal(&a, &packed(&b, &q))
        });
        assert!(ok);
        if let Some(previous) = previous {
            assert_eq!(
                work, previous,
                "unrelated facts changed query work at {size}"
            );
        }
        previous = Some(work);
    }
}

#[test]
fn range_values_and_constants_resolve_long_wide_equality_chains() {
    use crate::kernel::{ConditionTerm, PureFactContext};
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let var = |i| MachineTerm::Variable(Variable(950_000 + i));
        let mut facts = PureFactContext::new();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 0..size {
                facts = facts
                    .clone()
                    .assume_condition(ConditionTerm::uint64_equal(var(i), var(i + 1)), true);
            }
            facts = facts.clone().assume_condition(
                ConditionTerm::uint64_equal(var(size), MachineTerm::uint64_constant(37)),
                true,
            );
            assert_eq!(facts.wide_constant_from_equalities(&var(0)), Some(37));
            assert!(facts.uint64_values_equal_for_range_resolution(
                &var(0),
                &MachineTerm::uint64_constant(37)
            ));
        });
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn an_aliased_read_meets_its_stored_cell_without_scanning_unrelated_cells_or_aliases() {
    let mut previous = None;
    for size in [16_u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let mut memory = Memory::new().with_block("cells", 8 * (size as u32 + 1));
        let cell = |i: u64| Pointer {
            block: "cells".into(),
            offset: PointerOffsetTerm::Constant(8 * i as i64),
        };
        for i in 0..=size {
            memory = memory.store(
                cell(i),
                ProgramValue::UInt64(MachineTerm::uint64_constant(i)),
            );
        }
        let memory = intern_memory(memory);
        let mut context = PureFactContext::new();
        for i in 0..size {
            let other = Pointer::symbolic(Variable(970_000 + i));
            context = context.assume_proposition(alias(&other, &cell(i)));
        }
        let read_at = Pointer::symbolic(Variable(979_999));
        context = context.assume_proposition(alias(&read_at, &cell(size)));
        let read = word(&memory, &read_at, 8);
        let stored = MachineTerm::uint64_constant(size);
        let (ok, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.equality_graph.are_uint64_equal(&read, &stored)
        });
        assert!(ok);
        if let Some(previous) = previous {
            assert_eq!(
                work, previous,
                "unrelated cells or aliases changed work at {size}"
            );
        }
        previous = Some(work);
    }
}

#[test]
fn an_aliased_read_grows_linearly_with_its_own_alias_class() {
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let stored_at = Pointer {
            block: "cells".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = intern_memory(Memory::new().with_block("cells", 8).store(
            stored_at.clone(),
            ProgramValue::UInt64(MachineTerm::uint64_constant(7)),
        ));
        let mut context = PureFactContext::new();
        let link = |i: u64| Pointer::symbolic(Variable(972_000 + i));
        context = context.assume_proposition(alias(&link(0), &stored_at));
        for i in 1..=size {
            context = context.assume_proposition(alias(&link(i), &link(i - 1)));
        }
        let read = word(&memory, &link(size), 8);
        let (ok, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .equality_graph
                .are_uint64_equal(&read, &MachineTerm::uint64_constant(7))
        });
        assert!(ok);
        samples.push((size, work));
    }
    // Linear in the class: four times the aliases, at most about four times
    // the work.
    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 * 5),
        "{samples:?}"
    );
}

#[test]
fn a_late_alias_rechecks_only_the_reads_of_its_own_address_class() {
    let mut unrelated = None;
    let mut related = Vec::new();
    for size in [16_u64, 64, 256] {
        let _session = VerificationSession::enter();
        let read_at = Pointer::symbolic(Variable(973_000));
        let mut memory = Memory::new().with_block("other", 8 * size as u32);
        let mut graph = EqualityGraph::default();
        // One unresolved read of `read_at` in each of `size` states.
        for i in 0..size {
            memory = memory.store(
                Pointer {
                    block: "other".into(),
                    offset: PointerOffsetTerm::Constant(8 * i as i64),
                },
                ProgramValue::UInt64(MachineTerm::uint64_constant(i)),
            );
            let read = word(&intern_memory(memory.clone()), &read_at, 8);
            assert!(!graph.are_uint64_equal(&read, &MachineTerm::uint64_constant(99)));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.add_equality(
                &Pointer::symbolic(Variable(974_000)),
                &Pointer::symbolic(Variable(974_001)),
            );
        });
        if let Some(previous) = unrelated {
            assert_eq!(work, previous, "an unrelated alias changed work at {size}");
        }
        unrelated = Some(work);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.add_equality(&Pointer::symbolic(Variable(974_002)), &read_at);
            graph.are_uint64_equal(
                &MachineTerm::uint64_constant(1),
                &MachineTerm::uint64_constant(1),
            );
        });
        related.push((size, work));
    }
    // Linear in the class's reads: four times the reads, about four times
    // the work.
    assert!(
        related.windows(2).all(|pair| pair[1].1 <= pair[0].1 * 5),
        "{related:?}"
    );
}

#[test]
fn a_recorded_address_fact_is_found_through_its_word_class_without_scanning() {
    let mut previous = None;
    for size in [16_u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let word = |i: u64| MachineTerm::Variable(Variable(975_000 + i));
        let mut context = PureFactContext::new();
        for i in 0..size {
            context = context.assume_proposition(fact(word(i), word(i + 2_000)));
        }
        let read = word(9_000);
        let recorded = word(9_001);
        let address = MachineTerm::pointer_address(Pointer::symbolic(Variable(976_000)));
        context = context
            .assume_proposition(fact(recorded.clone(), address))
            .assume_proposition(fact(read.clone(), recorded.clone()));
        let (endpoints, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .equality_graph
                .wide_equation_endpoints_equal_to(crate::kernel::MachineOperandView::Legacy(&read))
        });
        assert!(endpoints.contains(&recorded), "{endpoints:?}");
        if let Some(previous) = previous {
            assert_eq!(
                work, previous,
                "unrelated equalities changed work at {size}"
            );
        }
        previous = Some(work);
    }
}

#[test]
fn shared_wide_endpoint_queries_reuse_growing_prefixes() {
    use crate::kernel::{
        IntegerTerm, KernelTerm, KernelTermExport, KernelTermImport, MachineOperandView as V,
        SharedMachineIntegerTerm,
    };
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let name = MachineTerm::Variable(Variable(984101));
        let mut root = KernelTermImport::default()
            .machine_arithmetic(ty, &name)
            .unwrap();
        let base = root.clone();
        let one = KernelTermImport::default()
            .machine_arithmetic(ty, &MachineTerm::uint64_constant(1))
            .unwrap();
        let observe =
            |root| IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, root).unwrap());
        let address = MachineTerm::pointer_address(Pointer::symbolic(Variable(984102)));
        let mut context = PureFactContext::new().assume_proposition(fact(name.clone(), address));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Multiply,
                    [root, one.clone()],
                );
                context = context.assume_condition(
                    ConditionTerm::integer_equal(observe(root.clone()), observe(base.clone())),
                    true,
                );
                let endpoints = context
                    .equality_graph
                    .wide_equation_endpoints_equal_to(V::Shared(&root));
                assert_eq!(endpoints, vec![name.clone()]);
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|p| p[1] <= p[0] * 5 + 100),
        "{samples:?}"
    );
}

#[test]
fn machine_observation_round_trips_retain_growing_shared_operands() {
    use crate::kernel::{
        IntegerTerm, KernelTerm, KernelTermExport, KernelType, SharedMachineIntegerTerm,
    };
    for nested in [false, true] {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = VerificationSession::enter();
            let format = MachineIntegerType::UInt64;
            let mut root =
                KernelTerm::variable(KernelType::Program(ProgramType::UInt64), Variable(989821));
            let context = PureFactContext::new();
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for index in 0..size {
                    let fresh = KernelTerm::variable(
                        KernelType::Program(ProgramType::UInt64),
                        Variable(989822 + index),
                    );
                    if !nested {
                        root = KernelTerm::machine_binary_shared(
                            format,
                            MachineBinaryOp::Add,
                            [root.clone(), fresh],
                        );
                    }
                    let original = IntegerTerm::Machine(
                        SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap(),
                    );
                    let observed: crate::kernel::SharedIntegerTerm = original.clone().into();
                    let conversion = KernelTerm::integer_to_machine(
                        format,
                        crate::kernel::KernelTermImport::default().integer(&observed),
                    )
                    .unwrap();
                    let converted = IntegerTerm::Machine(
                        SharedMachineIntegerTerm::from_shared(format, conversion.clone()).unwrap(),
                    );
                    assert!(
                        context
                            .equality_graph
                            .are_integer_equal(&converted, &original)
                    );
                    if nested {
                        root = conversion;
                    }
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            samples.push((size, work));
        }
        for pair in samples.windows(2) {
            assert!(pair[1].1 <= pair[0].1 * 5, "{samples:?}");
        }
    }
}

#[test]
fn machine_observation_round_trip_ignores_unrelated_equalities() {
    use crate::kernel::{IntegerTerm, SharedMachineIntegerTerm};
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256] {
        let _session = VerificationSession::enter();
        let mut graph = EqualityGraph::default();
        for index in 0..size {
            graph.add_uint64_equality(
                &MachineTerm::Variable(Variable(980000 + index)),
                &MachineTerm::Variable(Variable(981000 + index)),
            );
        }
        let source = MachineTerm::PureFunctionApplication {
            name: "opaque_round_trip_scaling".into(),
            arguments: vec![MachineTerm::Variable(Variable(989831))],
        };
        let converted = MachineTerm::IntegerToMachine {
            destination: MachineIntegerType::UInt64,
            value: IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::UInt64,
                source.clone(),
            ))
            .into(),
        };
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(graph.are_uint64_equal(&converted, &source));
            assert!(!graph.are_uint64_equal(&converted, &MachineTerm::Variable(Variable(989832))));
        });
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
}
