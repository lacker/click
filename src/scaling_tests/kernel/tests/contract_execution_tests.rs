// Scaling tests of `src/kernel/tests/contract_execution_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn certification_of_algebraic_witness_ignores_unrelated_quantifiers() {
    let mut samples = Vec::new();
    for size in [32, 64, 128, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = AlgebraicType::parameter("Path".into());
        let memory = Memory::new().with_block("graph", 4);
        let mut facts = PureFactContext::new().assume_proposition(path_exists_at_program_point(
            &ty,
            100,
            100,
            memory.clone(),
            0,
        ));
        for i in 1..=size {
            facts = facts.assume_proposition(path_exists_at_program_point(
                &ty,
                1_000 + u64::from(i),
                1_000 + u64::from(i),
                memory.clone(),
                i,
            ));
        }
        facts.build_stated_proposition_index();
        let goal = path_exists_at_program_point(&ty, 200, 200, memory.clone(), 0);
        let missing = path_exists_at_program_point(&ty, 200, 200, memory, 1_000);
        let (verdicts, work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                crate::kernel::PureFactContext::settles_exactly(&facts, &goal),
                crate::kernel::PureFactContext::settles_exactly(&facts, &missing),
            )
        });
        assert_eq!(verdicts, (true, false));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "certification scanned unrelated quantifiers: {samples:?}"
    );
}

#[test]
fn conditional_universal_certification_ignores_unrelated_facts() {
    let mut samples = Vec::new();
    for size in [32, 64, 128, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = AlgebraicType::parameter("Path".into());
        let memory = Memory::new().with_block("graph", 4);
        let mut facts = PureFactContext::new().assume_proposition(conditional_path_universal(
            &ty,
            100,
            memory.clone(),
            0,
        ));
        let mut proof_facts =
            crate::kernel::proof::ProofFacts::from_ordered(&[conditional_path_universal(
                &ty,
                100,
                memory.clone(),
                0,
            )]);
        for i in 1..=size {
            proof_facts = proof_facts.with_kernel_checked_fact(conditional_path_universal(
                &ty,
                1_000 + 2 * u64::from(i),
                memory.clone(),
                i,
            ));
            facts = facts.assume_proposition(conditional_path_universal(
                &ty,
                1_000 + 2 * u64::from(i),
                memory.clone(),
                i,
            ));
        }
        facts.build_stated_proposition_index();
        let goal = conditional_path_universal(&ty, 200, memory.clone(), 0);
        let missing = conditional_path_universal(&ty, 200, memory, 1_000);
        let (verdicts, work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                crate::kernel::PureFactContext::settles_exactly(&facts, &goal),
                crate::kernel::PureFactContext::settles_exactly(&facts, &missing),
                proof_facts.pure_known_available(&goal),
                proof_facts.pure_known_available(&missing),
            )
        });
        assert_eq!(verdicts, (true, false, true, false));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "conditional lookup scanned unrelated facts: {samples:?}"
    );
}

#[test]
fn reassociated_signed_add_domain_requires_each_guard_and_scales() {
    let a = MachineTerm::Variable(Variable(960_170));
    let b = MachineTerm::Variable(Variable(960_171));
    let c = MachineTerm::Variable(Variable(960_172));
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(a.clone(), MachineTerm::add(b.clone(), c.clone())),
        false,
    );
    let guards = [
        ConditionTerm::signed_add_overflows(a.clone(), b.clone()),
        ConditionTerm::signed_add_overflows(MachineTerm::add(a.clone(), b.clone()), c.clone()),
        ConditionTerm::signed_add_overflows(b.clone(), c.clone()),
    ];
    for missing in 0..3 {
        let mut facts = PureFactContext::new();
        for (index, guard) in guards.iter().enumerate() {
            if index != missing {
                facts = facts.assume_condition(guard.clone(), false);
            }
        }
        assert!(
            !crate::kernel::api::checked_int32_reassociated_add_domain(&facts, &goal),
            "missing domain {missing} was accepted"
        );
    }
    let work = [16, 64, 256].map(|size| {
        let mut facts = PureFactContext::new();
        for index in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(961_000 + index)),
                    MachineTerm::constant(index as u32),
                ),
                true,
            );
        }
        for guard in &guards {
            facts = facts.assume_condition(guard.clone(), false);
        }
        let (accepted, work) = crate::persistent::measure_persistent_work(|| {
            crate::kernel::api::checked_int32_reassociated_add_domain(&facts, &goal)
        });
        assert!(accepted);
        work
    });
    assert!(work[0] > 0);
    assert!(
        work.iter().all(|sample| *sample <= work[0] + 256),
        "regrouping scanned unrelated facts: {work:?}"
    );
    // The sequential total can be in range while the regrouped inner sum
    // overflows: MIN + MAX + 1 == 0 is not a license to evaluate MAX + 1.
    let a = MachineTerm::constant(i32::MIN as u32);
    let b = MachineTerm::constant(i32::MAX as u32);
    let c = MachineTerm::constant(1);
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(a, MachineTerm::add(b, c)),
        false,
    );
    assert!(!crate::kernel::api::checked_int32_reassociated_add_domain(
        &PureFactContext::new(),
        &goal
    ));
}

#[test]
fn shared_reassociated_add_domains_keep_operands_and_required_guards() {
    use crate::kernel::machine_integer::{Operation, definedness::OverflowQueryView};
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineBinaryOp as Op, MachineOperandView as View,
    };
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let variable =
            |id| KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(id));
        let add = |a, b| KernelTerm::machine_binary_shared(ty, Op::Add, [a, b]);
        let a = add(variable(972_000), variable(972_001));
        let b = variable(972_002);
        let c = variable(972_003);
        let ab = add(a.clone(), b.clone());
        let bc = add(b.clone(), c.clone());
        let domain = |a: &KernelTerm, b: &KernelTerm| {
            let [upper, lower] = OverflowQueryView::from_operands(
                ty,
                Operation::Add,
                [View::Shared(a), View::Shared(b)],
            )
            .unwrap()
            .bounds();
            Proposition::And(Box::new(upper), Box::new(lower))
        };
        let guards = [domain(&a, &b), domain(&ab, &c), domain(&b, &c)];
        let goals = [domain(&a, &bc), domain(&bc, &a)];
        let mut base = PureFactContext::new();
        for index in 0..size {
            base = base.assume_condition(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(973_000 + index)),
                    MachineTerm::constant(index as u32),
                ),
                true,
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (_, used) = crate::instrumentation::measure_deterministic_work(|| {
            for missing in 0..=3 {
                let mut facts = base.clone();
                for (index, guard) in guards.iter().enumerate() {
                    if index != missing {
                        facts = facts.assume_proposition(guard.clone());
                    }
                }
                for goal in &goals {
                    assert_eq!(
                        crate::kernel::api::checked_int32_reassociated_add_domain(&facts, goal),
                        missing == 3,
                        "missing guard {missing}"
                    );
                }
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(used);
    }
    assert!(work.iter().all(|used| *used <= work[0] + 256), "{work:?}");
}

// Scalar allocation and access must not scan unrelated memory or holdings.
#[test]
fn automatic_scalar_ownership_work_is_independent_of_unrelated_storage() {
    let mut measurements = Vec::new();
    for count in [0u32, 16, 64, 256] {
        let mut memory = Memory::new();
        let mut resources = ResourceContext::new();
        for index in 0..count {
            let pointer = Pointer {
                block: format!("global:unrelated:{index}").into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            memory = memory
                .with_block(pointer.block.clone(), 4)
                .store(pointer.clone(), uint32(index));
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(
                MemoryRange::new_with_element_width(pointer, 0.into(), 4.into(), 1),
            ));
        }
        let state = ExecutionState::new()
            .with_memory(memory)
            .with_resource_context(resources);
        let statement = program_seq(
            program_declare("word", ProgramType::UInt32),
            program_seq(
                program_assign("word", crate::kernel::program_expression::uint32_literal(7)),
                program_return(crate::kernel::program_expression::variable("word")),
            ),
        );
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_execution_statement_paths(
                &state,
                &statement,
                &PureFactContext::new(),
                ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
                &mut ExecutionBudget::new(),
            )
            .unwrap()
        });
        assert!(
            matches!(&paths[0].outcome, StatementOutcome::Return { value, .. } if *value.native() == ProgramValue::UInt32(MachineTerm::uint32_constant(7)))
        );
        measurements.push(work);
    }
    assert!(
        measurements
            .iter()
            .all(|work| *work <= measurements[0].max(1) * 4 + 32),
        "unrelated storage changed scalar allocation/access work: {measurements:?}"
    );
    {
        let costs = measurements.clone();
        let indexed = |costs: &[usize]| costs.iter().all(|work| *work <= costs[0] + 64);
        assert!(indexed(&costs), "indexed work: {costs:?}");
        let scanned = costs
            .iter()
            .zip([0u32, 16, 64, 256])
            .map(|(work, size)| work + usize::try_from(size).unwrap())
            .collect::<Vec<_>>();
        assert!(
            !indexed(&scanned),
            "the smaller fixture must detect a visit per unrelated item: {costs:?}"
        );
    }
}
