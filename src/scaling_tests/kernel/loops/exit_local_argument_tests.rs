// Scaling tests of `src/kernel/loops.rs` (module `exit_local_argument_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

// A declared argument selects one local; growing the unrelated environment
// must not introduce a scan or a search for equal-looking value vectors.
#[test]
fn exit_local_argument_lookup_skips_unrelated_locals() {
    let _session = crate::kernel::VerificationSession::enter();
    let (binder, instances) = fixture(ResourceStateSource::Current);
    let mut costs = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut ambient = ExecutionState::new();
        for index in 0..size {
            ambient = ambient.with_local(format!("other{index}"), int32(index));
        }
        let exits = [
            ambient.clone().with_local("cur", int32(1)),
            ambient.clone().with_local("cur", int32(2)),
        ];
        let successor = ambient.with_local("cur", int32(3));
        let (arguments, work) = crate::instrumentation::measure_deterministic_work(|| {
            loop_exit_local_arguments(
                &successor,
                &exits,
                &binder,
                &instances,
                &[PureFactContext::new(), PureFactContext::new()],
            )
        });
        assert_eq!(arguments, vec![Some(AlgebraicValue::Program(int32(3)))]);
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] * 2),
        "{costs:?}"
    );
}

#[test]
fn exit_local_argument_context_indexing_is_linear_and_shared() {
    let _session = crate::kernel::VerificationSession::enter();
    let (binder, instances) = fixture(ResourceStateSource::Current);
    let exits = [
        ExecutionState::new().with_local("cur", int32(1)),
        ExecutionState::new().with_local("cur", int32(2)),
    ];
    let successor = ExecutionState::new().with_local("cur", int32(3));
    for size in [4, 16, 64, 256] {
        let facts = (0..size)
            .map(|index| {
                ExecutionPureFact::new(Proposition::ConditionIs(
                    ConditionTerm::pointer_equal(
                        Pointer::symbolic(Variable(10000 + index)),
                        Pointer::symbolic(Variable(20000 + index)),
                    ),
                    true,
                ))
            })
            .collect::<ExecutionFacts>();
        let (contexts, work) = crate::instrumentation::measure_deterministic_work(|| {
            loop_exit_argument_contexts(&[&facts, &facts], &[], &PureFactContext::new(), true)
        });
        assert!(work > 0 && work <= size as usize * 200, "{size}: {work}");
        let before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
        for _ in 0..size {
            assert_eq!(
                loop_exit_local_arguments(&successor, &exits, &binder, &instances, &contexts),
                vec![Some(AlgebraicValue::Program(int32(3)))]
            );
        }
        assert_eq!(
            crate::kernel::reasoning::path_facts::context_rebuild_entries(),
            before
        );
    }
}

#[test]
fn exit_argument_checks_reuse_the_checked_path_context() {
    let _session = crate::kernel::VerificationSession::enter();
    let fact = |id, value| {
        Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::Variable(Variable(id)),
                MachineTerm::constant(value),
            ),
            true,
        )
    };
    let selected = fact(930_000, 7);
    let ambient_only = fact(930_001, 9);
    let mut costs = Vec::new();
    for count in [4u64, 8, 16, 32] {
        let mut root = crate::kernel::proof::ProofFacts::default();
        for index in 0..count {
            root = root.with_fact(fact(931_000 + index, index as u32));
        }
        let path = root.with_fact(selected.clone());
        let exit = LoopBreakExit::from_proof_facts(ExecutionState::new(), &path);
        let facts = exit
            .pure_facts()
            .iter()
            .cloned()
            .map(ExecutionPureFact::certified)
            .collect::<ExecutionFacts>();
        let Proposition::ConditionIs(selected_condition, _) = &selected else {
            unreachable!()
        };
        let older_truth = Proposition::ConditionIs(selected_condition.clone(), false);
        let ambient = root
            .assumptions()
            .clone()
            .assume_proposition(ambient_only.clone())
            .assume_proposition(older_truth.clone());
        let (contexts, work) = crate::instrumentation::measure_deterministic_work(|| {
            loop_exit_argument_contexts(&[&facts], &[exit.fact_context().cloned()], &ambient, true)
        });
        assert!(contexts[0].contains_assumed_exact(&selected));
        assert!(!contexts[0].contains_assumed_exact(&older_truth));
        assert!(contexts[0].contains_known(&ambient_only));
        assert!(!root.contains(&selected));
        assert!(!path.contains(&ambient_only));
        costs.push(work);
    }
    assert!(
        costs.iter().all(|work| *work <= costs[0] + 64),
        "exit join rebuilt the checked path context: {costs:?}"
    );
}
