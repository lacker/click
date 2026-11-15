// Scaling tests of `src/kernel/proof/object.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn invariant_body_evidence_requires_exact_complete_root_and_context() {
    use crate::kernel::proof::{
        ExecutionFrontier, ExecutionProofCore, ExecutionRegionKind, FrontierPosition,
    };
    use crate::kernel::{
        ComparisonOperator, ExecutionState, LoopInvariantCheck, ProgramValue, SpecExpression,
        SpecProposition,
    };
    type TestProof =
        ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ProofExecutionState<()>>;
    let root = |facts: ProofFacts, core: ExecutionProofCore| -> TestProof {
        ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Frontier(FrontierObligation),
                ProofBranchState {
                    facts,
                    unfolded_predicates: PersistentOrderedSet::default(),
                    execution: Some(Arc::new(ProofExecutionState::new(core, ()))),
                },
            ),
        )
    };
    let checks = [0, 1].map(|value| {
        LoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(ProgramValue::Int32(MachineTerm::constant(value))),
                operator: ComparisonOperator::LessEqual,
                right: SpecExpression::Value(ProgramValue::Int32(MachineTerm::constant(value))),
            },
            None,
            None,
        )
    });
    let entry = ExecutionState::new();
    let samples = [16, 32, 64, 128].map(|size| {
        let facts = ProofFacts::from_ordered(
            &(0..size)
                .map(|i| Proposition::Predicate {
                    name: format!("unrelated_{i}"),
                    arguments: vec![],
                })
                .collect::<Vec<_>>(),
        );
        let core = ExecutionProofCore::at_entry(
            ExecutionState::new(),
            ExecutionFrontier {
                region: ExecutionRegionKind::LoopBody,
                position: FrontierPosition::RegionBoundary,
                ..Default::default()
            },
        );
        let frontier = root(facts.clone(), core);
        let ((body, scope), opening_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                frontier
                    .open_invariant_body(
                        &entry,
                        &entry,
                        &crate::kernel::IntegerTerm::var(crate::kernel::Variable(9_999)),
                        &checks,
                        &[],
                        &[],
                        &[],
                        |_, _| (),
                    )
                    .unwrap()
            });
        assert!(
            frontier
                .retain_invariant_body(scope.clone(), &body)
                .is_err()
        );
        // Even the same exact goal and premises in a fresh root are not this scope.
        let unrelated = TestProof::root((), body.state.open_branches.root_branch().clone())
            .apply_normalize()
            .ok()
            .unwrap();
        assert!(
            frontier
                .retain_invariant_body(scope.clone(), &unrelated)
                .is_err()
        );
        let complete = body.apply_normalize().ok().unwrap();
        let (closed, closing_work) = crate::instrumentation::measure_deterministic_work(|| {
            let closed = frontier
                .retain_invariant_body(scope.clone(), &complete)
                .unwrap();
            closed
                .validate_checked_invariant_lowerings(&checks, &[])
                .unwrap();
            closed
        });
        assert!(
            closed
                .validate_checked_invariant_lowerings(&checks[..1], &[])
                .is_err()
        );
        let core = closed.execution_view().unwrap().execution().core.clone();
        for variant in 0..4 {
            let mut changed = core.clone();
            let mut changed_facts = facts.clone();
            match variant {
                0 => changed.state = ExecutionState::new().into(),
                1 => changed.effect_facts = Vec::new().into(),
                2 => {
                    changed_facts = facts.with_fact(Proposition::Predicate {
                        name: "other_arm".into(),
                        arguments: vec![],
                    })
                }
                _ => {
                    Arc::make_mut(changed.checked_invariant_lowerings.as_mut().unwrap()).body = None
                }
            }
            let stale = root(changed_facts, changed);
            assert!(
                stale
                    .validate_checked_invariant_lowerings(&checks, &[])
                    .is_err()
            );
            if variant < 3 {
                assert!(
                    stale
                        .retain_invariant_body(scope.clone(), &complete)
                        .is_err()
                );
            }
        }
        let mut wrong = core;
        Arc::make_mut(wrong.checked_invariant_lowerings.as_mut().unwrap())
            .body
            .as_mut()
            .unwrap()
            .goal = Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(false), true);
        assert!(
            root(facts, wrong)
                .validate_checked_invariant_lowerings(&checks, &[])
                .is_err()
        );
        opening_work + closing_work
    });
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(2).saturating_add(8),
            "{samples:?}"
        );
    }
}

#[test]
fn invariant_bundle_closure_checks_retained_evidence_and_context_locally() {
    use crate::kernel::proof::{
        ExecutionFrontier, ExecutionProofCore, ExecutionRegionKind, FrontierPosition,
    };
    use crate::kernel::{
        ComparisonOperator, ExecutionState, LoopInvariantCheck, ProgramValue, SpecExpression,
        SpecProposition,
    };
    type TestProof =
        ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ProofExecutionState<()>>;
    // One entry state: every state below must be the very same state,
    // creation ledger included.
    let entry = ExecutionState::new().with_population_creation_tracking();
    let root = |facts: ProofFacts, core: ExecutionProofCore| -> TestProof {
        ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Frontier(FrontierObligation),
                ProofBranchState {
                    facts,
                    unfolded_predicates: PersistentOrderedSet::default(),
                    execution: Some(Arc::new(ProofExecutionState::new(core, ()))),
                },
            ),
        )
    };
    let checks = vec![
        LoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(ProgramValue::Int32(MachineTerm::constant(0))),
                operator: ComparisonOperator::LessEqual,
                right: SpecExpression::Value(ProgramValue::Int32(MachineTerm::constant(0))),
            },
            None,
            None,
        ),
        LoopInvariantCheck::new(
            SpecProposition::Predicate {
                resource_state_dependent: true,
                name: "invariant".into(),
                arguments: vec![],
            },
            None,
            None,
        ),
    ];
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let facts = ProofFacts::from_ordered(
            &(0..size)
                .map(|i| Proposition::Predicate {
                    name: format!("unrelated_{i}"),
                    arguments: vec![],
                })
                .collect::<Vec<_>>(),
        )
        .with_fact(Proposition::Predicate {
            name: "invariant".into(),
            arguments: vec![Term::ExecutionState(Box::new(
                entry.resource_state_source(),
            ))],
        });
        let core = ExecutionProofCore::at_entry(
            entry.clone(),
            ExecutionFrontier {
                region: ExecutionRegionKind::LoopBody,
                position: FrontierPosition::RegionBoundary,
                ..Default::default()
            },
        );
        let unprepared = root(facts.clone(), core);
        assert!(
            unprepared
                .validate_checked_invariant_lowerings(&checks, &[])
                .is_err()
        );
        let requested = unprepared
            .request_frontier_invariant_closure()
            .ok()
            .unwrap();
        assert!(
            requested
                .validate_checked_invariant_lowerings(&checks, &[])
                .is_err()
        );
        let (body, scope) = unprepared
            .open_invariant_body(
                &entry.clone(),
                &entry.clone(),
                &crate::kernel::IntegerTerm::var(crate::kernel::Variable(9_999)),
                &checks,
                &[],
                &[],
                &[],
                |_, _| (),
            )
            .unwrap();
        let completed = body.apply_normalize().ok().unwrap();
        let prepared = unprepared.retain_invariant_body(scope, &completed).unwrap();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            prepared.validate_checked_invariant_lowerings(&checks, &[])
        });
        result.unwrap();
        samples.push(work);
        assert!(
            prepared
                .validate_checked_invariant_lowerings(&[], &[])
                .is_err()
        );
        let changed_checks = vec![LoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(ProgramValue::Int32(MachineTerm::constant(1))),
                operator: ComparisonOperator::LessEqual,
                right: SpecExpression::Value(ProgramValue::Int32(MachineTerm::constant(1))),
            },
            None,
            None,
        )];
        assert!(
            prepared
                .validate_checked_invariant_lowerings(&changed_checks, &[])
                .is_err()
        );
        let core = prepared.execution_view().unwrap().execution().core.clone();
        let mut stale_effects = core.clone();
        stale_effects.effect_facts = Vec::new().into();
        assert!(
            root(facts.clone(), stale_effects)
                .validate_checked_invariant_lowerings(&checks, &[])
                .is_err()
        );
        let mut stale = core.clone();
        // Even an equal-valued replacement state is not the saved one.
        stale.state = ExecutionState::new()
            .with_population_creation_tracking()
            .into();
        assert!(
            root(facts.clone(), stale)
                .validate_checked_invariant_lowerings(&checks, &[])
                .is_err()
        );
        let other_facts = facts.with_fact(Proposition::Predicate {
            name: "other_arm".into(),
            arguments: vec![],
        });
        assert!(
            root(other_facts, core.clone())
                .validate_checked_invariant_lowerings(&checks, &[])
                .is_err()
        );
        let mut incomplete = core.clone();
        Arc::make_mut(incomplete.checked_invariant_lowerings.as_mut().unwrap()).body = None;
        assert!(
            root(facts.clone(), incomplete)
                .validate_checked_invariant_lowerings(&checks, &[])
                .is_err()
        );
        // A body for another judgment cannot certify this bundle.
        let mut incomplete = core.clone();
        Arc::make_mut(incomplete.checked_invariant_lowerings.as_mut().unwrap())
            .body
            .as_mut()
            .unwrap()
            .goal = Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(false), true);
        assert!(
            root(facts.clone(), incomplete)
                .validate_checked_invariant_lowerings(&checks, &[])
                .is_err()
        );
        prepared
            .validate_checked_invariant_lowerings(&checks, &[])
            .unwrap();
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(2).saturating_add(8),
            "closure work: {samples:?}"
        );
    }
}

fn pure_match_value(variants_count: usize) -> crate::kernel::AlgebraicTerm {
    use crate::kernel::{
        AlgebraicSchemas, AlgebraicTerm, AlgebraicTermNode, AlgebraicType, AlgebraicValueType,
        AlgebraicVariantType, ProgramType,
    };
    let key = AlgebraicValueType::Algebraic {
        name: "PureMatchScaling".into(),
        arguments: vec![],
    };
    let variants: Arc<[AlgebraicVariantType]> = (0..variants_count)
        .map(|index| AlgebraicVariantType {
            name: format!("Case{index}"),
            fields: vec![AlgebraicValueType::Program(ProgramType::Int32)],
        })
        .collect::<Vec<_>>()
        .into();
    AlgebraicTerm {
        algebraic_type: AlgebraicType {
            rigid: false,
            name: "PureMatchScaling".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: Arc::new(AlgebraicSchemas::new(std::collections::BTreeMap::from([(
                key, variants,
            )]))),
        },
        node: AlgebraicTermNode::Variable(Variable(2)),
    }
}

#[test]
fn pure_match_and_payload_freshening_ignore_unrelated_facts() {
    type TestProof = ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()>;
    let value = pure_match_value(1);
    let mut costs = Vec::new();
    for size in [16, 64, 256] {
        let facts = ProofFacts::from_ordered(
            &(0..size)
                .map(|i| Proposition::Predicate {
                    name: format!("unrelated_match_{i}"),
                    arguments: vec![Term::Bitvector32(MachineTerm::Variable(Variable(i)))],
                })
                .collect::<Vec<_>>(),
        );
        let root: TestProof = ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Proposition(PropositionObligation::new(
                    Proposition::ConditionIs(
                        crate::kernel::ConditionTerm::equal(
                            MachineTerm::Variable(Variable(1)),
                            MachineTerm::Variable(Variable(1)),
                        ),
                        true,
                    ),
                    (),
                )),
                ProofBranchState {
                    facts,
                    unfolded_predicates: PersistentOrderedSet::default(),
                    execution: None,
                },
            ),
        );
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let refined = root
                    .refine_proposition_algebraic_match(&value, &[0])
                    .unwrap();
                let field = refined.apply_intro(|_, _, _| ()).ok().unwrap();
                let case = field.apply_intro(|_, _, _| ()).ok().unwrap();
                assert_eq!(case.state.added_facts.len(), 1);
                assert!(case.apply_normalize().is_ok());
            })
        });
        costs.push((work, map_work));
    }
    for pair in costs.windows(2) {
        assert!(pair[1].0 <= pair[0].0 * 2, "{costs:?}");
        assert!(pair[1].1 <= pair[0].1 * 2, "{costs:?}");
    }
}

#[test]
fn pure_match_constructor_obligation_work_is_linear_in_the_family() {
    type TestProof = ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()>;
    let mut costs = Vec::new();
    for size in [16, 64, 256] {
        let value = pure_match_value(size);
        let root: TestProof = ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Proposition(PropositionObligation::new(
                    Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(true), true),
                    (),
                )),
                ProofBranchState {
                    facts: ProofFacts::from_ordered(&[]),
                    unfolded_predicates: PersistentOrderedSet::default(),
                    execution: None,
                },
            ),
        );
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            root.refine_proposition_algebraic_match(&value, &(0..size).collect::<Vec<_>>())
                .unwrap()
        });
        costs.push(work);
    }
    for pair in costs.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{costs:?}");
    }
}

#[test]
fn typed_universal_intro_adds_fresh_bounds_without_scanning_ambient_facts() {
    use crate::kernel::{ConditionTerm, MachineIntegerType};
    type TestProof = ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()>;
    let binder = Variable(186);
    let body = Proposition::Predicate {
        name: "holds".into(),
        arguments: vec![Term::Bitvector32(MachineTerm::Variable(binder))],
    };
    let goal = Proposition::ForAll {
        name: Default::default(),
        var: binder,
        sort: Sort::machine_integer(MachineIntegerType::UInt8),
        body: Box::new(body),
    };
    let sample = |size: u64, related: bool| {
        let ambient = (0..size)
            .map(|index| {
                Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        MachineTerm::Variable(if related {
                            binder
                        } else {
                            Variable(700_000 + index)
                        }),
                        MachineTerm::constant(1000 + index as u32),
                    ),
                    true,
                )
            })
            .collect::<Vec<_>>();
        let proof = TestProof::root(
            (),
            ProofBranch::new(
                ProofObligation::Proposition(PropositionObligation::new(goal.clone(), ())),
                ProofBranchState {
                    facts: ProofFacts::from_ordered(&ambient),
                    unfolded_predicates: PersistentOrderedSet::default(),
                    execution: None,
                },
            ),
        );
        let mut fresh = None;
        let (next, work) = crate::instrumentation::measure_deterministic_work(|| {
            proof
                .apply_intro(|_, introduction, _| {
                    if let PropositionIntroduction::Universal { variable, .. } = introduction {
                        fresh = Some(variable);
                    }
                })
                .unwrap_or_else(|_| panic!("typed universal introduction"))
        });
        let fresh = fresh.unwrap();
        if related {
            assert_ne!(fresh, binder);
        }
        // A `uint8` binder is a value of its own format: its range is the
        // format's, and introducing it files no fact.
        assert!(next.state().added_facts().is_empty());
        work
    };
    for related in [false, true] {
        let samples = [4, 16, 64, 256].map(|size| sample(size, related));
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 64),
            "intro work: {samples:?}"
        );
    }
}

/// The new computational leaf reads the goal, not the facts that happen to
/// share its variable. Exercise both success and refusal in cold contexts.
#[test]
fn known_computation_work_ignores_related_and_unrelated_facts() {
    use crate::kernel::{ConditionTerm, IntegerTerm};
    let mut hits = Vec::new();
    let mut misses = Vec::new();
    for size in [16u64, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = IntegerTerm::var(Variable(882_000));
        let facts = ProofFacts::from_ordered(
            &(0..size)
                .flat_map(|i| {
                    [
                        Proposition::ConditionIs(
                            ConditionTerm::integer_equal(
                                variable.clone(),
                                IntegerTerm::var(Variable(883_000 + i)),
                            ),
                            true,
                        ),
                        Proposition::ConditionIs(
                            ConditionTerm::integer_equal(
                                IntegerTerm::var(Variable(884_000 + i)),
                                IntegerTerm::var(Variable(885_000 + i)),
                            ),
                            true,
                        ),
                    ]
                })
                .collect::<Vec<_>>(),
        );
        let successor = IntegerTerm::add(variable.clone(), IntegerTerm::constant_i64(1));
        for (condition, expected, costs) in [
            (
                ConditionTerm::IntegerGreaterThan(
                    successor.clone().into(),
                    variable.clone().into(),
                ),
                true,
                &mut hits,
            ),
            (
                ConditionTerm::IntegerEqual(successor.into(), variable.into()),
                false,
                &mut misses,
            ),
        ] {
            let proof =
                known_computation_proof(Proposition::ConditionIs(condition, true), facts.clone());
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                proof.apply_known(PropositionKnownContext::Exact)
            });
            assert_eq!(result.is_ok(), expected);
            costs.push(work);
        }
    }
    for costs in [hits, misses] {
        assert!(
            costs[0] > 0 && costs.iter().all(|work| *work == costs[0]),
            "{costs:?}"
        );
    }
}

#[test]
fn known_computation_work_is_linear_in_shared_integer_terms() {
    use crate::kernel::{ConditionTerm, IntegerTerm};
    let mut costs = Vec::new();
    for depth in [16, 32, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut term: crate::kernel::SharedIntegerTerm = IntegerTerm::var(Variable(886_000)).into();
        for _ in 0..depth {
            term = IntegerTerm::Add(term.clone(), term).into();
        }
        let successor = IntegerTerm::add(term.as_ref().clone(), IntegerTerm::constant_i64(1));
        let proof = known_computation_proof(
            Proposition::ConditionIs(
                ConditionTerm::IntegerGreaterThan(successor.into(), term),
                true,
            ),
            ProofFacts::default(),
        );
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            proof.apply_known(PropositionKnownContext::Exact)
        });
        assert!(result.is_ok());
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.windows(2).all(|pair| pair[1] <= pair[0] * 3),
        "{costs:?}"
    );
}
