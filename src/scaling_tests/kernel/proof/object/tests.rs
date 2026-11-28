// Scaling tests of `src/kernel/proof/object.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn close_on_exact_contradiction_uses_bounded_work() {
    use crate::instrumentation::measure_deterministic_work;

    let _session = crate::kernel::VerificationSession::enter();
    let goal = Proposition::Predicate {
        name: "goal".into(),
        arguments: vec![],
    };
    let positive = Proposition::Predicate {
        name: "guard".into(),
        arguments: vec![],
    };
    let negative = Proposition::Not(Box::new(positive.clone()));
    let frontier = |facts| -> ProofObject<
        (),
        ProofObligation<(), Arc<OutcomeProofState<()>>>,
        ProofExecutionState<()>,
    > {
        ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Frontier(FrontierObligation),
                ProofBranchState {
                    facts,
                    execution: None,
                },
            ),
        )
    };

    let mut baseline = None;
    let mut frontier_baseline = None;
    for size in [0, 16, 64, 256] {
        let unrelated = (0..size)
            .map(|i| Proposition::Predicate {
                name: format!("unrelated_{i}"),
                arguments: vec![],
            })
            .collect::<Vec<_>>();
        let facts = PureFactStore::from_ordered(&unrelated).with_fact(positive.clone());
        let consistent = known_computation_proof(goal.clone(), facts.clone());
        let inconsistent_facts = facts.with_fact(negative.clone());
        let inconsistent = known_computation_proof(goal.clone(), inconsistent_facts.clone());
        let (closed, work) =
            measure_deterministic_work(|| inconsistent.apply_known(PropositionKnownContext::Exact));
        assert!(closed.is_ok(), "fact count {size}");
        assert_eq!(work, *baseline.get_or_insert(work), "fact count {size}");
        let dead_frontier = frontier(inconsistent_facts);
        let (closed, work) =
            measure_deterministic_work(|| dead_frontier.close_unreachable_frontier());
        assert!(closed.is_some_and(|closed| {
            closed
                .state()
                .open_branches()
                .get(closed.focused_branch())
                .is_none()
        }));
        assert_eq!(
            work,
            *frontier_baseline.get_or_insert(work),
            "fact count {size}"
        );
        assert!(frontier(facts).close_unreachable_frontier().is_none());
        assert!(
            consistent
                .apply_known(PropositionKnownContext::Exact)
                .is_err()
        );
    }
}

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
    let root = |facts: PureFactStore, core: ExecutionProofCore| -> TestProof {
        ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Frontier(FrontierObligation),
                ProofBranchState {
                    facts,
                    execution: Some(Arc::new(ProofExecutionState::new(core, ()))),
                },
            ),
        )
    };
    let checks = [0, 1].map(|value| {
        LoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(ProgramValue::Int32(OldMachineTerm::constant(value))),
                operator: ComparisonOperator::LessEqual,
                right: SpecExpression::Value(ProgramValue::Int32(OldMachineTerm::constant(value))),
            },
            None,
            None,
        )
    });
    let entry = ExecutionState::new();
    let samples = [16, 32, 64, 128].map(|size| {
        let facts = PureFactStore::from_ordered(
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
        let ((body, scope, edge), opening_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                let edge = frontier
                    .prepare_loop_invariant_edge(
                        &entry,
                        &entry,
                        &crate::kernel::IntegerTerm::var(crate::kernel::Variable(9_999)),
                        &checks,
                        &[],
                        Some(&[]),
                    )
                    .unwrap();
                let (body, scope) = frontier
                    .open_prepared_invariant_body(&edge, &[], |_, _| ())
                    .unwrap();
                (body, scope, edge)
            });
        assert!(
            frontier
                .retain_invariant_body(scope.clone(), &body)
                .is_err()
        );
        // Even the same exact goal and premises in a fresh root are not this scope.
        let unrelated = TestProof::root((), body.state.open_branches.root_branch().clone())
            .apply_known(PropositionKnownContext::Exact)
            .ok()
            .unwrap();
        assert!(
            frontier
                .retain_invariant_body(scope.clone(), &unrelated)
                .is_err()
        );
        let complete = body
            .apply_known(PropositionKnownContext::Exact)
            .ok()
            .unwrap();
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
                assert!(
                    stale
                        .open_prepared_invariant_body(&edge, &[], |_, _| ())
                        .is_err()
                );
            }
        }
        let mut wrong = core;
        Arc::make_mut(wrong.checked_invariant_lowerings.as_mut().unwrap())
            .body
            .as_mut()
            .unwrap()
            .goal =
            Proposition::condition_is(crate::kernel::OldConditionTerm::Constant(false), true);
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
    let root = |facts: PureFactStore, core: ExecutionProofCore| -> TestProof {
        ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Frontier(FrontierObligation),
                ProofBranchState {
                    facts,
                    execution: Some(Arc::new(ProofExecutionState::new(core, ()))),
                },
            ),
        )
    };
    let checks = vec![
        LoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(ProgramValue::Int32(OldMachineTerm::constant(0))),
                operator: ComparisonOperator::LessEqual,
                right: SpecExpression::Value(ProgramValue::Int32(OldMachineTerm::constant(0))),
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
        let facts = PureFactStore::from_ordered(
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
        let completed = body
            .apply_known(PropositionKnownContext::Exact)
            .ok()
            .unwrap();
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
                left: SpecExpression::Value(ProgramValue::Int32(OldMachineTerm::constant(1))),
                operator: ComparisonOperator::LessEqual,
                right: SpecExpression::Value(ProgramValue::Int32(OldMachineTerm::constant(1))),
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
            .goal =
            Proposition::condition_is(crate::kernel::OldConditionTerm::Constant(false), true);
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
        let facts = PureFactStore::from_ordered(
            &(0..size)
                .map(|i| Proposition::Predicate {
                    name: format!("unrelated_match_{i}"),
                    arguments: vec![Term::Bitvector32(
                        OldMachineTerm::Variable(Variable(i)).into(),
                    )],
                })
                .collect::<Vec<_>>(),
        );
        let root: TestProof = ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Proposition(PropositionObligation::new(
                    Proposition::condition_is(
                        crate::kernel::OldConditionTerm::equal(
                            OldMachineTerm::Variable(Variable(1)),
                            OldMachineTerm::Variable(Variable(1)),
                        ),
                        true,
                    ),
                    (),
                )),
                ProofBranchState {
                    facts,
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
                assert!(case.apply_known(PropositionKnownContext::Exact).is_ok());
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
                    Proposition::condition_is(
                        crate::kernel::OldConditionTerm::Constant(true),
                        true,
                    ),
                    (),
                )),
                ProofBranchState {
                    facts: PureFactStore::from_ordered(&[]),
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
    use crate::kernel::{MachineIntegerType, OldConditionTerm};
    type TestProof = ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()>;
    let binder = Variable(186);
    let body = Proposition::Predicate {
        name: "holds".into(),
        arguments: vec![Term::Bitvector32(OldMachineTerm::Variable(binder).into())],
    };
    let goal = crate::kernel::quantifiers::test_forall(
        Default::default(),
        binder,
        Sort::machine_integer(MachineIntegerType::UInt8),
        body,
    );
    let sample = |size: u64, related: bool| {
        let ambient = (0..size)
            .map(|index| {
                Proposition::condition_is(
                    OldConditionTerm::signed_less_than(
                        OldMachineTerm::Variable(if related {
                            binder
                        } else {
                            Variable(700_000 + index)
                        }),
                        OldMachineTerm::constant(1000 + index as u32),
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
                    facts: PureFactStore::from_ordered(&ambient),
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
    use crate::kernel::{IntegerTerm, OldConditionTerm};
    let mut hits = Vec::new();
    let mut misses = Vec::new();
    for size in [16u64, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = IntegerTerm::var(Variable(882_000));
        let facts = PureFactStore::from_ordered(
            &(0..size)
                .flat_map(|i| {
                    [
                        Proposition::condition_is(
                            OldConditionTerm::integer_equal(
                                variable.clone(),
                                IntegerTerm::var(Variable(883_000 + i)),
                            ),
                            true,
                        ),
                        Proposition::condition_is(
                            OldConditionTerm::integer_equal(
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
                OldConditionTerm::IntegerGreaterThan(
                    successor.clone().into(),
                    variable.clone().into(),
                ),
                true,
                &mut hits,
            ),
            (
                OldConditionTerm::IntegerEqual(successor.into(), variable.into()),
                false,
                &mut misses,
            ),
        ] {
            let proof =
                known_computation_proof(Proposition::condition_is(condition, true), facts.clone());
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn literal_constructor_field_known_work_scales_with_the_goal() {
    use crate::kernel::{
        AlgebraicSchemas, AlgebraicTerm, AlgebraicTermNode, AlgebraicType, AlgebraicValue,
        AlgebraicValueType, AlgebraicVariantType, OldConditionTerm, ProgramType, ProgramValue,
        VerificationSession,
    };
    let mut costs = Vec::new();
    for count in [4, 16, 64] {
        let _session = VerificationSession::enter();
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Wrap".into(),
            fields: vec![AlgebraicValueType::Program(ProgramType::Int32); count],
        }]
        .into();
        let ty = AlgebraicType {
            rigid: false,
            name: "LiteralFields".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(std::collections::BTreeMap::from(
                [(
                    AlgebraicValueType::Algebraic {
                        name: "LiteralFields".into(),
                        arguments: vec![],
                    },
                    variants,
                )],
            ))),
        };
        let field = |value| AlgebraicValue::Program(ProgramValue::Int32(value));
        let constructor = |last| {
            let mut fields = vec![field(OldMachineTerm::constant(0)); count - 1];
            fields.push(field(last));
            AlgebraicTerm {
                algebraic_type: ty.clone(),
                node: AlgebraicTermNode::Constructor {
                    variant: "Wrap".into(),
                    fields,
                },
            }
        };
        let goal = |last| {
            Proposition::condition_is(
                OldConditionTerm::AlgebraicEqual(
                    Box::new(constructor(OldMachineTerm::constant(0))),
                    Box::new(constructor(last)),
                ),
                false,
            )
        };
        let distinct = goal(OldMachineTerm::constant(1));
        let symbolic = goal(OldMachineTerm::Variable(Variable(970103)));
        let mut samples = [Vec::new(), Vec::new()];
        for size in [0, 16, 64, 256] {
            let facts = (0..size)
                .flat_map(|index| {
                    [
                        goal(OldMachineTerm::Variable(Variable(970104 + index))),
                        Proposition::Predicate {
                            name: format!("unrelated_{index}"),
                            arguments: vec![],
                        },
                    ]
                })
                .collect::<Vec<_>>();
            let facts = PureFactStore::from_ordered(&facts);
            for ((goal, expected), costs) in [(&distinct, true), (&symbolic, false)]
                .into_iter()
                .zip(&mut samples)
            {
                let proof = known_computation_proof(goal.clone(), facts.clone());
                let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                    proof.apply_known(PropositionKnownContext::Exact)
                });
                assert_eq!(result.is_ok(), expected);
                costs.push(work);
            }
        }
        // The empty store skips indexed fact lookups. Compare populated
        // stores to bound the additional work as those indexes grow.
        for work in &samples {
            let populated = &work[1..];
            assert!(
                populated.iter().all(|sample| *sample <= populated[0] + 16),
                "{work:?}"
            );
        }
        costs.push(samples[0][0]);
    }
    assert!(
        costs[0] > 0 && costs.windows(2).all(|pair| pair[1] <= pair[0] * 5),
        "{costs:?}"
    );
}

#[test]
fn computed_negations_known_work_scales_with_the_goal() {
    use crate::kernel::{IntegerTerm, OldConditionTerm, VerificationSession};

    let mut goal_costs = Vec::new();
    for leaves in [4, 16, 64] {
        let mut samples = [Vec::new(), Vec::new()];
        for size in [16, 64, 256] {
            let _session = VerificationSession::enter();
            let variable = IntegerTerm::var(Variable(972_000));
            let equal = |left, right| {
                Proposition::condition_is(OldConditionTerm::integer_equal(left, right), true)
            };
            let false_atom = Proposition::condition_is(OldConditionTerm::Constant(false), true);
            let unknown = equal(variable.clone(), IntegerTerm::constant_i64(0));
            let goal = |tail| {
                let disjunction = (1..leaves).fold(tail, |right, _| {
                    Proposition::Or(Box::new(false_atom.clone()), Box::new(right))
                });
                Proposition::Not(Box::new(disjunction))
            };
            let facts = (0..size)
                .flat_map(|index| {
                    [
                        equal(
                            variable.clone(),
                            IntegerTerm::var(Variable(972_001 + index)),
                        ),
                        Proposition::Predicate {
                            name: format!("unrelated_{index}"),
                            arguments: vec![],
                        },
                    ]
                })
                .collect::<Vec<_>>();
            let facts = PureFactStore::from_ordered(&facts);
            for ((tail, expected), costs) in [(false_atom.clone(), true), (unknown, false)]
                .into_iter()
                .zip(&mut samples)
            {
                let proof = known_computation_proof(goal(tail), facts.clone());
                let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                    proof.apply_known(PropositionKnownContext::Exact)
                });
                assert_eq!(result.is_ok(), expected);
                costs.push(work);
            }
        }
        for work in &samples {
            assert!(
                work.iter().all(|sample| *sample <= work[0] + 16),
                "{work:?}"
            );
        }
        goal_costs.push(samples[0][0]);
    }
    assert!(
        goal_costs[0] > 0 && goal_costs.windows(2).all(|pair| pair[1] <= pair[0] * 5),
        "{goal_costs:?}"
    );
}

#[test]
fn strict_literal_remainder_bound_known_work_ignores_context_growth() {
    use crate::kernel::{CompareRelation, MachineBinaryOp, MachineIntegerType, OldConditionTerm};
    let mut samples = [Vec::new(), Vec::new()];
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let dividend = OldMachineTerm::Variable(Variable(970500));
        let strict_bound = |left, right| {
            Proposition::condition_is(
                OldConditionTerm::machine_compare(format, CompareRelation::LessThan, left, right),
                true,
            )
        };
        let remainder = OldMachineTerm::Binary {
            format,
            op: MachineBinaryOp::Remainder,
            left: Box::new(dividend.clone()),
            right: Box::new(OldMachineTerm::uint64_constant(1000)),
        };
        let facts = (0..size)
            .flat_map(|index| {
                [
                    strict_bound(
                        dividend.clone(),
                        OldMachineTerm::Variable(Variable(971000 + index)),
                    ),
                    Proposition::Predicate {
                        name: format!("unrelated_{index}"),
                        arguments: vec![],
                    },
                ]
            })
            .collect::<Vec<_>>();
        let facts = PureFactStore::from_ordered(&facts);
        for ((bound, expected), costs) in [(1000, true), (999, false)].into_iter().zip(&mut samples)
        {
            let goal = strict_bound(remainder.clone(), OldMachineTerm::uint64_constant(bound));
            let proof = known_computation_proof(goal, facts.clone());
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                proof.apply_known(PropositionKnownContext::Exact)
            });
            assert_eq!(result.is_ok(), expected);
            costs.push(work);
        }
    }
    for costs in samples {
        assert!(
            costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 16),
            "{costs:?}"
        );
    }
}

#[test]
fn unsigned_remainder_dividend_bound_known_work_ignores_context_growth() {
    use crate::kernel::{CompareRelation, MachineBinaryOp, MachineIntegerType, OldConditionTerm};
    let mut samples = [Vec::new(), Vec::new()];
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let dividend = OldMachineTerm::Variable(Variable(975_500));
        let divisor = OldMachineTerm::Variable(Variable(975_501));
        let relation = |relation, left, right| {
            Proposition::condition_is(
                OldConditionTerm::machine_compare(ty, relation, left, right),
                true,
            )
        };
        let positive = |value| {
            relation(
                CompareRelation::LessThan,
                OldMachineTerm::uint64_constant(0),
                value,
            )
        };
        let goal = relation(
            CompareRelation::LessEqual,
            OldMachineTerm::Binary {
                format: ty,
                op: MachineBinaryOp::Remainder,
                left: Box::new(dividend.clone()),
                right: Box::new(divisor.clone()),
            },
            dividend,
        );
        let facts = (0..size)
            .flat_map(|index| {
                [
                    relation(
                        CompareRelation::LessThan,
                        divisor.clone(),
                        OldMachineTerm::Variable(Variable(976_000 + index)),
                    ),
                    Proposition::Predicate {
                        name: format!("unrelated_{index}"),
                        arguments: vec![],
                    },
                ]
            })
            .collect::<Vec<_>>();
        let facts = PureFactStore::from_ordered(&facts);
        for (expected, costs) in [true, false].into_iter().zip(&mut samples) {
            let facts = if expected {
                facts.with_fact(positive(divisor.clone()))
            } else {
                facts.clone()
            };
            let proof = known_computation_proof(goal.clone(), facts);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                proof.apply_known(PropositionKnownContext::Exact)
            });
            assert_eq!(result.is_ok(), expected);
            costs.push(work);
        }
    }
    for costs in samples {
        assert!(
            costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 16),
            "{costs:?}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: signed quotient hit and miss scaling took 0.6s"]
fn signed_quotient_sign_known_work_ignores_context_growth() {
    use crate::kernel::{CompareRelation, MachineBinaryOp, MachineIntegerType, OldConditionTerm};
    let mut samples = [Vec::new(), Vec::new()];
    for size in [8, 32, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let n = OldMachineTerm::Variable(Variable(977_500));
        let d = OldMachineTerm::Variable(Variable(977_501));
        let zero = OldMachineTerm::constant(0);
        let relation = |relation, left, right, truth| {
            Proposition::condition_is(
                OldConditionTerm::machine_compare(ty, relation, left, right),
                truth,
            )
        };
        let goal = relation(
            CompareRelation::LessEqual,
            zero.clone(),
            OldMachineTerm::Binary {
                format: ty,
                op: MachineBinaryOp::Divide,
                left: Box::new(n.clone()),
                right: Box::new(d.clone()),
            },
            true,
        );
        let mut facts = vec![
            relation(CompareRelation::LessEqual, n.clone(), zero.clone(), true),
            relation(CompareRelation::LessThan, d.clone(), zero, true),
        ];
        for index in 0..size {
            facts.push(relation(
                CompareRelation::LessThan,
                d.clone(),
                OldMachineTerm::Variable(Variable(978_000 + index)),
                true,
            ));
            facts.push(Proposition::Predicate {
                name: format!("unrelated_{index}"),
                arguments: vec![],
            });
        }
        let facts = PureFactStore::from_ordered(&facts);
        for (expected, costs) in [true, false].into_iter().zip(&mut samples) {
            let facts = if expected {
                facts.with_fact(relation(
                    CompareRelation::Equal,
                    n.clone(),
                    OldMachineTerm::constant(i32::MIN as u32),
                    false,
                ))
            } else {
                facts.clone()
            };
            let proof = known_computation_proof(goal.clone(), facts);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                proof.apply_known(PropositionKnownContext::Exact)
            });
            assert_eq!(result.is_ok(), expected);
            costs.push(work);
        }
    }
    for costs in samples {
        assert!(
            costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 16),
            "{costs:?}"
        );
    }
}

#[test]
fn unchanged_machine_fold_known_work_ignores_context_growth() {
    use crate::kernel::{CompareRelation, MachineIntegerType, OldConditionTerm};
    let _session = crate::kernel::VerificationSession::enter();
    let seed = OldMachineTerm::Variable(Variable(984_001));
    let end = OldMachineTerm::Variable(Variable(984_002));
    let accumulator = Variable(984_003);
    let item = Variable(984_004);
    let comparison = |relation, left, right| {
        Proposition::condition_is(
            OldConditionTerm::machine_compare(MachineIntegerType::Int32, relation, left, right),
            true,
        )
    };
    let measurements = [8, 32, 64].map(|size| {
        let facts = (0..size)
            .flat_map(|index| {
                [
                    comparison(
                        CompareRelation::LessEqual,
                        end.clone(),
                        OldMachineTerm::Variable(Variable(985_000 + index)),
                    ),
                    Proposition::Predicate {
                        name: format!("unrelated_{index}"),
                        arguments: vec![],
                    },
                ]
            })
            .collect::<Vec<_>>();
        let facts = PureFactStore::from_ordered(&facts);
        [accumulator, item].map(|body| {
            let fold = OldMachineTerm::RangeFold {
                start: Box::new(OldMachineTerm::constant(0)),
                end: Box::new(end.clone()),
                initial: Box::new(seed.clone()),
                accumulator,
                item,
                body: Box::new(OldMachineTerm::Variable(body)),
            };
            let goal = comparison(CompareRelation::Equal, fold, seed.clone());
            let proof = known_computation_proof(goal, facts.clone());
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                proof.apply_known(PropositionKnownContext::Exact)
            });
            assert_eq!(result.is_ok(), body == accumulator);
            work
        })
    });
    for work in measurements {
        for (sample, baseline) in work.into_iter().zip(measurements[0]) {
            assert!(sample <= baseline + 16, "{measurements:?}");
        }
    }
}

#[test]
fn unfolded_machine_range_known_work_ignores_context_growth() {
    use crate::kernel::{CompareRelation, MachineBinaryOp, MachineIntegerType, OldConditionTerm};
    let _session = crate::kernel::VerificationSession::enter();
    let ty = MachineIntegerType::UInt64;
    let input = OldMachineTerm::Variable(Variable(996_001));
    let word = OldMachineTerm::uint64_constant;
    let guard =
        OldConditionTerm::machine_compare(ty, CompareRelation::LessThan, input.clone(), word(10));
    let decimal_length = OldMachineTerm::logical_machine_binary(
        ty,
        MachineBinaryOp::Add,
        word(1),
        OldMachineTerm::If {
            condition: guard.into(),
            then_term: word(0).into(),
            else_term: word(1).into(),
        },
    );
    let samples = [8, 32, 64].map(|count| {
        let facts = (0..count)
            .flat_map(|i| {
                [
                    Proposition::condition_is(
                        OldConditionTerm::machine_compare(
                            ty,
                            CompareRelation::LessEqual,
                            input.clone(),
                            word(100 + i),
                        ),
                        true,
                    ),
                    Proposition::Predicate {
                        name: format!("unrelated_{i}"),
                        arguments: vec![],
                    },
                ]
            })
            .collect::<Vec<_>>();
        let facts = PureFactStore::from_ordered(&facts);
        [2, 1].map(|bound| {
            let goal = Proposition::condition_is(
                OldConditionTerm::machine_compare(
                    ty,
                    CompareRelation::LessEqual,
                    decimal_length.clone(),
                    word(bound),
                ),
                true,
            );
            let proof = known_computation_proof(goal, facts.clone());
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                proof.apply_known(PropositionKnownContext::Exact)
            });
            assert_eq!(result.is_ok(), bound == 2);
            work
        })
    });
    for sample in samples {
        for (work, baseline) in sample.into_iter().zip(samples[0]) {
            assert!(work <= baseline + 16, "{samples:?}");
        }
    }
}

#[test]
fn known_computation_work_is_linear_in_shared_integer_terms() {
    use crate::kernel::{IntegerTerm, OldConditionTerm};
    let mut costs = Vec::new();
    for depth in [16, 32, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut term: crate::kernel::SharedIntegerTerm = IntegerTerm::var(Variable(886_000)).into();
        for _ in 0..depth {
            term = IntegerTerm::Add(term.clone(), term).into();
        }
        let successor = IntegerTerm::add(term.as_ref().clone(), IntegerTerm::constant_i64(1));
        let proof = known_computation_proof(
            Proposition::condition_is(
                OldConditionTerm::IntegerGreaterThan(successor.into(), term),
                true,
            ),
            PureFactStore::default(),
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

#[test]
fn apply_fact_uses_only_selected_implication_and_evidence() {
    type TestProof = ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()>;
    let atom = |name: String| Proposition::Predicate {
        name,
        arguments: vec![],
    };
    let antecedent = atom("selected_antecedent".into());
    let conclusion = atom("selected_conclusion".into());
    let implication =
        Proposition::Implies(Box::new(antecedent.clone()), Box::new(conclusion.clone()));
    let mut samples = Vec::new();
    for size in [4, 16, 64, 256] {
        let mut facts = vec![antecedent.clone(), implication.clone()];
        for index in 0..size {
            facts.push(atom(format!("unrelated_{index}")));
            // Grow the exact same consequent bucket, so a hidden source
            // search cannot pass by merely ignoring unrelated facts.
            facts.push(Proposition::Implies(
                Box::new(atom(format!("other_antecedent_{index}"))),
                Box::new(conclusion.clone()),
            ));
        }
        let root: TestProof = ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Proposition(PropositionObligation::new(conclusion.clone(), ())),
                ProofBranchState {
                    facts: PureFactStore::from_ordered(&facts),
                    execution: None,
                },
            ),
        );
        let (((), work), maps) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for applied in [
                    root.apply_fact(&implication, std::slice::from_ref(&antecedent)),
                    root.apply_fact_from_scope(&implication),
                ] {
                    let applied = applied.unwrap();
                    assert!(!applied.is_complete());
                    assert!(applied.focused_proposition().unwrap().1.contains(&conclusion));
                }
                assert!(root.apply_fact(&implication, &[]).is_err());
                assert!(
                    root.apply_fact(&implication, &[atom("missing".into())])
                        .is_err()
                );
                let missing = Proposition::Implies(
                    Box::new(atom("missing".into())),
                    Box::new(conclusion.clone()),
                );
                assert!(
                    root.apply_fact(&missing, std::slice::from_ref(&antecedent))
                        .is_err()
                );
                assert!(root.apply_fact_from_scope(&missing).is_err());
                assert!(
                    !root.is_complete(),
                    "application must leave the persistent input unchanged"
                );
            })
        });
        samples.push((work, maps));
    }
    assert!(
        samples
            .iter()
            .all(|(work, _)| *work <= samples[0].0 * 3 + 16),
        "work: {samples:?}"
    );
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 2 + 16,
            "persistent work: {samples:?}"
        );
    }
}

#[test]
fn known_quantified_identity_uses_selected_keys() {
    type TestProof = ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()>;
    let quantified = |binder, index| {
        crate::kernel::quantifiers::test_forall(
            Default::default(),
            Variable(binder),
            crate::kernel::Sort::ProgramInt32,
            Proposition::Predicate {
                name: "quantified_identity".into(),
                arguments: vec![
                    Term::ProgramValue(
                        (crate::kernel::ProgramValue::Int32(OldMachineTerm::Variable(Variable(
                            binder,
                        ))))
                        .into(),
                    ),
                    Term::ProgramValue(
                        (crate::kernel::ProgramValue::Int32(OldMachineTerm::constant(index)))
                            .into(),
                    ),
                ],
            },
        )
    };
    let mut samples = Vec::new();
    for size in [4u32, 16, 64, 256] {
        let mut facts = vec![quantified(1, 0)];
        for index in 1..=size {
            facts.push(quantified(1, index));
            facts.push(Proposition::Predicate {
                name: format!("unrelated_{index}"),
                arguments: vec![],
            });
        }
        let facts = PureFactStore::from_ordered(&facts);
        let root = |goal| -> TestProof {
            ProofObject::root(
                (),
                ProofBranch::new(
                    ProofObligation::Proposition(PropositionObligation::new(goal, ())),
                    ProofBranchState {
                        facts: facts.clone(),
                        execution: None,
                    },
                ),
            )
        };
        let hit = root(quantified(999, 0));
        let miss = root(quantified(999, 9999));
        let (((), work), maps) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(
                    hit.apply_known(PropositionKnownContext::Materialized)
                        .ok()
                        .unwrap()
                        .is_complete()
                );
                assert!(
                    miss.apply_known(PropositionKnownContext::Materialized)
                        .is_err()
                );
            })
        });
        samples.push((work, maps));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].0 <= pair[0].0 * 2 + 16,
            "identity work: {samples:?}"
        );
        assert!(
            pair[1].1 <= pair[0].1 * 2 + 16,
            "identity map work: {samples:?}"
        );
    }
}

#[test]
fn apply_fact_quantified_sources_use_selected_alpha_keys() {
    type TestProof = ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()>;
    let guard = Proposition::Predicate {
        name: "selected_guard".into(),
        arguments: vec![],
    };
    let quantified = |binder, value| {
        crate::kernel::quantifiers::test_exists(
            Default::default(),
            Variable(binder),
            crate::kernel::Sort::ProgramInt32,
            Proposition::Predicate {
                name: "selected_body".into(),
                arguments: vec![
                    Term::ProgramValue(
                        (crate::kernel::ProgramValue::Int32(OldMachineTerm::Variable(Variable(
                            binder,
                        ))))
                        .into(),
                    ),
                    Term::ProgramValue(
                        (crate::kernel::ProgramValue::Int32(OldMachineTerm::constant(value)))
                            .into(),
                    ),
                ],
            },
        )
    };
    let implication = |body| Proposition::Implies(Box::new(guard.clone()), Box::new(body));
    let mut samples = Vec::new();
    for size in [4u32, 16, 64, 256] {
        let goal = quantified(1, 0);
        let mut facts = vec![guard.clone(), implication(goal.clone())];
        for index in 1..=size {
            // Same guard and quantified shape, but a different free value.
            facts.push(implication(quantified(1, index)));
            facts.push(Proposition::Predicate {
                name: format!("unrelated_{index}"),
                arguments: vec![],
            });
        }
        let root: TestProof = ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Proposition(PropositionObligation::new(goal, ())),
                ProofBranchState {
                    facts: PureFactStore::from_ordered(&facts),
                    execution: None,
                },
            ),
        );
        let (((), work), maps) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let successor = root
                    .apply_fact(
                        &implication(quantified(999, 0)),
                        std::slice::from_ref(&guard),
                    )
                    .unwrap();
                assert!(!successor.is_complete());
                let successor = successor
                    .apply_known(PropositionKnownContext::Pure)
                    .unwrap_or_else(|_| {
                        panic!("the applied existential must be available up to binder renaming")
                    });
                assert!(successor.is_complete());
                assert!(
                    root.apply_fact(
                        &implication(quantified(999, u32::MAX)),
                        std::slice::from_ref(&guard)
                    )
                    .is_err()
                );
                assert!(
                    root.apply_fact(&implication(quantified(999, 0)), &[])
                        .is_err()
                );
                assert!(!root.is_complete());
            })
        });
        samples.push((work, maps));
    }
    assert!(
        samples
            .iter()
            .all(|(work, _)| *work <= samples[0].0 * 3 + 16),
        "{samples:?}"
    );
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 2 + 16, "{samples:?}");
    }
}

#[test]
fn known_compound_comparison_work_is_linear_in_selected_clauses() {
    use crate::kernel::machine_integer::comparison::retained_arithmetic_comparison;
    use crate::kernel::{KernelTermExport, OldConditionTerm};
    let mut costs = Vec::new();
    for size in [8, 16, 32, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let clause = |id: u64, shared| {
            let leaf = |bound| {
                let native = OldConditionTerm::equal(
                    OldMachineTerm::Binary {
                        format: crate::kernel::MachineIntegerType::Int32,
                        op: crate::kernel::MachineBinaryOp::Add,
                        left: Box::new(OldMachineTerm::Variable(Variable(989_000 + id))),
                        right: Box::new(OldMachineTerm::constant(1)),
                    },
                    OldMachineTerm::constant(bound),
                );
                Proposition::condition_is(
                    if shared {
                        retained_arithmetic_comparison(&native).unwrap()
                    } else {
                        native
                    },
                    true,
                )
            };
            Proposition::Or(Box::new(leaf(0)), Box::new(leaf(1)))
        };
        let sources = (0..size).map(|id| clause(id, false)).collect::<Vec<_>>();
        let facts = PureFactStore::from_ordered(&sources);
        let goal = (1..size).fold(clause(0, true), |goal, id| {
            Proposition::And(Box::new(goal), Box::new(clause(id, true)))
        });
        let proof = known_computation_proof(goal, facts);
        let exports = KernelTermExport::machine_export_count();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            proof.apply_known(PropositionKnownContext::Exact)
        });
        assert!(result.is_ok());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.windows(2).all(|pair| pair[1] <= pair[0] * 3),
        "{costs:?}"
    );
}

#[test]
fn automatic_object_separation_ignores_ambient_address_facts() {
    use crate::kernel::{
        Address, AddressBase, AddressOffset, LocalBindingId, LocalFunctionId, LocalStorageInstance,
        MemoryRange, OldConditionTerm, Resource, Variable,
    };

    let _session = crate::kernel::VerificationSession::enter();
    let function = LocalFunctionId::new(Some("separation.c".into()), "f".into());
    let local = |index| {
        Address::new(
            AddressBase::AutomaticLocal {
                binding: LocalBindingId::new(function.clone(), false, index, None),
                instance: LocalStorageInstance::Implicit,
            },
            AddressOffset::constant(0),
        )
    };
    let selected = local(0);
    let incoming = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
    let alias = Address::symbolic(Variable(1));
    let resource = |pointer| {
        Box::new(Resource::Memory(MemoryRange::new_with_element_width(
            pointer,
            OldMachineTerm::constant(0),
            OldMachineTerm::constant(1),
            4,
        )))
    };
    let separate = |left, right| Proposition::ResourceSeparate {
        left: resource(left),
        right: resource(right),
    };
    let goals = [
        (separate(selected.clone(), incoming.clone()), true),
        (separate(incoming, selected.clone()), true),
        (separate(local(1), selected.clone()), true),
        (
            separate(selected.clone(), selected.offset_by_bytes(1)),
            false,
        ),
        (separate(selected.clone(), alias.clone()), false),
    ];
    let samples = [4u64, 16, 64, 256].map(|size| {
        let mut facts = vec![Proposition::condition_is(
            OldConditionTerm::address_equal(selected.clone(), alias.clone()),
            true,
        )];
        for i in 0..size {
            facts.push(Proposition::condition_is(
                OldConditionTerm::address_equal(alias.clone(), Address::symbolic(Variable(10 + i))),
                true,
            ));
            facts.push(Proposition::Predicate {
                name: format!("unrelated_{i}"),
                arguments: vec![],
            });
        }
        let facts = PureFactStore::from_ordered(&facts);
        let proofs = goals
            .each_ref()
            .map(|(goal, _)| known_computation_proof(goal.clone(), facts.clone()));
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for (proof, (_, expected)) in proofs.iter().zip(&goals) {
                assert_eq!(
                    proof
                        .apply_known(PropositionKnownContext::Materialized)
                        .is_ok_and(|closed| closed.is_complete()),
                    *expected
                );
            }
        });
        work
    });
    assert!(
        samples[0] > 0 && samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn selected_match_conditionals_known_work_ignores_context_growth() {
    use crate::kernel::{CompareRelation, MachineIntegerType, OldConditionTerm};
    let _session = crate::kernel::VerificationSession::enter();
    let payload = OldMachineTerm::Variable(Variable(986_000));
    let expected = OldMachineTerm::Variable(Variable(986_001));
    let compare = |relation, left, right| {
        OldConditionTerm::machine_compare(MachineIntegerType::Int32, relation, left, right)
    };
    let conditional = |left, right, then_term| OldMachineTerm::If {
        condition: Box::new(OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(left),
            right: Box::new(right),
        }),
        then_term: Box::new(then_term),
        else_term: Box::new(OldMachineTerm::constant(0)),
    };
    let measurements = [8, 32, 64].map(|size| {
        let facts = (0..size)
            .flat_map(|index| {
                [
                    Proposition::condition_is(
                        compare(
                            CompareRelation::LessEqual,
                            payload.clone(),
                            OldMachineTerm::Variable(Variable(987_000 + index)),
                        ),
                        true,
                    ),
                    Proposition::Predicate {
                        name: format!("unrelated_{index}"),
                        arguments: vec![],
                    },
                ]
            })
            .collect::<Vec<_>>();
        let facts = PureFactStore::from_ordered(&facts);
        [&payload, &expected].map(|guard_value| {
            let nested = conditional(
                payload.clone(),
                payload.clone(),
                conditional(
                    payload.clone(),
                    guard_value.clone(),
                    OldMachineTerm::constant(1),
                ),
            );
            let goal = Proposition::condition_is(
                compare(CompareRelation::Equal, nested, OldMachineTerm::constant(1)),
                true,
            );
            let proof = known_computation_proof(goal, facts.clone());
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                proof.apply_known(PropositionKnownContext::Exact)
            });
            assert_eq!(result.is_ok(), guard_value == &payload);
            work
        })
    });
    for work in measurements {
        for (sample, baseline) in work.into_iter().zip(measurements[0]) {
            assert!(sample <= baseline + 16, "{measurements:?}");
        }
    }
}

#[test]
fn pointer_index_projection_looks_up_only_its_full_width_bound() {
    use crate::kernel::OffsetTree;
    use crate::kernel::proof::fact_reasoning::{known_bridge_leaf, pointer_projection_source};
    use crate::kernel::{AddressOffset, OldConditionTerm, VerificationSession};
    let _session = VerificationSession::enter();
    let index = OldMachineTerm::Variable(Variable(970_020));
    let narrow = AddressOffset::scaled_int32_node(OldMachineTerm::uint32_from_64(index.clone()), 4);
    let wide = AddressOffset::scaled_int64_node(index.clone(), 4, true);
    let at_parameter =
        |offset| AddressOffset::add(AddressOffset::variable(Variable(970_021)), offset);
    let compare = OldConditionTerm::address_offset_equal(at_parameter(narrow), at_parameter(wide));
    let wide = pointer_projection_source(&compare).unwrap();
    let goal = Proposition::condition_is(compare, true);
    let exact = Proposition::condition_is(
        OldConditionTerm::IntegerLessEqual(
            wide.into(),
            crate::kernel::IntegerTerm::constant_i64(i64::from(i32::MAX)).into(),
        ),
        true,
    );
    let work = [8, 32, 64].map(|size| {
        let mut premises = Vec::new();
        for i in 0..size {
            premises.push(Proposition::condition_is(
                OldConditionTerm::uint64_less_equal(
                    index.clone(),
                    OldMachineTerm::uint64_constant(4_000_000_000 + i),
                ),
                true,
            ));
            premises.push(Proposition::Predicate {
                name: format!("projection_other_{i}"),
                arguments: Vec::new(),
            });
        }
        [false, true].map(|present| {
            let mut premises = premises.clone();
            if present {
                premises.push(exact.clone());
            }
            let facts = PureFactStore::from_ordered(&premises);
            let (closed, units) = crate::instrumentation::measure_deterministic_work(|| {
                known_bridge_leaf(&goal, &|p| facts.pure_known_available(p))
            });
            assert_eq!(closed, present);
            units
        })
    });
    assert!(
        work.iter().all(|pair| pair
            .iter()
            .zip(work[0])
            .all(|(actual, baseline)| *actual <= baseline + 32)),
        "{work:?}"
    );
}

#[test]
fn known_constructor_order_looks_up_only_the_selected_payload_bound() {
    use crate::kernel::{
        AlgebraicBitvectorMatchArm, AlgebraicTermNode, AlgebraicValue, AlgebraicValueType,
        CompareRelation, KernelMatch, MachineIntegerType, OldConditionTerm, ProgramType,
        ProgramValue,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let payload = OldMachineTerm::Variable(Variable(986_001));
    let binding = OldMachineTerm::Variable(Variable(986_002));
    let field = |term| AlgebraicValue::Program(ProgramValue::Int32(term));
    let mut scrutinee =
        KernelMatch::test_scrutinee(vec![AlgebraicValueType::Program(ProgramType::Int32)]);
    scrutinee.node = AlgebraicTermNode::Constructor {
        variant: "Arm".into(),
        fields: vec![field(payload.clone())],
    };
    let matched = OldMachineTerm::AlgebraicMatch {
        scrutinee: Box::new(scrutinee),
        arms: vec![AlgebraicBitvectorMatchArm {
            variant: "Arm".into(),
            bindings: vec![field(binding.clone())],
            body: binding,
            binding_names: Default::default(),
        }],
    };
    let bound = |term, upper| {
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(term),
                right: Box::new(OldMachineTerm::constant(upper)),
            },
            true,
        )
    };
    let measurements = [8, 32, 128].map(|size| {
        let mut premises = vec![bound(payload.clone(), 9)];
        for index in 0..size {
            premises.push(bound(payload.clone(), 100 + index));
            premises.push(bound(
                OldMachineTerm::Variable(Variable(987_000 + u64::from(index))),
                9,
            ));
        }
        let sibling = PureFactStore::from_ordered(&premises[1..]);
        let written = bound(matched.clone(), 9);
        let context = sibling.assumptions();
        let (interval, admission_work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .clone()
                .assume_proposition(written)
                .indexed_constant_interval(&payload)
        });
        assert_eq!(interval, Some((i64::from(i32::MIN), 8)));
        assert_eq!(
            context.indexed_constant_interval(&payload),
            Some((i64::from(i32::MIN), 99))
        );
        let facts = PureFactStore::from_ordered(&premises);
        let known_work = [9, 8].map(|upper| {
            let proof = known_computation_proof(bound(matched.clone(), upper), facts.clone());
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                proof.apply_known(PropositionKnownContext::Exact)
            });
            assert_eq!(result.is_ok(), upper == 9);
            work
        });
        [admission_work, known_work[0], known_work[1]]
    });
    for work in measurements {
        for (sample, baseline) in work.into_iter().zip(measurements[0]) {
            assert!(sample <= baseline + 24, "{measurements:?}");
        }
    }
}
