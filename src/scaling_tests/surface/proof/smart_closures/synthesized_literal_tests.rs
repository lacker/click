// Scaling tests of `src/surface/proof/smart_closures.rs` (module `synthesized_literal_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn speculative_simp_premise_spelling_declines_large_components_without_rendering() {
    let function = syntax::parse_function("int32 noop() { return 0; }").unwrap();
    let state = CState::new();
    let snapshots = RecordedSnapshots::new();
    let surfaces = SurfacePropositionMap::default();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let proof = Proof::for_fixed_state_goal(
        "speculative premise rendering",
        0,
        &[],
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Constant(0)),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        ),
        ParameterBinding::new(function.parameters(), &[]),
        &state,
        &state,
        &snapshots,
        &surfaces,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
        &[],
        &[],
    );
    for size in [128, 512, 2048, 8192] {
        let premises = (0..size)
            .map(|index| {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(Bitvector32Term::Variable(Variable(8_179_000 + index))),
                        Box::new(Bitvector32Term::Constant(0)),
                    ),
                    true,
                )
            })
            .collect::<Vec<_>>();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            proof.resolve_simp_premises(&premises, &[])
        });
        assert!(
            result.is_none(),
            "an oversized speculative component must be declined"
        );
        assert_eq!(work, 0, "size {size}: no candidate should be rendered");
    }
}

#[test]
fn reflexive_pointer_metadata_does_not_search_snapshot_history() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let pointer = Pointer::symbolic(Variable(8_179_830));
    let state = CState::new().with_local("p", CValue::pointer(pointer.clone()));
    let reflexive = Proposition::ConditionIs(
        ConditionTerm::PointerEqual(Box::new(pointer.clone()), Box::new(pointer)),
        true,
    );
    let equivalent = Proposition::Not(Box::new(match &reflexive {
        Proposition::ConditionIs(condition, _) => {
            Proposition::ConditionIs(condition.clone(), false)
        }
        _ => unreachable!(),
    }));
    let facts = [reflexive.clone(), equivalent.clone()];
    let surfaces = SurfacePropositionMap::default();
    for size in [4usize, 16, 64, 256] {
        let mut snapshots = RecordedSnapshots::new();
        for index in 0..size {
            snapshots.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Statement(index),
                    kind: ProgramPointKind::Entry,
                },
                state.clone(),
            );
        }
        let anchor = ProgramPointRef {
            region: CodeRegionRef::Statement(size - 1),
            kind: ProgramPointKind::Entry,
        };
        let root = Proof::for_fixed_state_goal_with_requirements(
            "reflexive pointer metadata",
            0,
            &facts,
            Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            ParameterBinding::default(),
            FixedStateFrame::new(&state, &state, None, &snapshots),
            Some(&anchor),
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
            &[],
        );
        for fact in &facts {
            let ((surface, events), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    crate::instrumentation::collect(|| {
                        root.available_surface_fact(&surfaces, Some(&anchor), fact)
                    })
                });
            assert!(surface.is_none());
            assert!(work <= 32, "{size} snapshots: {work} work");
            assert!(
                !events.iter().any(|event| matches!(event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name.starts_with("simp premise surface"))),
                "metadata must not walk history"
            );
            assert!(
                root.facts().contains(fact),
                "search leaves the kernel fact available"
            );
        }
    }
}

#[test]
fn native_signed_certificate_results_do_not_walk_ambient_facts() {
    use crate::kernel::proof::signed_arithmetic::{
        SignedArithmeticCarrier, SignedArithmeticCertificate, SignedArithmeticClaim,
        SignedArithmeticNode, SignedArithmeticRelation, add_claim, signed_arithmetic_claim,
    };
    let function = syntax::parse_function("int32 noop(int32 x) { return x; }").unwrap();
    let x = Bitvector32Term::Variable(Variable(8_172_000));
    let arguments = [CExpression::Value(CValue::Int32(x.clone()))];
    let premise = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessEqual(
            Box::new(x),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        true,
    );
    let original = signed_arithmetic_claim(&premise).unwrap();
    let slack = SignedArithmeticClaim {
        carrier: SignedArithmeticCarrier::SignedInt32,
        relation: SignedArithmeticRelation::LessEqual,
        terms: BTreeMap::new(),
        constant: BigInt::from(-1),
    };
    let sum = add_claim(&original, &slack).unwrap();
    let plan = SignedArithmeticCertificate {
        nodes: vec![
            SignedArithmeticNode::Premise {
                index: 0,
                result: original,
            },
            SignedArithmeticNode::Trivial { result: slack },
            SignedArithmeticNode::Add {
                left: 0,
                right: 1,
                result: sum,
            },
        ],
        conclusion: 0,
    };
    let surface = ClickProposition::Comparison {
        left: ContractExpression::CFragment(CExpression::Variable("x".into())),
        operator: ComparisonOperator::LessEqual,
        right: ContractExpression::IntegerLiteral("1".into()),
    };
    let pairs = [(premise.clone(), surface.clone())];
    let state = CState::new();
    let snapshots = RecordedSnapshots::new();
    let surfaces = SurfacePropositionMap::default();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let mut baseline = None;
    for size in [4, 16, 64, 256] {
        let mut facts = (0..size)
            .map(|i| {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(Bitvector32Term::Variable(Variable(8_173_000 + i))),
                        Box::new(Bitvector32Term::Constant(0)),
                    ),
                    true,
                )
            })
            .collect::<Vec<_>>();
        facts.push(premise.clone());
        let proof = Proof::for_fixed_state_goal(
            "native certificate result",
            0,
            &facts,
            premise.clone(),
            ParameterBinding::new(function.parameters(), &arguments),
            &state,
            &state,
            &snapshots,
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
        );
        let (certificate, work) = crate::instrumentation::measure_deterministic_work(|| {
            proof.signed_plan_to_surface_certificate(&plan, &pairs, &surface)
        });
        let certificate = certificate.unwrap();
        assert!(matches!(
            &certificate.nodes[2],
            SignedArithmeticStep::Add {
                result: ClickProposition::Comparison {
                    left: ContractExpression::CUnary { .. },
                    right: ContractExpression::CUnary { .. },
                    ..
                },
                ..
            }
        ));
        assert_eq!(
            work,
            *baseline.get_or_insert(work),
            "ambient {size}: certificate emission must stay local"
        );
        eprintln!("ambient facts={size}, certificate emission work={work}");
    }
}
