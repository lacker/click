use super::*;

#[test]
fn integer_certificate_lowering_scales_with_nodes_not_unrelated_bindings() {
    use crate::kernel::{IntegerTerm, SpecIntegerExpression};
    let surface = ClickProposition::Comparison {
        left: ContractExpression::Add(
            Box::new(ContractExpression::Binding("x".into())),
            Box::new(ContractExpression::IntegerLiteral("1".into())),
        ),
        operator: ComparisonOperator::GreaterThan,
        right: ContractExpression::Binding("x".into()),
    };
    let mut costs = Vec::new();
    for unrelated in [0, 64, 256, 1024] {
        let mut bindings = crate::persistent::PersistentMap::default();
        bindings = bindings.with_inserted(
            "x".into(),
            SpecIntegerExpression::Term(IntegerTerm::var(Variable(7))),
        );
        for index in 0..unrelated {
            bindings = bindings.with_inserted(
                format!("unused{index}"),
                SpecIntegerExpression::Term(IntegerTerm::var(Variable(index + 100))),
            );
        }
        let mut node_costs = Vec::new();
        for nodes in [8, 16, 32, 64] {
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..nodes {
                    lower_integer_certificate_proposition(&surface, &bindings).unwrap();
                }
            });
            node_costs.push(work);
        }
        for pair in node_costs.windows(2) {
            assert_eq!(pair[1], 2 * pair[0]);
        }
        costs.push(node_costs[0]);
    }
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

thread_local! {
    pub(super) static PROPOSITION_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[test]
fn nested_snapshot_propositions_lower_with_small_frames_and_linear_visits() {
    std::thread::Builder::new()
        .name("small-stack-proposition-lowering".into())
        .stack_size(1024 * 1024)
        .spawn(|| {
            let state = CState::new().with_local("x", int32(7));
            let predicates = PredicateEnvironment::new(&[]);
            let functions = ClickFunctionEnvironment::new(&[]);
            let mut snapshots = RecordedSnapshots::default();
            snapshots.insert(SnapshotSelector::Mark("before".into()), state.clone());
            let assumptions = PureFactContext::new();
            let atom = || ClickProposition::Comparison {
                left: ContractExpression::At {
                    selector: SnapshotSelector::Mark("before".into()),
                    expression: Box::new(ContractExpression::CFragment(CExpression::Variable(
                        "x".into(),
                    ))),
                },
                operator: ComparisonOperator::Equal,
                right: ContractExpression::CFragment(CExpression::Value(int32(7))),
            };
            for depth in [4, 8, 16, 32] {
                let mut proposition = atom();
                for level in 0..depth {
                    let left = Box::new(atom());
                    let right = Box::new(proposition);
                    proposition = match level % 3 {
                        0 => ClickProposition::And(left, right),
                        1 => ClickProposition::Or(left, right),
                        _ => ClickProposition::Implies(left, right),
                    };
                }
                let (mut lowerer, context) = fixed_state_elaboration(
                    BTreeMap::new(),
                    &state,
                    BTreeMap::from([("x".into(), int32(7))]),
                    BTreeMap::from([("x".into(), int32(9))]),
                    None,
                    &snapshots,
                    &assumptions,
                    &predicates,
                    &functions,
                    BTreeSet::new(),
                );
                PROPOSITION_VISITS.with(|visits| visits.set(0));
                let lowered = lowerer
                    .click_proposition_to_spec_proposition(&proposition, &context)
                    .unwrap();
                assert_eq!(
                    PROPOSITION_VISITS.with(|visits| visits.get()),
                    2 * depth + 1
                );
                let mut pending = vec![&lowered];
                let mut leaves = 0;
                while let Some(node) = pending.pop() {
                    match node {
                        SpecProposition::And(left, right)
                        | SpecProposition::Or(left, right)
                        | SpecProposition::Implies(left, right) => {
                            pending.push(left);
                            pending.push(right);
                        }
                        SpecProposition::Comparison { left, right, .. } => {
                            assert!(
                                matches!(left, SpecExpression::Value(value) if value == &int32(7))
                            );
                            assert!(
                                matches!(right, SpecExpression::Value(value) if value == &int32(7))
                            );
                            leaves += 1;
                        }
                        _ => panic!("lowering changed the proposition shape"),
                    }
                }
                assert_eq!(leaves, depth + 1);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
