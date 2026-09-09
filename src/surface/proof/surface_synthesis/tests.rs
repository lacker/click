use super::*;

#[test]
fn nested_propositions_synthesize_with_small_frames_and_linear_work() {
    std::thread::Builder::new()
        .name("small-stack-proposition-synthesis".into())
        .stack_size(1024 * 1024)
        .spawn(|| {
            let state = CState::new();
            let atom = || {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(Bitvector32Term::Constant(7)),
                        Box::new(Bitvector32Term::Constant(7)),
                    ),
                    true,
                )
            };
            let samples = [4, 8, 16, 32].map(|depth| {
                let mut proposition = atom();
                for level in 0..depth {
                    let left = Box::new(atom());
                    let right = Box::new(proposition);
                    proposition = match level % 3 {
                        0 => Proposition::And(left, right),
                        1 => Proposition::Or(left, right),
                        _ => Proposition::Implies(left, right),
                    };
                }
                let _scope = SurfaceSynthesisScope::enter();
                let surface = synthesize_surface_proposition_with_bound_variables(
                    &proposition,
                    &[],
                    &[],
                    &state,
                    &BTreeMap::new(),
                )
                .expect("connective synthesis must fit the small stack");
                let work = SURFACE_SYNTHESIS_BUDGET.with(|budget| {
                    let budget = budget.borrow();
                    let budget = budget.as_ref().unwrap();
                    assert_eq!(budget.depth, 0);
                    assert_eq!(budget.exhausted_category, None);
                    SURFACE_SYNTHESIS_WORK_LIMIT - budget.remaining_work
                });
                let mut pending = vec![&surface];
                let mut leaves = 0;
                while let Some(node) = pending.pop() {
                    match node {
                        ClickProposition::And(left, right)
                        | ClickProposition::Or(left, right)
                        | ClickProposition::Implies(left, right) => {
                            pending.push(left);
                            pending.push(right);
                        }
                        ClickProposition::Comparison {
                            operator: ComparisonOperator::Equal,
                            ..
                        } => leaves += 1,
                        _ => panic!("synthesis changed the proposition shape"),
                    }
                }
                assert_eq!(leaves, depth + 1);
                work
            });
            assert!(samples[0] > 0);
            for pair in samples.windows(2) {
                assert!(pair[1] > pair[0] && pair[1] <= 2 * pair[0], "{samples:?}");
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
