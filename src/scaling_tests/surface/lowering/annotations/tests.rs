// Scaling tests of `src/surface/lowering/annotations/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

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

#[test]
fn proposition_state_selection_matches_full_context_without_unrelated_bindings() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let entry = ExecutionState::new().with_local("used", int32(1));
    let atom = |expression| ClickProposition::Comparison {
        left: expression,
        operator: ComparisonOperator::Equal,
        right: ContractExpression::Binding("late".into()),
    };
    let proposition = ClickProposition::And(
        Box::new(atom(ContractExpression::At {
            selector: ProgramPointSelector::Mark("before".into()),
            expression: Box::new(ContractExpression::Binding("used".into())),
        })),
        Box::new(atom(ContractExpression::Old(Box::new(
            ContractExpression::Binding("used".into()),
        )))),
    );
    let mut costs = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut state = ExecutionState::new().with_local("used", int32(2));
        for index in 0..size {
            state = state.with_local(format!("unused{index}"), int32(index));
        }
        let mut retained_states = RecordedStates::new();
        retained_states.insert(ProgramPointSelector::Mark("before".into()), state);
        let (mut lowerer, context) = fixed_state_elaboration(
            BTreeMap::new(),
            BTreeMap::new(),
            &entry,
            BTreeMap::from([("used".into(), int32(1))]),
            BTreeMap::from([("used".into(), int32(9)), ("late".into(), int32(3))]),
            None,
            &retained_states,
            SpecDefinitions::new(&predicates, &functions),
            BTreeSet::new(),
            BTreeMap::new(),
        );
        let reference = lowerer
            .click_proposition_to_spec_proposition(&proposition, &context)
            .unwrap();
        let mut names = BTreeSet::new();
        collect_click_proposition_referenced_names(&proposition, &mut names);
        lowerer.capture_referenced_names = Some(names);
        let ((selected, projected), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                let selected = lowerer
                    .click_proposition_to_spec_proposition(&proposition, &context)
                    .unwrap();
                let projected = lowerer
                    .point_environment(&ProgramPointSelector::Mark("before".into()), &context)
                    .unwrap()
                    .unwrap();
                (selected, projected)
            });
        assert_eq!(selected, reference);
        assert_eq!(projected.values.len(), 2);
        assert!(
            matches!(projected.values.get(&"used".to_string()), Some(SpecExpression::Value(value)) if value == &int32(2))
        );
        assert!(
            matches!(projected.values.get(&"late".to_string()), Some(SpecExpression::Value(value)) if value == &int32(3))
        );
        costs.push(work);
    }
    assert!(
        costs.iter().all(|cost| *cost == costs[0]),
        "state selection costs: {costs:?}"
    );
}

/// Putting a lowered loop in place follows the loop's path from the body's
/// root, whose length is the loop's nesting depth: a sequence on the path
/// replaces its one statement and shares the rest. The kernel body was a
/// pair tree, and the walk this replaces found the loop by numbering the
/// loops of every statement before it, so a function's loops cost work
/// quadratic in its length
/// (see "Sequential loop clauses" in
/// `docs/internals/verification-efficiency.md`). A C block
/// lowers to a balanced tree of pairs, so the path to the first, middle and
/// last of 16 to 1,024 loops visits at most the tree's depth, two more
/// statements per fourfold size, and the result is what the walk builds.
#[test]
fn putting_a_lowered_loop_in_place_reads_its_path_not_the_loops_before_it() {
    let mut visits = Vec::new();
    for loops in [16, 64, 256, 1024] {
        let body = (0..loops)
            .map(|k| format!("    i = 0;\n    while (i < 4) {{ p[i] = {k}; i = i + 1; }}\n"))
            .collect::<String>();
        let function = crate::languages::c::syntax::parse_function(&format!(
            "int32 caller(int32* p) {{\n    int32 i;\n{body}    return 0;\n}}"
        ))
        .expect("the loops parse")
        .to_kernel_function();
        let body = function.body();
        let paths = KernelLoopPaths::of(body);
        let replacement = ProgramStatement::While {
            condition: crate::kernel::program_expression::int32_literal(0),
            invariant: Vec::new(),
            invariant_checks: Vec::new(),
            effect_checks: Vec::new(),
            resource_specs: Vec::new(),
            ranking_measures: Vec::new(),
            structural_measure: None,
            do_while: false,
            backedge_target: None,
            natural_exit_target: None,
            body: Box::new(ProgramStatement::Skip),
        };
        let mut size_visits = Vec::new();
        for target in [0, loops / 2, loops - 1] {
            let before = kernel_loop_replacement_steps();
            let replaced = paths
                .replaced(body, target, &replacement)
                .expect("a top-level loop is put in place");
            size_visits.push(kernel_loop_replacement_steps() - before);
            assert_eq!(
                Some(&replaced),
                kernel_loop_replaced(body, target, &mut 0, &replacement).as_ref(),
                "loop({target}) of {loops}"
            );
            let (ProgramStatement::Seq(old), ProgramStatement::Seq(new)) = (body, &replaced) else {
                panic!("a block body");
            };
            assert_eq!(
                old.iter()
                    .zip(new.iter())
                    .filter(|(old, new)| !std::sync::Arc::ptr_eq(old, new))
                    .count(),
                1,
                "loop({target}) of {loops} shares every other statement"
            );
        }
        visits.push(size_visits);
    }
    for (index, size) in visits.iter().enumerate().skip(1) {
        for (position, visited) in size.iter().enumerate() {
            assert!(
                *visited <= visits[0][position] + 2 * index,
                "putting a loop in place visits more than the depth of a longer body: {visits:?}"
            );
        }
    }
}

#[test]
fn mathematical_lowering_keeps_repeated_squares_shared_without_evaluation() {
    use crate::kernel::{IntegerTerm, SpecIntegerExpression};
    let expression = ContractExpression::Multiply(
        Box::new(ContractExpression::Binding("selected".into())),
        Box::new(ContractExpression::Binding("selected".into())),
    );
    let state = ExecutionState::new();
    let retained_states = RecordedStates::new();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let (mut lowerer, mut context) = fixed_state_elaboration(
        BTreeMap::new(),
        BTreeMap::new(),
        &state,
        BTreeMap::new(),
        BTreeMap::new(),
        None,
        &retained_states,
        SpecDefinitions::new(&predicates, &functions),
        BTreeSet::new(),
        BTreeMap::new(),
    );
    for ordinary in [false, true] {
        let mut costs = Vec::new();
        for size in [16, 64, 256, 1024] {
            let mut bindings = crate::persistent::PersistentMap::default();
            for index in 0..size {
                bindings = bindings.with_inserted(
                    format!("unused{index}"),
                    SpecIntegerExpression::Term(IntegerTerm::constant_i64(index)),
                );
            }
            let mut value = IntegerTerm::constant_i64(2);
            for _ in 0..size {
                bindings = bindings.with_inserted(
                    "selected".into(),
                    SpecIntegerExpression::Term(value.clone()),
                );
                context.integer_values = bindings.clone();
                let (lowered, work) = crate::instrumentation::measure_deterministic_work(|| {
                    if ordinary {
                        lowerer
                            .lower_contract_integer_to_spec(&expression, &context)
                            .unwrap()
                    } else {
                        lower_contract_integer_to_spec(&expression, &bindings).unwrap()
                    }
                });
                let SpecIntegerExpression::Term(IntegerTerm::Multiply(left, right)) = lowered
                else {
                    panic!("lowering must retain the multiplication instead of evaluating it");
                };
                assert_eq!(left, right, "the two operands share one retained DAG");
                assert_eq!(left.as_ref(), &value);
                value = IntegerTerm::Multiply(left, right);
                // The first operation interns constants; all subsequent reads are
                // shallow DAG roots, independent of depth and unrelated bindings.
                assert!(work < 64, "size={size}, work={work}");
                costs.push(work);
            }
        }
        assert!(costs.iter().max().unwrap() <= &64);
    }
}
