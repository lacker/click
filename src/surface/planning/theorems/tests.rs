use super::*;

const SHIFT: &str = "function shifted(x: Integer) -> Integer { x + 7 }";
const BOUND: &str = "theorem shifted_bound(x: Integer) { requires 0 <= x; ensures 7 <= shifted(x) by { unfold(shifted(x)); close(); } }";

#[test]
fn single_theorem_discovery_expands_and_rechecks() {
    let proof = "by { close() using { 0 <= value; }; }";
    let source = format!(
        "{SHIFT} theorem too_strong(x: Integer) {{ requires 100 <= x; ensures 7 <= shifted(x) by {{ unfold(shifted(x)); close(); }} }} {BOUND} theorem test(value: Integer) {{ requires 0 <= value; ensures 7 <= shifted(value) {proof} }}"
    );
    let verified = verify_click_theorems(&source).unwrap_or_else(|e| panic!("{}", e.report()));
    let expanded = verified.last().unwrap().expanded_proof_source().unwrap();
    assert!(
        expanded.contains("apply(shifted_bound(value));"),
        "{expanded}"
    );
    assert!(!expanded.contains("solve("), "{expanded}");
    // The library declarations' proofs still contain solve; recheck only the
    // expanded target with those declarations supplied as dependencies.
    let expanded_source = source.replace(proof, &expanded);
    let file = parser::parse(&expanded_source).unwrap();
    let definitions = file.theorem_definitions();
    let functions = ClickFunctionEnvironment::new(file.click_function_definitions());
    crate::surface::without_implicit_solve(|| {
        crate::surface::proof::verify_theorem_definition(
            definitions.last().unwrap(),
            SpecDefinitions::new(&PredicateEnvironment::new(&[]), &functions),
            &TheoremEnvironment::new(&definitions[..definitions.len() - 1]),
            None,
        )
    })
    .unwrap_or_else(|e| panic!("{expanded}: {}", e.report()));
}

#[test]
fn single_theorem_discovery_keeps_unlisted_facts_unavailable() {
    for premises in ["", "1 <= value;"] {
        let source = format!(
            "{SHIFT} {BOUND} theorem test(value: Integer) {{ requires 0 <= value; requires 1 <= value; ensures 7 <= shifted(value) by {{ close() using {{ {premises} }}; }} }}"
        );
        assert!(verify_click_theorems(&source).is_err(), "{source}");
    }
    let source = format!(
        "{SHIFT} {BOUND} theorem test(value: Integer) {{ requires 0 <= value; ensures 8 <= shifted(value) by {{ close() using {{ 0 <= value; }}; }} }}"
    );
    assert!(verify_click_theorems(&source).is_err());
}

#[test]
fn single_theorem_discovery_does_not_invent_arguments_or_chain() {
    let hidden = format!(
        "{SHIFT} theorem hidden(x: Integer, witness: Integer) {{ requires 0 <= witness; requires x == witness; ensures 7 <= shifted(x) by {{ unfold(shifted(x)); close(); }} }} theorem test(value: Integer) {{ requires 0 <= value; ensures 7 <= shifted(value) by {{ close() using {{ 0 <= value; }}; }} }}"
    );
    assert!(verify_click_theorems(&hidden).is_err());
    let chain = format!(
        "{SHIFT} function middle(x: Integer) -> Integer {{ x }} theorem first(x: Integer) {{ requires 0 <= x; ensures 0 <= middle(x) by {{ unfold(middle(x)); close(); }} }} theorem second(x: Integer) {{ requires 0 <= middle(x); ensures 7 <= shifted(x) by {{ unfold(middle(x)); unfold(shifted(x)); close(); }} }} theorem test(value: Integer) {{ requires 0 <= value; ensures 7 <= shifted(value) by {{ close() using {{ 0 <= value; }}; }} }}"
    );
    assert!(verify_click_theorems(&chain).is_err());
}

#[test]
fn single_theorem_discovery_finds_generic_library_law() {
    let proof = "by { close() using {}; }";
    let source = format!(
        "import click::list; theorem test(xs: List<Integer>, ys: List<Integer>) {{ ensures list::length(list::append(xs, ys)) == nat::add(list::length(xs), list::length(ys)) {proof} }}"
    );
    let verified = verify_click_theorems(&source).unwrap_or_else(|e| panic!("{}", e.report()));
    let expanded = verified[0].expanded_proof_source().unwrap();
    assert!(expanded.contains("length_append"), "{expanded}");
    assert!(!expanded.contains("solve("), "{expanded}");
    verify_click_theorems(&source.replace(proof, &expanded))
        .unwrap_or_else(|e| panic!("{expanded}: {}", e.report()));
}

#[test]
fn single_theorem_discovery_closes_c_outcome_and_expands() {
    let proof = "by { step_until(function.exit); close() using { 0 <= to_integer(x); }; }";
    let source = format!(
        "verifying \"noop.c\"; {SHIFT} {BOUND} void noop(int32 x) {{ requires 0 <= to_integer(x); ensures 7 <= shifted(to_integer(x)); }} {proof}"
    );
    let c = [("noop.c", "void noop(int32 x) {}")];
    let verified = verify_c_sources(&source, &c).unwrap_or_else(|e| panic!("{}", e.report()));
    let expanded = verified[0].expanded_proof_source().unwrap();
    assert!(expanded.contains("shifted_bound"), "{expanded}");
    assert!(!expanded.contains("solve("), "{expanded}");
    verify_c_sources(&source.replace(proof, &expanded), &c)
        .unwrap_or_else(|e| panic!("{expanded}: {}", e.report()));
}

#[test]
fn discovery_respects_library_imports_and_prefixes() {
    let file = parser::parse(
        "import click::integer; theorem probe(a: Integer, b: Integer) { ensures a < b; }",
    )
    .unwrap();
    let empty = parser::parse("").unwrap();
    let Ensure::Proposition(goal) = file.theorem_definitions()[0].ensures()[0].ensure() else {
        panic!()
    };
    let law = "click::integer::le_ne_lt";
    let visible = TheoremEnvironment::with_standard_library(&[])
        .unwrap()
        .with_discovery_library(&file)
        .unwrap();
    assert!(
        visible
            .conclusion_candidates(goal)
            .any(|candidate| candidate.name == law)
    );
    let hidden = TheoremEnvironment::with_standard_library(&[])
        .unwrap()
        .with_discovery_library(&empty)
        .unwrap();
    assert!(
        !hidden
            .conclusion_candidates(goal)
            .any(|candidate| candidate.name == law)
    );
    let position = *visible.standard_library_index.get(law).unwrap();
    let prefix = TheoremEnvironment::with_full_library_prefix(position, &[]).unwrap();
    assert!(
        !prefix
            .conclusion_candidates(goal)
            .any(|candidate| candidate.name == law)
    );
    let selected_prefix = prefix.with_discovery_library(&file).unwrap();
    assert!(
        !selected_prefix
            .conclusion_candidates(goal)
            .any(|candidate| candidate.name == law)
    );
    let through_law = TheoremEnvironment::with_full_library_prefix(position + 1, &[])
        .unwrap()
        .with_discovery_library(&file)
        .unwrap();
    assert!(
        through_law
            .conclusion_candidates(goal)
            .any(|candidate| candidate.name == law)
    );
}

#[test]
fn theorem_matching_retains_typed_c_binding_identity() {
    let owner = crate::kernel::LocalFunctionId::new(Some("caller.c".into()), "caller".into());
    let local = crate::kernel::LocalBindingId::new(owner, false, 1, Some("x".into()));
    let local = ContractExpression::ProgramExpression(ProgramExpression::Variable(local.into()));
    assert_eq!(parameter_name(&local), None);
    let named = ContractExpression::ProgramExpression(ProgramExpression::Variable("x".into()));
    assert_eq!(parameter_name(&named), Some("x"));
    let file = parser::parse("function shifted(x: int32) -> Integer { to_integer(x) + 7 } theorem law(x: int32) { ensures 7 <= shifted(x); }").unwrap();
    let theorem = &file.theorem_definitions()[0];
    let Ensure::Proposition(mut goal) = theorem.ensures()[0].ensure().clone() else {
        panic!()
    };
    let ClickProposition::Comparison {
        right: ContractExpression::Call { arguments, .. },
        ..
    } = &mut goal
    else {
        panic!()
    };
    arguments[0] = local.clone();
    let application = match_theorem_conclusion(theorem, 0, &goal).next().unwrap();
    assert_eq!(application.arguments, vec![local]);
}

#[test]
fn equivalent_comparison_spellings_discover_and_expand() {
    for (conclusion, goal) in [
        ("fixed(x) == 7", "7 == fixed(value)"),
        ("fixed(x) != 8", "8 != fixed(value)"),
        ("fixed(x) < 8", "8 > fixed(value)"),
        ("fixed(x) <= 7", "7 >= fixed(value)"),
        ("fixed(x) > 6", "6 < fixed(value)"),
        ("fixed(x) >= 7", "7 <= fixed(value)"),
    ] {
        let proof = "by { close() using { 0 <= value; }; }";
        let source = format!(
            "function fixed(x: Integer) -> Integer {{ 7 }} theorem law(x: Integer) {{ requires 0 <= x; ensures {conclusion} by {{ unfold(fixed(x)); close(); }} }} theorem test(value: Integer) {{ requires 0 <= value; ensures {goal} {proof} }}"
        );
        let verified =
            verify_click_theorems(&source).unwrap_or_else(|e| panic!("{source}: {}", e.report()));
        let expanded = verified.last().unwrap().expanded_proof_source().unwrap();
        assert!(expanded.contains("apply(law(value));"), "{expanded}");
        assert!(!expanded.contains("solve("), "{expanded}");
        verify_click_theorems(&source.replace(proof, &expanded))
            .unwrap_or_else(|e| panic!("{expanded}: {}", e.report()));
        let missing = source.replace("close() using { 0 <= value; }", "close() using {}");
        assert!(verify_click_theorems(&missing).is_err(), "{missing}");
    }
}

#[test]
fn equality_orientation_is_disambiguated_by_listed_prerequisites() {
    for (function, operator) in [("0", "=="), ("x", "!=")] {
        let proof = "by { close() using { a < b; }; }";
        let source = format!(
            "function image(x: Integer) -> Integer {{ {function} }} theorem law(x: Integer, y: Integer) {{ requires x < y; ensures image(x) {operator} image(y) by {{ unfold(image(x)); unfold(image(y)); close(); }} }} theorem test(a: Integer, b: Integer) {{ requires a < b; ensures image(b) {operator} image(a) {proof} }}"
        );
        let verified =
            verify_click_theorems(&source).unwrap_or_else(|e| panic!("{source}: {}", e.report()));
        let expanded = verified.last().unwrap().expanded_proof_source().unwrap();
        assert!(expanded.contains("apply(law(a, b));"), "{expanded}");
        assert!(!expanded.contains("solve("), "{expanded}");
        verify_click_theorems(&source.replace(proof, &expanded))
            .unwrap_or_else(|e| panic!("{expanded}: {}", e.report()));
    }
}

#[test]
fn nested_comparison_matching_preserves_shared_arguments() {
    let file = parser::parse("function image(x: Integer) -> Integer { x } theorem law(x: Integer, y: Integer) { ensures image(x) == image(y) and x < y; } theorem target(a: Integer, b: Integer) { ensures image(b) == image(a) and b > a; }").unwrap();
    let theorem = &file.theorem_definitions()[0];
    let Ensure::Proposition(goal) = file.theorem_definitions()[1].ensures()[0].ensure() else {
        panic!()
    };
    let applications = match_theorem_conclusion(theorem, 0, goal).collect::<Vec<_>>();
    assert_eq!(applications.len(), 1);
    assert_eq!(
        applications[0].arguments,
        vec![
            ContractExpression::Binding("a".into()),
            ContractExpression::Binding("b".into())
        ]
    );
    let repeated = parser::parse("function image(x: Integer) -> Integer { x } theorem law(x: Integer) { ensures image(x) == x; } theorem target(a: Integer, b: Integer) { ensures b == image(a); }").unwrap();
    let Ensure::Proposition(goal) = repeated.theorem_definitions()[1].ensures()[0].ensure() else {
        panic!()
    };
    assert!(
        match_theorem_conclusion(&repeated.theorem_definitions()[0], 0, goal)
            .next()
            .is_none()
    );
}

#[test]
fn mirrored_float_orders_do_not_complement_nan_comparisons() {
    for (ty, bits, one) in [
        ("float", "float32_from_bits", "0x3f800000"),
        ("double", "float64_from_bits", "0x3ff0000000000000"),
    ] {
        let proof = "by { close() using {}; }";
        let source = format!(
            "function fixed(x: {ty}) -> {ty} {{ {bits}({one}) }} theorem law(x: {ty}) {{ ensures fixed(x) > {bits}(0) by {{ unfold(fixed(x)); normalize(); }} }} theorem test(value: {ty}) {{ ensures {bits}(0) < fixed(value) {proof} }}"
        );
        let verified = verify_click_theorems(&source).unwrap_or_else(|e| panic!("{}", e.report()));
        let expanded = verified.last().unwrap().expanded_proof_source().unwrap();
        assert!(expanded.contains("apply(law(value));"), "{expanded}");
        verify_click_theorems(&source.replace(proof, &expanded))
            .unwrap_or_else(|e| panic!("{expanded}: {}", e.report()));
    }
    let false_goal = "theorem test(x: double, y: double) { requires not (x <= y); ensures y < x by { close() using { not (x <= y); }; } }";
    assert!(verify_click_theorems(false_goal).is_err());
    let wrong_relation = parser::parse("theorem law(x: Integer, y: Integer) { ensures x < y; } theorem target(a: Integer, b: Integer) { ensures b >= a; }").unwrap();
    let Ensure::Proposition(goal) = wrong_relation.theorem_definitions()[1].ensures()[0].ensure()
    else {
        panic!()
    };
    assert!(
        match_theorem_conclusion(&wrong_relation.theorem_definitions()[0], 0, goal)
            .next()
            .is_none()
    );
}

#[test]
fn discovery_failures_explain_missing_listed_prerequisites() {
    let source = format!(
        "{SHIFT} {BOUND} theorem test(value: Integer) {{ requires 0 <= value; ensures 7 <= shifted(value) by {{ close() using {{}}; }} }}"
    );
    let error = verify_click_theorems(&source).unwrap_err();
    let report = error.report().to_string();
    assert!(
        report.contains("theorem discovery [MissingPrerequisite]"),
        "{report}"
    );
    assert!(
        report.contains("theorem `shifted_bound` needs listed prerequisite `0 <= value`"),
        "{report}"
    );
    assert!(!report.contains("[NoMatch]"), "{report}");

    let source = format!(
        "verifying \"noop.c\"; {SHIFT} {BOUND} void noop(int32 x) {{ requires 0 <= to_integer(x); ensures 7 <= shifted(to_integer(x)); }} by {{ step_until(function.exit); close() using {{}}; }}"
    );
    let report = verify_c_sources(&source, &[("noop.c", "void noop(int32 x) {}")])
        .unwrap_err()
        .report()
        .to_string();
    assert!(
        report.contains("theorem discovery [MissingPrerequisite]"),
        "{report}"
    );
    assert!(
        report.contains("needs listed prerequisite `0 <= to_integer(x)`"),
        "{report}"
    );
    assert!(!report.contains("[NoMatch]"), "{report}");
}

#[test]
fn discovery_failures_identify_undetermined_arguments() {
    let source = format!(
        "{SHIFT} theorem hidden(x: Integer, witness: Integer) {{ requires 0 <= witness; requires x == witness; ensures 7 <= shifted(x) by {{ unfold(shifted(x)); close(); }} }} theorem test(value: Integer) {{ requires 0 <= value; ensures 7 <= shifted(value) by {{ close() using {{ 0 <= value; }}; }} }}"
    );
    let report = verify_click_theorems(&source)
        .unwrap_err()
        .report()
        .to_string();
    assert!(
        report.contains("theorem discovery [UndeterminedArgument]"),
        "{report}"
    );
    assert!(
        report.contains("theorem `hidden`: argument `witness` cannot be inferred from the goal"),
        "{report}"
    );
    assert!(report.contains("explicit apply(...)"), "{report}");
    assert!(!report.contains("[NoMatch]"), "{report}");
}

#[test]
fn discovery_failures_report_structural_misses_without_claiming_nonexistence() {
    // Both an empty bucket and a candidate whose constant does not match.
    for library in ["", BOUND] {
        let source = format!(
            "{SHIFT} {library} theorem test(value: Integer) {{ requires 1 <= value; ensures 8 <= shifted(value) by {{ close() using {{ 1 <= value; }}; }} }}"
        );
        let report = verify_click_theorems(&source)
            .unwrap_err()
            .report()
            .to_string();
        assert!(report.contains("theorem discovery [NoMatch]"), "{report}");
        assert!(report.contains("supported structural fragment"), "{report}");
        assert!(!report.contains("[MissingPrerequisite]"), "{report}");
    }
}

#[test]
fn matcher_reports_exhaustion_once_instead_of_a_structural_miss() {
    let file = parser::parse("theorem law(x: Integer) { ensures x < 7; }").unwrap();
    let theorem = &file.theorem_definitions()[0];
    let Ensure::Proposition(goal) = theorem.ensures()[0].ensure() else {
        panic!()
    };
    crate::instrumentation::with_run_work_limit(0, || {
        let mut outcomes = theorem_conclusion_matches(theorem, 0, goal);
        assert!(matches!(
            outcomes.next(),
            Some(TheoremConclusionMatch::Exhausted)
        ));
        assert!(outcomes.next().is_none());
    });
}
