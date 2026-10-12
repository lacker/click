use super::*;

#[test]
fn batch_source_positions_preserve_unicode_columns_and_request_order() {
    let source = "αβ;\n\tγδ;\nlast";
    let offsets = [source.len(), 2, 0, 9, 2];
    assert_eq!(
        positions_at_offsets(source, offsets),
        offsets.map(|offset| position_at_offset(source, offset))
    );
}

#[test]
fn batch_source_positions_walk_a_long_line_once() {
    let mut measurements = Vec::new();
    for size in [16, 64, 256] {
        let source = "α ".repeat(size);
        let (positions, work) = crate::instrumentation::measure_deterministic_work(|| {
            positions_at_offsets(&source, (0..size).map(|index| index * 3))
        });
        assert_eq!(
            positions.last(),
            Some(&SourcePosition::new(1, size * 2 - 1))
        );
        assert!(work <= size * 3);
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{measurements:?}");
    }
}

#[test]
fn execute_until_in_proof_if_arms_expands_and_rechecks() {
    let c = "int32 identity(int32 x) { int32 y = x; return y; }";
    let source = r#"
verifying "identity.c";
int32 identity(int32 x) { ensures result == x; } by {
    if x == 0 {
        execute_until(statement(0));
        execute_until(assignment(y, 0));
        step(); execute(); simp();
    } else {
        execute_until(statement(0));
        execute_until(assignment(y, 0));
        step(); execute(); simp();
    }
}
"#;
    let sources = [("identity.c", c)];
    verify_c0_sources(source, &sources).unwrap();
    let expanded = expand_c0_claim_source_by_label(source, &sources, "identity.contract").unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
    assert!(
        verify_c0_sources(
            &expanded.replace("ensures result == x;", "ensures result == x + 1;"),
            &sources,
        )
        .is_err()
    );
}

#[test]
fn tactic_expansion_can_name_an_outer_c_parameter_after_intro() {
    let c_source = "int32 shadowed_c(int32 x) { return 0; }";
    let click_source = r#"
verifying "shadowed.c";

int32 shadowed_c(int32 x) {
    requires x == 0;
    ensures forall (x: int32) { x == x };
} by {
    execute();
    intro();
    have outer.x == 0 by { simp(); }
    simp();
}
"#;
    let sources = [("shadowed.c", c_source)];
    verify_c0_sources(click_source, &sources).expect("C proof should retain the outer x");
    let position = position_at_offset(click_source, click_source.find("simp();").unwrap());
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("selected smart tactic should expand");
    assert!(
        expanded.contains("have outer.x == 0 by {\n        assumption();"),
        "{expanded}"
    );
    assert!(expanded.contains("outer.x"), "{expanded}");
    verify_c0_sources(&expanded, &sources).expect("expanded C proof must reverify");

    let wrong_binder = click_source.replace("have outer.x == 0", "have x == 0");
    verify_c0_sources(&wrong_binder, &sources)
        .expect_err("the fresh universal x must not inherit the parameter's equality");
}

#[test]
fn tactic_expansion_can_name_two_outer_c_binders_after_intro() {
    let c_source = "int32 shadowed_twice_c(int32 x) { return 0; }";
    let click_source = r#"
verifying "shadowed.c";

int32 shadowed_twice_c(int32 x) {
    requires x == 0;
    ensures forall (x: int32) { forall (x: int32) { x == x } };
} by {
    execute();
    intro();
    intro();
    have outer.outer.x == 0 by { simp(); }
    simp();
}
"#;
    let sources = [("shadowed.c", c_source)];
    verify_c0_sources(click_source, &sources).expect("both shadowed binders stay distinct");
    let position = position_at_offset(click_source, click_source.find("simp();").unwrap());
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("selected smart tactic should expand");
    assert!(
        expanded.contains("have outer.outer.x == 0 by {\n        assumption();"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &sources).expect("expanded nested C proof must reverify");
}

#[test]
fn tactic_expansion_can_name_two_levels_of_shadowed_binders() {
    let source = r#"
theorem shadowed_twice(x: int32) {
    requires x == 0;
    ensures forall (x: int32) { forall (x: int32) { x == x } } by {
        intro();
        intro();
        have outer.outer.x == 0 by { simp(); }
        simp();
    }
}
"#;
    verify_c0_sources(source, &[]).expect("the oldest x should remain available");
    let position = position_at_offset(source, source.find("simp();").unwrap());
    let expanded = expand_c0_tactic_source_at(source, &[], position.line, position.column)
        .expect("selected smart tactic should expand");
    assert!(!expanded.contains("simp();"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(expanded.contains("outer.outer.x"), "{expanded}");
    verify_c0_sources(&expanded, &[]).expect("expanded proof must reverify");

    let wrong_depth = source.replace("outer.outer.x", "outer.outer.outer.x");
    verify_c0_sources(&wrong_depth, &[])
        .expect_err("a qualifier beyond the enclosing x bindings must fail");
}

#[test]
fn tactic_line_disambiguation_uses_columns_only_for_shared_lines() {
    let source = "by { step(); step(); }\nby {\n    step();\n}\n";
    assert!(tactic_line_has_multiple_starts(source, &SourcePosition::new(1, 6)).unwrap());
    assert!(tactic_line_has_multiple_starts(source, &SourcePosition::new(1, 14)).unwrap());
    assert!(!tactic_line_has_multiple_starts(source, &SourcePosition::new(3, 5)).unwrap());

    let quantified = "by { have exists (x: int32) { x == x }; }\n";
    assert!(!tactic_line_has_multiple_starts(quantified, &SourcePosition::new(1, 6)).unwrap());

    let nested = "by {\n    have n <= n by { simp(); }\n}\n";
    let have = position_at_offset(nested, nested.find("have").unwrap());
    let simp = position_at_offset(nested, nested.find("simp").unwrap());
    assert!(!tactic_line_has_multiple_starts(nested, &have).unwrap());
    assert!(tactic_line_has_multiple_starts(nested, &simp).unwrap());
}

#[test]
fn trace_target_selects_only_the_arm_containing_its_source_position() {
    let source = "by {\n  branch then { step(); } else { step(); }\n  step();\n}\n";
    let branch = position_at_offset(source, source.find("branch").unwrap());
    let then_step = position_at_offset(
        source,
        source.find("then { step").unwrap() + "then { ".len(),
    );
    let else_step = position_at_offset(
        source,
        source.find("else { step").unwrap() + "else { ".len(),
    );
    let continuation = position_at_offset(source, source.rfind("step();").unwrap());
    assert_eq!(
        tactic_arm_containing_position(source, &branch, &then_step).unwrap(),
        Some(0)
    );
    assert_eq!(
        tactic_arm_containing_position(source, &branch, &else_step).unwrap(),
        Some(1)
    );
    assert_eq!(
        tactic_arm_containing_position(source, &branch, &continuation).unwrap(),
        None
    );
}

#[test]
fn nested_tactic_position_follows_have_and_open_bodies() {
    let source = "have true by {\n    open(resource) {\n        have true by {\n            assumption();\n        }\n    }\n}\n";
    let position = nested_tactic_source_position(source, &SourcePosition::new(1, 1), &[0, 0, 0])
        .expect("nested step has a source position");
    assert_eq!(position, SourcePosition::new(4, 13));
}

#[test]
fn integer_function_unfold_expands_and_reverifies() {
    let source = r#"
function successor(z: Integer) -> Integer {
    z + 1
}

theorem successor_expansion(z: Integer) {
    ensures successor(z) == z + 1 by {
        unfold(successor(z));
        simp();
    }
}
"#;
    verify_c0_sources(source, &[]).expect("Integer successor source verifies");
    let expanded = expand_c0_claim_source_by_label(source, &[], "successor_expansion.ensures_0")
        .expect("Integer successor claim expands");
    verify_c0_sources(&expanded, &[]).expect("expanded Integer successor re-verifies");
}

#[test]
fn nat_integer_laws_expand_and_reject_wrong_successor() {
    let source = r#"
theorem nat_integer_client(n: Nat) {
    ensures to_integer(Nat::Succ(n)) == to_integer(n) + 1 by {
        apply(nat_integer_succ(n));
    }
}
"#;
    verify_c0_sources(source, &[]).expect("Nat conversion law verifies");
    let expanded = expand_c0_claim_source_by_label(source, &[], "nat_integer_client.ensures_0")
        .expect("Nat conversion claim expands");
    verify_c0_sources(&expanded, &[]).expect("expanded Nat conversion re-verifies");

    let invalid = source.replace("+ 1", "+ 2");
    assert!(verify_c0_sources(&invalid, &[]).is_err());
}

#[test]
fn builtin_nat_integer_dispatch_and_checked_to_nat() {
    let source = r#"
theorem nat_dispatch(n: Nat) {
    ensures to_integer(n) == to_integer(n) by { normalize(); }
}
theorem checked_to_nat(z: Integer) {
    requires z >= 0;
    ensures to_nat(z) == to_nat(z) by { normalize(); }
}
"#;
    verify_c0_sources(source, &[]).expect("Nat/Integer conversion dispatch verifies");
    let missing_bound = r#"
theorem missing_to_nat_bound(z: Integer) {
    ensures to_nat(z) == to_nat(z) by { normalize(); }
}
"#;
    assert!(verify_c0_sources(missing_bound, &[]).is_err());
    let nested_missing_bound = r#"
theorem nested_missing_to_nat_bound(z: Integer) {
    ensures Nat::Succ(to_nat(z)) == Nat::Succ(to_nat(z)) by { normalize(); }
}
"#;
    assert!(verify_c0_sources(nested_missing_bound, &[]).is_err());
    let shadowed = r#"
function to_nat(z: Integer) -> Nat { Nat::Zero }
"#;
    assert!(verify_c0_sources(shadowed, &[]).is_err());
}

#[test]
fn successive_constructor_unfolds_retain_a_checked_goal() {
    let source = r#"
theorem add_two(n: Nat) {
    ensures nat_add(Nat::Succ(Nat::Succ(Nat::Zero)), n) == Nat::Succ(Nat::Succ(n)) by {
        unfold(nat_add(Nat::Succ(Nat::Succ(Nat::Zero)), n));
        unfold(nat_add(Nat::Succ(Nat::Zero), n));
        unfold(nat_add(Nat::Zero, n));
        normalize();
    }
}
theorem singleton<T>(x: T) {
    ensures list_length(List<T>::Cons(x, List<T>::Nil)) == Nat::Succ(Nat::Zero) by {
        unfold(list_length(List<T>::Cons(x, List<T>::Nil)));
        unfold(list_length(List<T>::Nil));
        normalize();
    }
}
"#;
    verify_c0_sources(source, &[]).expect("successive explicit unfolds verify");
    let smart_source = source.replace("normalize();", "simp();");
    verify_c0_sources(&smart_source, &[]).expect("smart closers have checked certificates");
    for (claim, index) in [("add_two.ensures_0", 3), ("singleton.ensures_0", 2)] {
        let position = c0_tactic_source_position(&smart_source, &[], claim, index).unwrap();
        let expanded =
            expand_c0_tactic_source_at(&smart_source, &[], position.line, position.column).unwrap();
        verify_c0_sources(&expanded, &[]).expect("successive unfolds expand and recheck");
    }
    let tampered = source.replace("== Nat::Succ(Nat::Succ(n))", "== Nat::Succ(n)");
    assert!(verify_c0_sources(&tampered, &[]).is_err());
}

#[test]
fn generic_smart_proofs_expand_without_concrete_clients() {
    let source = r#"
theorem independent<T, U>(x: T, y: U) {
    ensures x == x by { simp(); }
    ensures y == y by { simp(); }
}
theorem lists<T>(xs: List<List<T>>) {
    ensures list_append(xs, List<List<T>>::Nil) == xs by {
        apply(list_append_right_identity(xs));
    }
}
"#;
    let verified = verify_click_theorems(source).expect("parametric proofs verify");
    assert_eq!(verified.len(), 3);
    for claim in [
        "independent.ensures_0",
        "independent.ensures_1",
        "lists.ensures_0",
    ] {
        let position = c0_tactic_source_position(source, &[], claim, 0).unwrap();
        let expanded =
            expand_c0_tactic_source_at(source, &[], position.line, position.column).unwrap();
        assert!(expanded.contains("independent<T, U>"));
        assert!(expanded.contains("lists<T>"));
        verify_c0_sources(&expanded, &[]).expect("expanded parametric certificate rechecks");
    }
}

#[test]
fn conditional_normalization_roundtrips_and_rejects_tampering() {
    let source = r#"
theorem client(xs: List<int32>, ys: List<int32>) {
    requires not(xs == ys);
    ensures (if xs == ys { 1 } else { 0 }) == 0 by {
        normalize() using { not(xs == ys); }
    }
}
"#;
    verify_c0_sources(source, &[]).expect("conditional client verifies before expansion");
    let position = c0_tactic_source_position(source, &[], "client.ensures_0", 0).unwrap();
    let expanded = expand_c0_tactic_source_at(source, &[], position.line, position.column)
        .expect("simple conditional normalization roundtrips");
    assert!(expanded.contains("normalize() using"));
    verify_c0_sources(&expanded, &[]).expect("conditional certificate rechecks");
    for tampered in [
        expanded.replace("requires not(xs == ys);", "requires xs == ys;"),
        expanded.replace("not(xs == ys)", "xs == ys"),
        expanded.replace("else { 0 }) == 0", "else { 0 }) == 1"),
    ] {
        assert_ne!(tampered, expanded);
        assert!(verify_c0_sources(&tampered, &[]).is_err());
    }
}

#[test]
fn generic_template_expansion_checks_arbitrary_types() {
    let source = r#"
theorem client<T>(xs: List<T>, ys: List<T>) {
    requires not(xs == ys);
    ensures (if xs == ys { 1 } else { 0 }) == 0 by {
        normalize() using { not(xs == ys); }
    }
}
"#;
    let position = c0_tactic_source_position(source, &[], "client.ensures_0", 0)
        .expect("generic parameter lists have source locations");
    let expanded = expand_c0_tactic_source_at(source, &[], position.line, position.column)
        .expect("a template has a checked parametric certificate");
    verify_c0_sources(&expanded, &[]).expect("expanded template rechecks without a client");
    assert!(
        verify_c0_sources(
            &expanded.replace("requires not(xs == ys);", "requires xs == ys;"),
            &[]
        )
        .is_err()
    );
}

#[test]
fn smart_conditional_normalization_emits_checked_evidence() {
    let source = r#"
function same_list(xs: List<int32>, ys: List<int32>) -> int32 {
    if xs == ys { 1 } else { 0 }
}
theorem client(xs: List<int32>, ys: List<int32>) {
    requires not(xs == ys);
    ensures same_list(xs, ys) == 0 by { simp(); }
}
"#;
    verify_c0_sources(source, &[]).expect("smart conditional proof verifies");
    let position = c0_tactic_source_position(source, &[], "client.ensures_0", 0).unwrap();
    let expanded = expand_c0_tactic_source_at(source, &[], position.line, position.column)
        .expect("smart conditional proof expands");
    assert!(expanded.contains("normalize() using"), "{expanded}");
    verify_c0_sources(&expanded, &[]).expect("emitted conditional evidence rechecks");
    assert!(
        verify_c0_sources(
            &expanded.replace("requires not(xs == ys);", "requires xs == ys;"),
            &[],
        )
        .is_err()
    );
}

#[test]
fn nested_list_membership_expands_and_rechecks() {
    let source = r#"
theorem client(xs: List<List<int32>>, ys: List<List<int32>>, value: List<int32>) {
    ensures list_contains(list_append(xs, ys), value)
        == if list_contains(xs, value) == 1 { 1 } else { list_contains(ys, value) } by {
        apply(list_contains_append(xs, ys, value));
    }
}
"#;
    verify_c0_sources(source, &[]).expect("nested-list client verifies before expansion");
    let position = c0_tactic_source_position(source, &[], "client.ensures_0", 0).unwrap();
    let expanded = expand_c0_tactic_source_at(source, &[], position.line, position.column)
        .expect("nested-list application expands");
    verify_c0_sources(&expanded, &[]).expect("expanded nested-list client rechecks");
}

#[test]
fn scalar_call_congruence_expands_and_rejects_tampering() {
    let source = r#"
theorem client(xs: List<int32>, ys: List<int32>, value: int32) {
    requires xs == ys;
    ensures list_contains(xs, value) == list_contains(ys, value) by {
        rewrite(xs == ys);
        simp();
    }
}
"#;
    verify_c0_sources(source, &[]).expect("rewrite client verifies before expansion");
    let position = c0_tactic_source_position(source, &[], "client.ensures_0", 1).unwrap();
    let expanded = expand_c0_tactic_source_at(source, &[], position.line, position.column)
        .expect("rewritten scalar goal expands");
    verify_c0_sources(&expanded, &[]).expect("expanded rewrite client rechecks");
    let tampered = expanded.replace("requires xs == ys;", "requires xs == xs;");
    assert!(verify_c0_sources(&tampered, &[]).is_err());
}

#[test]
fn library_list_theorem_application_expands_and_rechecks() {
    let source = r#"
theorem client(xs: List<int32>, ys: List<int32>, zs: List<int32>) {
    ensures list_append(list_append(xs, ys), zs) == list_append(xs, list_append(ys, zs)) by {
        apply(list_append_associative(xs, ys, zs));
    }
}
"#;
    verify_c0_sources(source, &[]).expect("library client verifies before expansion");
    let position = c0_tactic_source_position(source, &[], "client.ensures_0", 0)
        .expect("application has a source position");
    let expanded = expand_c0_tactic_source_at(source, &[], position.line, position.column)
        .expect("library theorem application expands");
    verify_c0_sources(&expanded, &[]).expect("expanded library client rechecks");
}

#[test]
fn block_tactic_optional_semicolon_belongs_to_the_tactic() {
    let source = "by { step(); simp(); }";
    let tokens = scan_source_tokens(source).expect("source should tokenize");
    let by = tokens
        .iter()
        .position(|token| token.text == "by")
        .expect("proof should contain by");
    let open = by + 1;
    let close = matching_delimiter(&tokens, open, "{", "}")
        .expect("proof block should have a closing brace");
    let ranges = direct_tactic_token_ranges(&tokens, open, close)
        .expect("block tactics should be indexable");

    assert_eq!(ranges.len(), 2, "{ranges:?}");
    assert_eq!(tokens[ranges[0].end - 1].text, ";");
    assert_eq!(tokens[ranges[1].end - 1].text, ";");
}

#[test]
fn inventories_and_expands_smart_tactics_inside_structural_induction() {
    let click_source = r#"
spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}

theorem reflexive(xs: TestList<int32>) {
    ensures xs == xs by {
        induct(xs) as ih {
            TestList::Nil => {
                simp();
            }
            TestList::Cons(head, tail) => {
                simp();
            }
        }
    }
}
"#;
    let sites = c0_smart_tactic_source_sites(click_source, &[])
        .expect("structural induction sites should be indexed");
    assert_eq!(
        sites,
        vec![
            SmartTacticSourceSite {
                claim_label: "reflexive.ensures_0".to_string(),
                source_index: 1,
                tactic_name: "simp".to_string(),
                position: position_at_offset(click_source, click_source.find("simp();").unwrap()),
            },
            SmartTacticSourceSite {
                claim_label: "reflexive.ensures_0".to_string(),
                source_index: 2,
                tactic_name: "simp".to_string(),
                position: position_at_offset(click_source, click_source.rfind("simp();").unwrap()),
            },
        ]
    );
    let position = c0_tactic_source_position(click_source, &[], "reflexive.ensures_0", 1)
        .expect("the first induction arm should have a source position");
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("a smart tactic in an induction arm should expand");
    assert!(expanded.contains("TestList::Nil => {\n                normalize();"));
    assert!(expanded.contains("TestList::Cons(head, tail) => {\n                normalize();"));
    verify_c0_sources(&expanded, &[]).expect("the expanded structural proof should re-verify");
}

fn expand_top_level_tactic_for_test(
    click_source: &str,
    c_sources: &[(&str, &str)],
    function_name: &str,
    claim: CProofClaim,
    tactic_index: usize,
) -> Result<String, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
    let function = find_function(&tokens, function_name)?;
    let proof = match claim {
        CProofClaim::Grouped => find_grouped_proof_span(&tokens, &function)?,
        CProofClaim::Ensure(_) | CProofClaim::ExceptionalEnsure(_) => {
            let file = parse_source_with_c_layouts(click_source, c_sources)?;
            let function_block = file
                .function_blocks()
                .iter()
                .find(|function| function.signature().name() == function_name)
                .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
            find_claim_proof_span(&tokens, &function, function_block, claim)?
        }
    };
    let span = find_tactic_span(&tokens, &proof, tactic_index)?;
    let position = position_at_offset(click_source, span.start);
    expand_c0_tactic_source_at(click_source, c_sources, position.line, position.column)
}

#[test]
fn expands_one_grouped_tactic_without_running_the_suffix() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = r#"
verifying "identity.c";

int32 identity(int32 x) {
    ensures result == x;
} by {
    execute();
    simp();
}
"#;

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Grouped,
        0,
    )
    .expect("the first grouped tactic should expand");

    assert!(!expanded.contains("execute();"));
    assert!(expanded.contains("    step();\n    simp();"));
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the source with one expanded tactic should re-verify");
}

#[test]
fn expands_grouped_immutable_read_with_multiple_claim_successors() {
    let c_source = "int32 read_first(int32 p[1]) { return p[0]; }";
    let click_source = r#"
verifying "read.c";

int32 read_first(int32 p[1]) {
    views p[0..1];
    ensures result == p[0];
} by {
    execute();
    simp();
}
"#;

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("read.c", c_source)],
        "read_first",
        CProofClaim::Grouped,
        0,
    )
    .expect("the grouped immutable read should have one common expansion");

    assert!(!expanded.contains("execute();"));
    assert!(expanded.contains("step();"), "{expanded}");
    verify_c0_sources(&expanded, &[("read.c", c_source)])
        .expect("the expanded immutable read should re-verify every grouped claim");
}

#[test]
fn expands_nested_branch_tactic_by_source_location() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = r#"
verifying "identity.c";

int32 identity(int32 x) {
    ensures result == x;
} by {
    if x == x {
        execute();
        simp();
    } else {
        execute();
        simp();
    }
}
"#;
    let then_offset = click_source
        .find("        execute();")
        .expect("then tactic should exist")
        + 8;
    let position = position_at_offset(click_source, then_offset);
    let (expanded, capture_flat_units) = super::super::proof::count_flat_proof_units(|| {
        {
            expand_c0_tactic_source_at(
                click_source,
                &[("identity.c", c_source)],
                position.line,
                position.column,
            )
        }
    });
    let expanded = expanded.expect("the nested then tactic should expand");
    assert_eq!(capture_flat_units, 1, "capture should retain one Proof");

    assert_eq!(expanded.matches("execute();").count(), 1);
    assert!(
        expanded.contains("    if x == x {\n        step();"),
        "{expanded}"
    );
    let (reverified, reverify_flat_units) = super::super::proof::count_flat_proof_units(|| {
        verify_c0_sources(&expanded, &[("identity.c", c_source)])
    });
    reverified.expect("the source with one nested expansion should re-verify");
    assert_eq!(
        reverify_flat_units, 1,
        "the rewritten nested tactic should retain one Proof"
    );
}

#[test]
fn source_positions_include_tactics_nested_in_open_blocks() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = r#"
resource known(x: int32) {
    fact x == x;
}

verifying "identity.c";

int32 identity(int32 x) {
    owns known(x);
    ensures result == x;
} by {
    open(known(x)) {
        execute();
    }
    simp();
}
"#;
    let sources = [("identity.c", c_source)];

    let nested = c0_tactic_source_position(click_source, &sources, "identity.contract", 1)
        .expect("the tactic inside `open` should have a source position");
    assert_eq!(
        nested,
        SourcePosition {
            line: 13,
            column: 9,
            origin: None
        }
    );

    let continuation = c0_tactic_source_position(click_source, &sources, "identity.contract", 2)
        .expect("the tactic after `open` should retain its source position");
    assert_eq!(
        continuation,
        SourcePosition {
            line: 15,
            column: 5,
            origin: None
        }
    );
}

#[test]
fn expands_common_step_after_frontier_branch() {
    let c_source = r#"
int32 increment_selected(int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
    } else {
        y = 0;
    }
    y = y + 1;
    return y;
}
"#;
    let click_source = r#"
verifying "increment.c";

int32 increment_selected(int32 x) {
    requires x < 2147483647;
    ensures result > 0 by {
        step();
        branch ensuring {
            fact y >= 0;
            fact y < 2147483647;
        } then {
            step();
        } else {
            step();
        }
        step();
        step();
        simp();
    }
}
"#;
    let selected_offset = click_source
        .find("        step();\n        step();\n        simp();")
        .expect("common step should exist")
        + 8;
    let position = position_at_offset(click_source, selected_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("increment.c", c_source)],
        position.line,
        position.column,
    )
    .expect("common step should expand");

    verify_c0_sources(&expanded, &[("increment.c", c_source)]).unwrap_or_else(|error| {
        panic!("expanded common step should check:\n{error:?}\n{expanded}")
    });
}

#[test]
fn expands_deferred_simp_after_frontier_branch() {
    let c_source = r#"
int32 positive_after_branch(int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
    } else {
        y = 0;
    }
    y = y + 1;
    return y;
}
"#;
    let click_source = r#"
verifying "positive.c";

int32 positive_after_branch(int32 x) {
    requires x < 2147483647;
    ensures result > 0 by {
        step();
        branch ensuring {
            fact y >= 0;
            fact y < 2147483647;
        } then {
            step();
        } else {
            step();
        }
        step();
        step();
        simp();
    }
}
"#;
    let selected_offset = click_source
        .find("        simp();")
        .expect("simp should exist")
        + 8;
    let position = position_at_offset(click_source, selected_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("positive.c", c_source)],
        position.line,
        position.column,
    )
    .expect("deferred simp should expand");

    verify_c0_sources(&expanded, &[("positive.c", c_source)]).unwrap_or_else(|error| {
        panic!("expanded deferred simp should check:\n{error:?}\n{expanded}")
    });
}

#[test]
fn shares_equal_deferred_expansions_after_frontier_branch() {
    let c_source = r#"
int32 same_after_branch(int32 x, int32 flag) {
    int32 y;
    if (flag != 0) {
        y = x;
    } else {
        y = x;
    }
    return y;
}
"#;
    let click_source = r#"
verifying "same.c";

int32 same_after_branch(int32 x, int32 flag) {
    ensures result == x by {
        step();
        branch then { step(); } else { step(); }
        step();
        simp();
    }
}
"#;
    let selected_offset = click_source
        .find("        simp();")
        .expect("simp should exist")
        + 8;
    let position = position_at_offset(click_source, selected_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("same.c", c_source)],
        position.line,
        position.column,
    )
    .expect("equal deferred certificates should expand");

    assert!(!expanded.contains("if at(statement(1).entry"), "{expanded}");
    verify_c0_sources(&expanded, &[("same.c", c_source)]).unwrap_or_else(|error| {
        panic!("shared deferred expansion should check:\n{error:?}\n{expanded}")
    });
}

#[test]
fn expands_common_deferred_tactic_with_a_returning_branch_arm() {
    let c_source = r#"
int32 clamp_nonnegative(int32 x) {
    if (x < 0) {
        return 0;
    }
    return x;
}
"#;
    let click_source = r#"
verifying "returning.c";

int32 clamp_nonnegative(int32 x) {
    ensures result >= 0 by {
        branch then {
            step();
            simp();
        } else {}
        step();
        simp();
    }
}
"#;
    let selected_offset = click_source
        .rfind("        simp();")
        .expect("common simp should exist")
        + 8;
    let position = position_at_offset(click_source, selected_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("returning.c", c_source)],
        position.line,
        position.column,
    )
    .expect("reachable continuation simp should expand");

    verify_c0_sources(&expanded, &[("returning.c", c_source)]).unwrap_or_else(|error| {
        panic!("returning-arm deferred expansion should check:\n{error:?}\n{expanded}")
    });
}

#[test]
fn expands_deferred_simp_after_nested_frontier_branches() {
    let c_source = r#"
int32 nested_nonnegative(int32 x, int32 flag) {
    int32 y;
    if (flag != 0) {
        if (x >= 0) {
            y = x;
        } else {
            y = 0;
        }
    } else {
        y = 0;
    }
    return y;
}
"#;
    let click_source = r#"
verifying "nested.c";

int32 nested_nonnegative(int32 x, int32 flag) {
    ensures result >= 0 by {
        step();
        branch ensuring {
            fact y >= 0;
        } then {
            branch ensuring {
                fact y >= 0;
            } then { step(); } else { step(); }
        } else { step(); }
        step();
        simp();
    }
}
"#;
    let (verified, flat_units) = super::super::proof::count_flat_proof_units(|| {
        verify_c0_sources(click_source, &[("nested.c", c_source)])
    });
    let verified = verified.expect("nested end-of-arm interfaces should verify through Proof");
    assert_eq!(flat_units, 1, "the nested script should retain one Proof");
    let retained = verified[0]
        .expanded_proof_tactics()
        .expect("the nested proof should retain surface provenance");
    fn count_branches(tactics: &[ProofTactic]) -> usize {
        tactics
            .iter()
            .map(|tactic| match tactic {
                ProofTactic::Branch(branch) => {
                    1 + count_branches(&branch.then_tactics) + count_branches(&branch.else_tactics)
                }
                ProofTactic::If(proof_if) => {
                    count_branches(&proof_if.then_tactics) + count_branches(&proof_if.else_tactics)
                }
                ProofTactic::Open(open) => count_branches(&open.tactics),
                _ => 0,
            })
            .sum()
    }
    assert_eq!(count_branches(&retained), 2, "{retained:#?}");

    let selected_offset = click_source
        .find("        simp();")
        .expect("common simp should exist")
        + 8;
    let position = position_at_offset(click_source, selected_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("nested.c", c_source)],
        position.line,
        position.column,
    );
    let expanded = expanded.expect("nested deferred simp should expand");

    verify_c0_sources(&expanded, &[("nested.c", c_source)]).unwrap_or_else(|error| {
        panic!("nested deferred expansion should check:\n{error:?}\n{expanded}")
    });

    let inner_offset = click_source
        .find("            branch ensuring {")
        .expect("inner branch should exist")
        + 12;
    let inner_position = position_at_offset(click_source, inner_offset);
    let inner = expand_c0_tactic_source_at(
        click_source,
        &[("nested.c", c_source)],
        inner_position.line,
        inner_position.column,
    );
    let inner = inner.expect("the retained inner branch should expand");
    verify_c0_sources(&inner, &[("nested.c", c_source)]).unwrap_or_else(|error| {
        panic!("inner branch expansion should reverify:\n{error:?}\n{inner}")
    });
}

#[test]
fn locates_a_block_tactic_as_one_source_statement() {
    let source = "by { have x == x by simp; simp(); }";
    let tokens = scan_source_tokens(source).expect("source should scan");
    let proof = proof_span(&tokens, 0).expect("proof should have a span");

    let first = find_tactic_span(&tokens, &proof, 0).expect("first tactic should exist");
    let second = find_tactic_span(&tokens, &proof, 1).expect("second tactic should exist");

    assert_eq!(&source[first], "have x == x by simp;");
    assert_eq!(&source[second], "simp();");
}

#[test]
fn hides_statement_local_opaque_call_facts_from_surface_premises() {
    let zero_c = "int32 zero() { return 0; }";
    let caller_c = "int32 caller() { int32 value; value = zero(); return value; }";
    let click_source = r#"
verifying "zero.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    execute();
    simp();
}
"#;
    let sources = [("zero.c", zero_c), ("caller.c", caller_c)];

    let expanded =
        expand_top_level_tactic_for_test(click_source, &sources, "caller", CProofClaim::Grouped, 0)
            .expect("opaque call internals should not become surface premises");

    assert_eq!(expanded.matches("execute();").count(), 1);
    verify_c0_sources(&expanded, &sources)
        .expect("the caller with one expanded tactic should re-verify");
}

#[test]
fn opaque_call_expansion_keeps_only_consumed_ambient_conditions() {
    let positive_c = "int32 positive(int32 x) { return x; }";
    let caller_c = "int32 caller(int32 x) { int32 result; result = positive(x); return result; }";
    let click_source = r#"
verifying "positive.c";
verifying "caller.c";

int32 positive(int32 x) {
    requires 0 < x;
    ensures result == x;
} by {
    execute();
    simp();
}

int32 caller(int32 x) {
    requires 0 < x;
    requires x < 100;
    requires x != 37;
    ensures result == x;
} by {
    execute();
    simp();
}
"#;
    let sources = [("positive.c", positive_c), ("caller.c", caller_c)];

    let expanded =
        expand_top_level_tactic_for_test(click_source, &sources, "caller", CProofClaim::Grouped, 0)
            .expect("the call should expand with its consumed precondition");
    // Both statements run in the whole context; the call's precondition is
    // proved from it and the expansion names no premise.
    assert_eq!(expanded.matches("step();").count(), 3, "{expanded}");
    verify_c0_sources(&expanded, &sources).expect("the call steps should check");
}

#[test]
fn opaque_call_expansion_keeps_memory_condition_safety() {
    let positive_at_c =
        "struct box { int32 value; }; int32 positive_at(struct box* p) { return p->value; }";
    let caller_c = r#"struct box { int32 value; };
int32 caller(struct box* p, int32 x) {
    int32 result;
    result = positive_at(p);
    return result;
}"#;
    let click_source = r#"
verifying "positive_at.c";
verifying "caller.c";

int32 positive_at(struct box* p) {
    views p->value;
    requires 0 < p->value;
    ensures result == p->value;
} by {
    execute();
    simp();
}

int32 caller(struct box* p, int32 x) {
    views p->value;
    requires 0 < p->value;
    requires x < 100;
    ensures result == p->value;
} by {
    execute();
    simp();
}
"#;
    let sources = [("positive_at.c", positive_at_c), ("caller.c", caller_c)];

    let expanded =
        expand_top_level_tactic_for_test(click_source, &sources, "caller", CProofClaim::Grouped, 0)
            .expect("the memory-reading precondition should expand");
    // Both statements run in the whole context; the call's memory-reading
    // precondition is proved from it and the expansion names no premise.
    assert_eq!(expanded.matches("step();").count(), 3, "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the condition and its ambient view should verify normally");
}

#[test]
fn expands_public_opaque_call_results_through_later_call_arguments() {
    let zero_c = "int32 zero() { return 0; }";
    let passthrough_c = "int32 passthrough(int32 x) { return x; }";
    let caller_c = r#"int32 caller() {
    int32 first;
    int32 second;
    first = zero();
    second = passthrough(first);
    return second;
}"#;
    let click_source = r#"
verifying "zero.c";
verifying "passthrough.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 passthrough(int32 x) {
    ensures result == x;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    execute();
    simp();
}
"#;
    let sources = [
        ("zero.c", zero_c),
        ("passthrough.c", passthrough_c),
        ("caller.c", caller_c),
    ];
    let final_simp = click_source
        .rfind("simp();")
        .expect("caller final simp should exist");
    let position = position_at_offset(click_source, final_simp);

    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("public call facts should compose through their receiving locals");

    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("call-havoc"), "{expanded}");
    assert!(!expanded.contains("symbolic-pointer"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the expanded public fact chain should independently re-verify");
}

#[test]
fn grouped_simp_distinguishes_c_local_result_from_contract_result() {
    let zero_c = "int32 zero() { return 0; }";
    let caller_c = "int32 caller() { int32 result; result = zero(); return result; }";
    let click_source = r#"
verifying "zero.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    execute();
    simp();
}
"#;
    let sources = [("zero.c", zero_c), ("caller.c", caller_c)];
    let final_simp = click_source
        .rfind("simp();")
        .expect("caller final simp should exist");
    let position = position_at_offset(click_source, final_simp);

    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the grouped simp should expand across the local result assignment");

    verify_c0_sources(&expanded, &sources)
        .expect("the explicit C result binding should check without aliasing contract result");

    let explicit_source = r#"
verifying "zero.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    execute();
    have at(statement(2).entry, c(result)) == 0 by {
        assumption();
    }
    have result == at(statement(2).entry, c(result)) by {
        normalize();
    }
    assumption();
}
"#;
    verify_c0_sources(explicit_source, &sources)
        .expect("`c(result)` should denote the C local rather than contract result");
}

#[test]
fn selected_tactic_uses_an_unselected_callee_contract_without_proving_its_body() {
    let zero_c = "int32 zero() { return 1; }";
    let caller_c = "int32 caller() { int32 value; value = zero(); return value; }";
    let click_source = r#"
verifying "zero.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    step();
    execute();
    simp();
}
"#;
    let sources = [("zero.c", zero_c), ("caller.c", caller_c)];

    let expanded =
        expand_top_level_tactic_for_test(click_source, &sources, "caller", CProofClaim::Grouped, 0)
            .expect("capture should use the well-formed unselected callee contract");
    assert!(expanded.contains("step();"));
    let error = verify_c0_sources(&expanded, &sources)
        .expect_err("whole-file verification must still reject the callee implementation proof");
    assert!(error.message().contains("zero.ensures_0"));
    assert!(error.message().contains("unclosed goal:"));
}

#[test]
fn grouped_simp_expansion_preserves_each_claim_closer() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = r#"
verifying "identity.c";

int32 identity(int32 x) {
    ensures result == x;
    ensures result == old(x);
} by {
    execute();
    simp();
}
"#;
    let sources = [("identity.c", c_source)];

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &sources,
        "identity",
        CProofClaim::Grouped,
        1,
    )
    .expect("grouped simp should expand");

    assert_eq!(
        expanded.matches("\n    assumption();").count(),
        2,
        "each grouped claim should retain one top-level closer:\n{expanded}"
    );
    verify_c0_sources(&expanded, &sources)
        .expect("each grouped claim closer should survive expansion");
}

#[test]
fn return_fold_retains_post_return_proof_through_expansion() {
    let sources = [("fold.c", "int f(int *p) { return 0; }")];
    let source = r#"
verifying "fold.c";
function reflexive(p: int32*) -> int32 { if p == p { 1 } else { 0 } }
resource Cell(p: int32*) {
    field tag: int32;
    owns p[0..1];
    fact reflexive(p) == 1;
}
int32 f(int32* p) {
    consumes p[0..1];
    produces out: Cell(p);
    ensures result == 0;
} by {
    execute();
    have reflexive(p) == 1 by { unfold(reflexive(p)); normalize(); }
    let out = fold(Cell(p), { tag: 1 });
    simp();
}
"#;
    verify_c0_sources(source, &sources).unwrap();
    let expanded = expand_top_level_tactic_for_test(source, &sources, "f", CProofClaim::Grouped, 3)
        .expect("the returned fold's final closer expands");
    verify_c0_sources(&expanded, &sources).expect("the checked have survives explicit closers");
    let false_body = source.replace("if p == p { 1 }", "if p == p { 0 }");
    assert!(verify_c0_sources(&false_body, &sources).is_err());
}

#[test]
fn grouped_simp_expansion_preserves_resource_scalar_and_quantified_transitions() {
    let c_source = "int32 inspect(int32 p[1], int32 x) { return 0; }";
    let click_source = r#"
verifying "inspect.c";

int32 inspect(int32 p[1], int32 x) {
    requires forall (k: int32) {
        0 <= k and k < 1 implies x == x
    };
    owns p[0..1];
    ensures result == 0;
    ensures forall (k: int32) {
        0 <= k and k < 1 implies x == x
    };
} by {
    execute();
    simp();
}
"#;
    let sources = [("inspect.c", c_source)];

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &sources,
        "inspect",
        CProofClaim::Grouped,
        1,
    )
    .expect("grouped simp should capture every newly closed claim");

    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the grouped transition certificate should re-verify");
}

#[test]
fn grouped_simp_expansion_uses_explicit_frame_consequences() {
    let c_source = r#"
int32 increment_and_return_old(int32 p[1]) {
    int32 result;
    result = p[0];
    p[0] = 0;
    return result;
}
"#;
    let click_source = r#"
verifying "increment.c";

int32 increment_and_return_old(int32 p[1]) {
    owns p[0..1];
    ensures result == old(p[0]);
    ensures p[0] == 0;
} by {
    execute();
    simp();
}
"#;
    let sources = [("increment.c", c_source)];

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &sources,
        "increment_and_return_old",
        CProofClaim::Grouped,
        1,
    )
    .expect("grouped simp should capture frame-dependent claims");

    assert!(!expanded.contains("simp();"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the grouped frame transition certificate should re-verify");
}

#[test]
fn expansion_preserves_unfolded_resource_and_predicate_fact_forms() {
    let c_source = r#"
struct box {
    int32 len;
    int32 cap;
    int32* data;
};

int32 inspect(struct box* owner) {
    int32 ignored;
    return 0;
}
"#;
    let click_source = r#"
predicate terminated_at(data: int32[], length: int32) {
    data[length] == 0
}

resource owned_box(owner: struct box*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact terminated_at(owner->data, owner->len);
    fact separate(
        memory(*owner),
        memory(owner->data[0..owner->cap])
    );
}

verifying "inspect.c";

int32 inspect(struct box* owner) {
    consumes owned_box(owner);
    ensures result == 0;
} by {
    unfold(owned_box(owner));
    unfold(terminated_at);
    step();
    execute();
    simp();
}
"#;

    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("inspect.c", c_source)],
        "inspect",
        CProofClaim::Grouped,
        2,
    )
    .expect("the declaration should expand with unfolded surface facts");

    // A bare `step()` runs in the whole context: the unfolded resource and
    // predicate facts are visible to it without being spelled as premises,
    // and the expansion keeps the step as written.
    assert!(expanded.contains("step();"), "{expanded}");
    verify_c0_sources(&expanded, &[("inspect.c", c_source)])
        .expect("the expansion with unfolded facts in context should verify");
}

#[test]
fn source_position_maps_smart_and_implicit_default_proofs() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let explicit = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
} by auto;
"#;
    assert_eq!(
        c0_tactic_source_position(
            explicit,
            &[("identity.c", c_source)],
            "identity.contract",
            0,
        )
        .unwrap(),
        SourcePosition {
            line: 4,
            column: 6,
            origin: None
        }
    );
    assert!(
        c0_tactic_source_position(
            explicit,
            &[("identity.c", c_source)],
            "identity.contract",
            2,
        )
        .is_err()
    );
    let expanded = expand_c0_tactic_source_at(explicit, &[("identity.c", c_source)], 4, 6)
        .expect("an internal smart-proof timing should select the whole source proof");
    assert!(!expanded.contains("by auto"));
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the expanded smart proof should verify");

    let implicit = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
}
"#;
    assert_eq!(
        c0_tactic_source_position(
            implicit,
            &[("identity.c", c_source)],
            "identity.ensures_0",
            0,
        )
        .unwrap(),
        SourcePosition {
            line: 3,
            column: 5,
            origin: None
        }
    );
    assert!(
        c0_tactic_source_position(
            implicit,
            &[("identity.c", c_source)],
            "identity.ensures_0",
            2,
        )
        .is_err()
    );
}

#[test]
fn expanded_uint8_facts_print_as_parseable_typed_literals() {
    let c_source = "int32 contains(uint8 p[], int32 n) { return 0; }";
    let click_source = r#"verifying "contains.c";
int32 contains(uint8 p[], int32 n) {
    requires viewable(p[0..n]);
    requires bytes_contains(p, 0, n, 'x');
    ensures bytes_contains(p, 0, n, 'x') by {
        execute();
        unfold(bytes_contains);
        obtain (found: int32) {
            0 <= found and found < n and p[found] == 'x'
        };
        witness { k: found };
        simp();
    }
}"#;
    let offset = click_source.rfind("simp").expect("simp should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("contains.c", c_source)],
        position.line,
        position.column,
    )
    .expect("uint8 proposition should expand");

    // The `simp` closes the proof the `witness` opened, so it expands to
    // that one step rather than restating the claim.
    assert!(
        expanded.contains("witness { k: found };\n        assumption();"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("contains.c", c_source)])
        .expect("the expansion should re-verify");
    // A uint8 fact still prints as a parseable typed literal.
    let file = parse_source_with_c_layouts(click_source, &[("contains.c", c_source)])
        .expect("the sidecar parses");
    let Ensure::Proposition(claim) = file.function_blocks()[0].ensures()[0].ensure() else {
        panic!("the claim is a proposition");
    };
    assert_eq!(
        crate::surface::printing::source_click_proposition(claim),
        "bytes_contains(p, 0, n, 120u8)"
    );
}

#[test]
fn expanded_bitvector_facts_print_parseable_negative_literals() {
    let c_source = "int32 all_bits() { return ~0; }";
    // `~0` is -1, and a sidecar literal takes the same type it takes in C, so
    // the claim is spelled with the negative literal the expansion prints.
    let click_source = r#"verifying "all_bits.c";
int32 all_bits() {
    ensures result == -1 by auto;
}"#;
    let offset = click_source.find("auto").expect("auto should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("all_bits.c", c_source)],
        position.line,
        position.column,
    )
    .expect("bitvector proposition should expand");

    assert!(expanded.contains("result == -1"));
    verify_c0_sources(&expanded, &[("all_bits.c", c_source)])
        .expect("printed negative literal should parse and re-verify");
}

#[test]
fn expanded_branch_certificate_uses_the_branch_entry_state() {
    let c_source = r#"int32 compare_swap2(int32 p[2]) {
    int32 tmp;
    if (p[1] < p[0]) {
        tmp = p[0];
        p[0] = p[1];
        p[1] = tmp;
    } else {
        tmp = 0;
    }
    return 0;
}"#;
    let click_source = r#"verifying "compare_swap2.c";
predicate sorted_pair(p: int32[2]) {
    p[0] <= p[1]
}
int32 compare_swap2(int32 p[2]) {
    consumes p[0..2];
    ensures sorted_pair(p) by {
        execute();
        unfold(sorted_pair);
        simp();
    }
}"#;
    let expanded_execute = expand_top_level_tactic_for_test(
        click_source,
        &[("compare_swap2.c", c_source)],
        "compare_swap2",
        CProofClaim::Ensure(0),
        0,
    );
    let expanded_execute =
        expanded_execute.expect("branch-shaped execute should expand from retained Proof steps");
    verify_c0_sources(&expanded_execute, &[("compare_swap2.c", c_source)])
        .expect("expanded branch-shaped execute should verify normally");
    let original_condition = "if at(statement(1).entry, p[1]) < at(statement(1).entry, p[0]) {";
    let corrupted_condition = "if at(statement(1).entry, p[1]) >= at(statement(1).entry, p[0]) {";
    let corrupted_execute = expanded_execute.replacen(original_condition, corrupted_condition, 1);
    assert_ne!(
        corrupted_execute, expanded_execute,
        "the retained execute branch condition should be present"
    );
    verify_c0_sources(&corrupted_execute, &[("compare_swap2.c", c_source)])
        .expect_err("ordinary verification should reject a corrupted execute branch");

    let offset = click_source.rfind("simp").expect("simp should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("compare_swap2.c", c_source)],
        position.line,
        position.column,
    );
    let expanded = expanded.expect("post-execution simp should expand");

    // The branch anchors at the statement that branched; statement 0 is
    // the `tmp` declaration, so this is the same state as function entry
    // written at the point the certificate actually read it.
    assert!(
        expanded.contains("if at(statement(1).entry, p[1]) < at(statement(1).entry, p[0])"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("compare_swap2.c", c_source)])
        .expect("branch certificate should check against the state where it branched");
}

/// A branch over a field read through a struct pointer expands to a
/// condition that names the field, as a sidecar writes it.
#[test]
fn expanded_branch_condition_names_a_struct_pointer_field() {
    let c_source = "struct cell { int first; int second; };\nint pick(struct cell *p) { if (p->second > 0) { return 1; } return 0; }";
    let click_source = "verifying \"pick.c\";\nint32 pick(struct cell* p) { views p->second; ensures result >= 0; } by { execute(); simp(); }\n";
    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("pick.c", c_source)],
        "pick",
        CProofClaim::Grouped,
        0,
    )
    .expect("a branch over a field should expand");
    assert!(
        expanded.contains("if at(statement(0).entry, p->second) > at(statement(0).entry, 0) {"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("pick.c", c_source)])
        .expect("the expansion naming the field should verify");
}

/// The same through a local struct pointer.
#[test]
fn expanded_branch_condition_names_a_local_struct_pointer_field() {
    let c_source = "struct cell { int first; int second; };\nint pick(struct cell *p) { struct cell *q = p; if (q->second > 0) { return 1; } return 0; }";
    let click_source = "verifying \"pick.c\";\nint32 pick(struct cell* p) { views p->second; ensures result >= 0; } by { execute(); simp(); }\n";
    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("pick.c", c_source)],
        "pick",
        CProofClaim::Grouped,
        0,
    )
    .expect("a branch over a field should expand");
    assert!(!expanded.contains("load_int32("), "{expanded}");
    assert!(expanded.contains("->second) > "), "{expanded}");
    verify_c0_sources(&expanded, &[("pick.c", c_source)])
        .expect("the expansion naming the field should verify");
}

/// A field of a struct nested in another, and a pointer field to a struct,
/// are written as places too.
#[test]
fn expanded_branch_condition_names_nested_and_pointer_fields() {
    let c_source = "struct inner { int x; int y; };\nstruct outer { int tag; struct inner in; struct outer *next; };\nint pick(struct outer *p) { if (p->in.y > 0) { return 1; } if (p->next == 0) { return 2; } return 0; }";
    let click_source = "verifying \"pick.c\";\nint32 pick(struct outer* p) { views p->in.y; views p->next; ensures result >= 0; } by { execute(); simp(); }\n";
    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("pick.c", c_source)],
        "pick",
        CProofClaim::Grouped,
        0,
    )
    .expect("branches over nested fields should expand");
    assert!(expanded.contains("p->in.y) > "), "{expanded}");
    assert!(expanded.contains("p->next"), "{expanded}");
    assert!(!expanded.contains("load_"), "{expanded}");
    verify_c0_sources(&expanded, &[("pick.c", c_source)])
        .expect("the expansion naming the fields should verify");
}

/// A field read through a pointer that was itself loaded from a field is
/// written as the place, `p->next->second`, not as a byte offset from it.
#[test]
fn expanded_branch_condition_names_a_field_through_a_loaded_pointer() {
    let c_source = "struct node { int first; int second; struct node *next; };\nint pick(struct node *p) { if (p->next->second > 0) { return 1; } return 0; }";
    let click_source = "verifying \"pick.c\";\nint32 pick(struct node* p) { views p->next; views p->next->second; ensures result >= 0; } by { execute(); simp(); }\n";
    let expanded = expand_top_level_tactic_for_test(
        click_source,
        &[("pick.c", c_source)],
        "pick",
        CProofClaim::Grouped,
        0,
    )
    .expect("a branch over a field through a loaded pointer should expand");
    assert!(expanded.contains("p->next->second) > "), "{expanded}");
    assert!(!expanded.contains("load_"), "{expanded}");
    verify_c0_sources(&expanded, &[("pick.c", c_source)])
        .expect("the expansion naming the field should verify");
}

/// `arithmetic` on a `uint64` goal expands to the bridge steps it took,
/// and the expansion verifies with no `arithmetic()` left to plan.
#[test]
fn uint64_arithmetic_expands_to_its_integer_bridge_steps() {
    let source = "theorem step_two(i: uint64, length: uint64) {\n    requires i <= length;\n    requires i + 1u64 < length;\n    requires length <= 2147483647u64;\n    ensures i + 2u64 <= length by {\n        arithmetic() using { i <= length; i + 1u64 < length; length <= 2147483647u64; }\n    }\n}\n";
    verify_c0_sources(source, &[]).expect("the uint64 goal verifies");
    let expanded = expand_c0_claim_source_by_label(source, &[], "step_two.ensures_0")
        .expect("the uint64 arithmetic step expands");
    for step in [
        "apply(uint64_less_than_to_integer((i + 1u64), length))",
        "apply(uint64_add_to_integer(i, 2u64))",
        "apply(uint64_to_integer_less_equal_implies_less_equal((i + 2u64), length))",
        "arithmetic_certificate {",
    ] {
        assert!(expanded.contains(step), "{step}\n{expanded}");
    }
    assert!(!expanded.contains("arithmetic()"), "{expanded}");
    verify_c0_sources(&expanded, &[]).expect("the expansion verifies");
    // Without the bound on `i`, `i + 1` may wrap, and the step says so.
    let unbounded = source.replace("i <= length; i + 1u64", "i + 1u64");
    assert_ne!(unbounded, source);
    let error = verify_c0_sources(&unbounded, &[]).expect_err("the sum may wrap");
    assert!(
        error.message().contains("stays within uint64"),
        "{}",
        error.message()
    );
}

#[test]
fn wide_arithmetic_promotes_unsuffixed_literals_in_checked_bridge_arguments() {
    for (carrier, suffix) in [("uint64", "u64"), ("int64", "i64")] {
        let source = format!(
            "theorem span(n: {carrier}) {{ requires 4{suffix} <= n; requires n <= 16{suffix}; \
             ensures (16 - n) + 4 <= 16 by {{ arithmetic() using {{ 4 <= n; n <= 16; }} }} }}"
        );
        verify_c0_sources(&source, &[]).expect("implicit wide literals must verify");
        let expanded = expand_c0_claim_source_by_label(&source, &[], "span.ensures_0")
            .expect("the promoted bridge arguments must expand");
        assert!(
            expanded.contains(&format!("{carrier}_subtract_to_integer(16{suffix}, n)")),
            "{expanded}"
        );
        assert!(!expanded.contains("arithmetic()"), "{expanded}");
        verify_c0_sources(&expanded, &[]).expect("the explicit bridges must independently verify");
        let missing_bound = source.replace("4 <= n; n <= 16;", "n <= 16;");
        verify_c0_sources(&missing_bound, &[])
            .expect_err("the final inequality lacks its lower bound");
        let false_result = source.replace("+ 4 <= 16 by", "+ 5 <= 16 by");
        verify_c0_sources(&false_result, &[]).expect_err("promotion cannot prove a false bound");
    }
}

#[test]
fn wide_arithmetic_reads_listed_bounds_at_their_named_snapshot() {
    for carrier in ["uint64", "int64"] {
        let c_source = format!("{carrier} advance({carrier} n) {{ n = n - 4; return n; }}");
        let source = format!(
            r#"verifying "advance.c";
{carrier} advance({carrier} n) {{
    requires 4 <= n;
    requires n <= 16;
    ensures result <= 12 by {{
        mark before;
        execute();
        have result <= 12 by {{
            arithmetic() using {{
                at(before, 4 <= n);
                at(before, n <= 16);
                result == at(before, n) - 4;
            }}
        }}
        simp();
    }}
}}"#
        );
        let sources = [("advance.c", c_source.as_str())];
        verify_c0_sources(&source, &sources).expect("snapshot bounds must verify");
        let expanded = expand_c0_claim_source_by_label(&source, &sources, "advance.ensures_0")
            .expect("snapshot bridges must expand");
        assert!(!expanded.contains("arithmetic()"), "{expanded}");
        verify_c0_sources(&expanded, &sources).expect("snapshot bridges must independently verify");
        let missing_bound = source.replace("at(before, n <= 16);", "");
        verify_c0_sources(&missing_bound, &sources)
            .expect_err("a historical upper bound cannot be inferred from type bounds");
        let false_result = source.replace("result <= 12", "result <= 11");
        verify_c0_sources(&false_result, &sources)
            .expect_err("snapshot facts cannot prove a false bound");
    }
}

/// The same for a signed 64-bit goal: each sum is shown defined from its
/// Integer bounds before it is observed, and a premise over a sum is
/// carried only once that sum is defined.
#[test]
fn int64_arithmetic_expands_to_its_integer_bridge_steps() {
    let source = "theorem step_two(i: int64, length: int64) {\n    requires 0i64 <= i;\n    requires i <= length;\n    requires i + 1i64 < length;\n    requires length <= 2147483647i64;\n    ensures i + 2i64 <= length by {\n        arithmetic() using { 0i64 <= i; i <= length; i + 1i64 < length; length <= 2147483647i64; }\n    }\n}\n";
    verify_c0_sources(source, &[]).expect("the int64 goal verifies");
    let expanded = expand_c0_claim_source_by_label(source, &[], "step_two.ensures_0")
        .expect("the int64 arithmetic step expands");
    for step in [
        "apply(int64_add_defined_by_integer_bounds(i, 1i64))",
        "apply(int64_add_to_integer(i, 2i64))",
        "apply(int64_less_than_to_integer((i + 1i64), length))",
        "apply(int64_to_integer_less_equal_implies_less_equal((i + 2i64), length))",
    ] {
        assert!(expanded.contains(step), "{step}\n{expanded}");
    }
    assert!(!expanded.contains("arithmetic()"), "{expanded}");
    verify_c0_sources(&expanded, &[]).expect("the expansion verifies");
    // Without the lower bound on `i`, `i + 1` may overflow below.
    let unbounded = source.replace("{ 0i64 <= i; i <= length;", "{ i <= length;");
    assert_ne!(unbounded, source);
    let error = verify_c0_sources(&unbounded, &[]).expect_err("the sum may overflow");
    assert!(
        error.message().contains("stays within int64"),
        "{}",
        error.message()
    );
}

/// A sidecar writes an inherent method without the module its `impl` block
/// is in, and the proof tools are asked for it by the importer's name,
/// which has that module. The method is found by the spelling the source
/// index reads.
#[test]
fn an_inherent_method_in_another_module_is_located_by_its_type() {
    let source = "verifying \"lib.rs\";\nimpl adler2::Adler32 {\n    fn compute(&mut self, seed: u32) {\n        ensures 0 == 0;\n    } by { execute(); simp(); }\n}\n";
    let tokens = scan_source_tokens(source).unwrap();
    let beside = "__rust_q_I6_adler2_T29___rust_q_I6_adler2_I7_Adler32_I7_compute";
    let elsewhere = "__rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute";
    let body = find_function(&tokens, beside).expect("the source spelling is indexed");
    assert_eq!(
        find_function(&tokens, elsewhere)
            .expect("the importer's name is located")
            .body_open,
        body.body_open
    );
    // A function that is not that method is not found by this route.
    assert!(find_function(&tokens, "__rust_q_I6_adler2_I4_algo_I7_compute").is_err());
    assert_eq!(
        rust_inherent_method_in_its_type_module(elsewhere).as_deref(),
        Some(beside)
    );
    assert_eq!(rust_inherent_method_in_its_type_module("compute"), None);
}

#[test]
fn expanded_contract_let_facts_remain_source_indexable() {
    let c_source = "int32 increment(int32 x) { return x + 1; }";
    let click_source = r#"verifying "increment.c";
int32 increment(int32 x) {
    let max: int32 = 2147483647;
    let expected = x + 1;
    requires x < max;
    ensures result_value: result == expected by auto;
}"#;
    let offset = click_source.find("auto").expect("auto should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("increment.c", c_source)],
        position.line,
        position.column,
    )
    .expect("contract-let proof should expand");

    // The step runs in the whole context; the contract `let` needs no
    // spelling as a premise. The expansion must still verify.
    verify_c0_sources(&expanded, &[("increment.c", c_source)])
        .expect("parenthesized contract lets should re-verify");
    c0_tactic_source_position(
        &expanded,
        &[("increment.c", c_source)],
        "increment.result_value",
        0,
    )
    .expect("semicolons inside contract lets must not split source tactics");
}

#[test]
fn expanded_post_execution_apply_retains_its_facts_for_the_closer() {
    let c_source = "int32 inspect(uint8 p[], uint64 len) { return 0; }";
    let click_source = r#"verifying "inspect.c";
int32 inspect(uint8 p[], uint64 len) {
    requires viewable(p[0..len + 1u64]);
    requires cstr_len(p, len);
    ensures p[len] == '\0' by {
        execute();
        apply(cstr_len_has_terminator(p, len));
        simp();
    }
}"#;
    let offset = click_source.find("apply").expect("apply should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("inspect.c", c_source)],
        position.line,
        position.column,
    )
    .expect("post-execution apply should expand");

    assert!(expanded.contains("apply(cstr_len_has_terminator(p, len)) using"));
    verify_c0_sources(&expanded, &[("inspect.c", c_source)])
        .expect("explicit apply conclusions should remain available to the trailing simp");
}

#[test]
fn expansion_retains_callees_used_by_an_earlier_claim() {
    let callee_source = r#"int32 set_cell(int32 p[], int32 value) {
    p[0] = value;
    return value;
}"#;
    let caller_source = r#"int32 set_then_read(int32 p[], int32 value) {
    int32 ignored;
    ignored = set_cell(p, value);
    return p[0];
}"#;
    let click_source = r#"verifying "set_cell.c";
verifying "set_then_read.c";
int32 set_cell(int32 p[], int32 value) {
    owns p[0..1] by auto;
    ensures p[0] == value by auto;
    ensures result == value by auto;
}
int32 set_then_read(int32 p[], int32 value) {
    owns p[0..1] by {
        step();
        step();
        step();
    }
    ensures result == value by {
        step();
        step();
        step();
        simp();
    }
}"#;
    let sources = [
        ("set_cell.c", callee_source),
        ("set_then_read.c", caller_source),
    ];
    let position = c0_tactic_source_position(click_source, &sources, "set_then_read.ensures_0", 0)
        .expect("later claim should have a source tactic");
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("selected later-claim tactic should expand with the callee available");

    verify_c0_sources(&expanded, &sources)
        .expect("expanded later claim should re-verify with its earlier claim");
}

#[test]
fn expands_a_deferred_tactic_in_one_nested_proof_branch() {
    let c_source = r#"int32 nested(int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
        if (y > 0) { y = y + 1; } else { y = 0; }
    } else {
        y = 0;
    }
    return y;
}"#;
    let click_source = r#"verifying "nested.c";
int32 nested(int32 x) {
    requires x < 2147483647;
    ensures result >= 0 by {
        step();
        if x >= 0 {
            step();
            step();
            if y > 0 {
                step();
                step();
                step();
                simp();
            } else {
                step();
                step();
                step();
                simp();
            }
        } else {
            step();
            step();
            step();
            simp();
        }
    }
}"#;
    let needle = "step();\n                step();\n                step();\n                simp";
    let offset = click_source
        .find(needle)
        .map(|start| start + needle.rfind("simp").unwrap())
        .expect("inner else simp should be present");
    let position = position_at_offset(click_source, offset);
    let (verified, original_flat_units) = proof::count_flat_proof_units(|| {
        verify_c0_sources(click_source, &[("nested.c", c_source)])
    });
    verified.expect("nested source proof should stay on Proof");
    assert_eq!(
        original_flat_units, 1,
        "nested source proof split its Proof"
    );

    let (expanded, expansion_flat_units) = proof::count_flat_proof_units(|| {
        {
            {
                expand_c0_tactic_source_at(
                    click_source,
                    &[("nested.c", c_source)],
                    position.line,
                    position.column,
                )
            }
        }
    });
    let expanded = expanded.expect("selected nested-branch simp should expand");
    assert_eq!(expansion_flat_units, 1, "nested expansion split its Proof");

    assert_eq!(expanded.matches("simp();").count(), 2);
    let (reverified, reverify_flat_units) =
        proof::count_flat_proof_units(|| verify_c0_sources(&expanded, &[("nested.c", c_source)]));
    reverified.expect("sibling proof cases must not steal the deferred capture");
    assert_eq!(
        reverify_flat_units, 1,
        "rewritten nested proof split its Proof"
    );

    let leading = "if x >= 0 {\n            step();";
    let leading_offset = click_source
        .find(leading)
        .map(|start| start + leading.rfind("step").unwrap())
        .expect("outer then leading step should be present");
    let leading_position = position_at_offset(click_source, leading_offset);
    let (leading_expanded, leading_flat_units) = proof::count_flat_proof_units(|| {
        {
            {
                expand_c0_tactic_source_at(
                    click_source,
                    &[("nested.c", c_source)],
                    leading_position.line,
                    leading_position.column,
                )
            }
        }
    });
    let leading_expanded = leading_expanded.expect("leading smart branch step should expand");
    assert_eq!(leading_flat_units, 1, "leading expansion split its Proof");

    assert!(
        leading_expanded.contains("step();"),
        "leading smart step did not extract its checked operation: {leading_expanded}"
    );
    let (leading_reverified, _) = proof::count_flat_proof_units(|| {
        verify_c0_sources(&leading_expanded, &[("nested.c", c_source)])
    });
    leading_reverified.expect("expanded leading branch step should reverify");
}

#[test]
fn expanded_symbolic_range_propositions_use_parser_syntax() {
    let c_source = "int32 identity(int32 x, int32 n) { return x; }";
    let click_source = r#"verifying "identity.c";
int32 identity(int32 x, int32 n) {
    requires (0..n).any(|k| { k == x });
    ensures same_any: (0..n).any(|k| { k == x }) by auto;
}"#;
    let offset = click_source.find("auto").expect("auto should be present");
    let position = position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("identity.c", c_source)],
        position.line,
        position.column,
    )
    .expect("symbolic range proposition should expand");

    assert!(expanded.contains("(0..n).any(|k| { k == x })"));
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("printed symbolic range proposition should re-verify");
}

#[test]
fn expands_single_smart_and_default_function_proofs_by_source_location() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let smart = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x by { execute(); simp(); }
}
"#;
    let smart_position = position_at_offset(smart, smart.find("simp").unwrap());
    let smart_expanded = expand_c0_tactic_source_at(
        smart,
        &[("identity.c", c_source)],
        smart_position.line,
        smart_position.column,
    )
    .expect("single smart proof should expand as a whole proof");
    assert!(smart_expanded.contains("execute();"));
    assert!(!smart_expanded.contains("simp();"));
    verify_c0_sources(&smart_expanded, &[("identity.c", c_source)]).unwrap();

    let implicit = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
}
"#;
    let implicit_position = position_at_offset(implicit, implicit.find("ensures").unwrap());
    let implicit_expanded = expand_c0_tactic_source_at(
        implicit,
        &[("identity.c", c_source)],
        implicit_position.line,
        implicit_position.column,
    )
    .expect("default proof should expand from its clause coordinate");
    assert!(implicit_expanded.contains("ensures result == x by {"));
    verify_c0_sources(&implicit_expanded, &[("identity.c", c_source)]).unwrap();
}

#[test]
fn whole_function_proof_expansion_skips_unrelated_broken_proofs() {
    let good_c = "int32 good(int32 x) { return x; }";
    let bad_c = "int32 bad(int32 x) { return x; }";
    let click_source = r#"verifying "good.c";
verifying "bad.c";
int32 good(int32 x) {
    ensures result == x;
}
int32 bad(int32 x) {
    ensures result == x + 1 by simp;
}
"#;
    let sources = [("good.c", good_c), ("bad.c", bad_c)];
    verify_c0_sources(click_source, &sources)
        .expect_err("the unrelated bad proof should fail complete verification");
    let selected = position_at_offset(click_source, click_source.find("ensures").unwrap());

    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, selected.line, selected.column)
            .expect("whole-proof expansion should verify only the selected function");

    assert!(expanded.contains("ensures result == x by {"));
    verify_c0_sources_at(&expanded, &sources, selected.line, selected.column)
        .expect("the expanded selected function should verify independently");
}

#[test]
fn partial_tactic_expansion_skips_unrelated_broken_proofs() {
    let good_c = "int32 good(int32 x) { return x; }";
    let bad_c = "int32 bad(int32 x) { return x; }";
    let click_source = r#"verifying "good.c";
verifying "bad.c";
int32 good(int32 x) {
    ensures result == x by { execute(); simp(); }
}
int32 bad(int32 x) {
    ensures result == x + 1 by simp;
}
"#;
    let sources = [("good.c", good_c), ("bad.c", bad_c)];
    verify_c0_sources(click_source, &sources)
        .expect_err("the unrelated bad proof should fail complete verification");
    let selected_offset = click_source.find("execute();").unwrap();
    let selected = position_at_offset(click_source, selected_offset);

    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, selected.line, selected.column)
            .expect("partial expansion should verify only the selected function");

    assert_ne!(expanded, click_source);
    assert_eq!(
        &expanded[..selected_offset],
        &click_source[..selected_offset]
    );
    let unselected_suffix = &click_source[selected_offset + "execute();".len()..];
    assert!(expanded.ends_with(unselected_suffix));
    let relocated = c0_tactic_source_position(&expanded, &sources, "good.ensures_0", 0).unwrap();
    verify_c0_sources_at(&expanded, &sources, relocated.line, relocated.column)
        .expect("the expanded selected function should verify independently");
    verify_c0_sources(&expanded, &sources)
        .expect_err("whole-file verification should still see the unrelated failure");
}

#[test]
fn tactic_expansion_does_not_select_a_broken_callee_implementation() {
    let callee_c = "int32 callee(int32 x) { return x + 1; }";
    let caller_c = "int32 caller(int32 x) { int32 result; result = callee(x); return result; }";
    let click_source = r#"verifying "callee.c";
verifying "caller.c";
int32 callee(int32 x) {
    ensures result == x;
} by { execute(); simp(); }
int32 caller(int32 x) {
    ensures result == x;
} by { execute(); simp(); }
"#;
    let sources = [("callee.c", callee_c), ("caller.c", caller_c)];
    let selected = position_at_offset(click_source, click_source.rfind("execute();").unwrap());
    verify_c0_sources_at(click_source, &sources, selected.line, selected.column)
        .expect("the selected caller should verify under the callee interface");

    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, selected.line, selected.column)
            .expect("the selected caller expansion should assume the callee contract");
    let relocated = c0_tactic_source_position(&expanded, &sources, "caller.ensures_0", 0).unwrap();
    verify_c0_sources_at(&expanded, &sources, relocated.line, relocated.column)
        .expect("the expanded caller should verify under the callee interface");
    let error = verify_c0_sources(&expanded, &sources)
        .expect_err("whole-file verification must still reject the callee proof");
    assert!(error.message().contains("callee.contract"));
}

#[test]
fn expands_selected_tactics_in_branched_execution_by_path() {
    let c_source = r#"int32 write_selected(int32 p[2], int32 flag) {
    if (flag) {
        p[0] = 1;
        return 0;
    } else {
        p[1] = 1;
        return 1;
    }
}"#;
    let click_source = r#"verifying "write_selected.c";
int32 write_selected(int32 p[2], int32 flag) {
    consumes p[0..2];
    ensures result == 0 or result == 1;
} by {
    execute();
    if result == 0 {
        have result + 1 == 1 by simp;
    } else {
        have result - 1 == 0 by simp;
    }
    simp();
}
"#;
    let sources = [("write_selected.c", c_source)];
    let verified = verify_c0_sources(click_source, &sources);
    verified.expect("branched baseline should verify");
    for (selected_text, selected_smart) in [
        ("have result + 1", "have result + 1 == 1 by simp"),
        ("have result - 1", "have result - 1 == 0 by simp"),
    ] {
        let selected_offset = click_source.find(selected_text).unwrap();
        let selected = position_at_offset(click_source, selected_offset);

        let expanded =
            expand_c0_tactic_source_at(click_source, &sources, selected.line, selected.column)
                .expect("one branch's smart have should expand by its execution path");

        assert!(!expanded.contains(selected_smart));
        assert!(expanded.contains("if result == 0"));
        verify_c0_sources(&expanded, &sources)
            .expect("path-aligned branch expansion should check as a complete proof");
    }
}

#[test]
fn pure_theorem_expansion_is_certificate_backed_and_idempotent() {
    let source = r#"theorem incremented_zero_is_one(before: int32, after: int32) {
    requires before == 0;
    requires after == before + 1;
    ensures after == 1 by {
        rewrite(after == before + 1);
        rewrite(before == 0);
        simp();
    }
}
"#;
    let expanded_once = expand_pure_theorem_source(source, &[], "incremented_zero_is_one", 0)
        .expect("smart theorem script should expand");
    let expanded_twice =
        expand_pure_theorem_source(&expanded_once, &[], "incremented_zero_is_one", 0)
            .expect("expanded theorem certificate should expand again");

    assert!(!expanded_once.contains("simp"));
    assert_eq!(expanded_once, expanded_twice);
    let verified =
        verify_click_theorems(&expanded_once).expect("expanded theorem should re-verify");
    verified[0]
        .proof_certificate()
        .expect("expanded theorem should retain a surface certificate");
}

#[test]
fn contract_refinement_theorem_expands_with_its_concrete_c_environment() {
    let c_source = r#"void set_one_if_active(int32 active, int32* cell) {
    if (active != 0) {
        cell[0] = 1;
    }
}"#;
    let click_source = r#"
resource optional_cell(active: int32, cell: int32*) {
    if active != 0 {
        owns cell[0..1];
    }
}

verifying "set_one.c";

contract void MakePositive(int32 active, int32* cell) {
    owns optional_cell(active, cell);
    ensures active != 0 implies cell[0] > 0;
}

void set_one_if_active(int32 active, int32* cell) {
    owns optional_cell(active, cell);
    ensures active != 0 implies cell[0] == 1;
} by {
    if active != 0 {
        unfold(optional_cell(active, cell));
        execute();
        fold(optional_cell(active, cell));
        simp();
    } else {
        unfold(optional_cell(active, cell));
        execute();
        fold(optional_cell(active, cell));
        simp();
    }
}

theorem set_one_is_make_positive() {
    ensures MakePositive(&set_one_if_active) by {
        unfold(MakePositive);
        if active != 0 {
            simp();
        } else {
            simp();
        }
    }
}
"#;
    let sources = [("set_one.c", c_source)];

    let expanded =
        expand_pure_theorem_source(click_source, &sources, "set_one_is_make_positive", 0)
            .expect("contract-refinement theorem should expand with its concrete target");
    let theorem = &expanded[expanded
        .find("theorem set_one_is_make_positive")
        .expect("expanded source should retain the theorem")..];
    assert!(theorem.contains("intro();"), "{theorem}");
    assert!(theorem.contains("extract("), "{theorem}");
    assert!(!theorem.contains("simp();"), "{theorem}");
    verify_c0_sources(&expanded, &sources)
        .expect("expanded contract-refinement theorem should re-verify with its C target");
}

#[test]
fn pure_mixed_linear_smart_script_expands_the_retained_proof_object_path() {
    let source = r#"
        theorem required(x: int32) {
            requires x >= 0;
            ensures x >= 0 by auto;
        }

        theorem applied_then_simp(x: int32) {
            requires (x >= 0) and (x <= 10);
            ensures (x >= 0) and (x >= 0) by {
                extract(x >= 0);
                apply(required(x));
                simp();
            }
        }
    "#;
    let expanded = expand_pure_theorem_source(source, &[], "applied_then_simp", 0)
        .expect("the checked pure theorem path should expand");
    let selected = &expanded[expanded
        .find("theorem applied_then_simp")
        .expect("expanded source should retain the selected theorem")..];
    assert!(
        selected.contains("apply(required(x)) using {"),
        "{selected}"
    );
    assert!(selected.contains("x >= 0;"), "{selected}");
    assert!(selected.contains("extract(x >= 0);"), "{selected}");
    assert!(selected.contains("assumption();"), "{selected}");
    assert!(!selected.contains("apply(required(x));"), "{selected}");
    assert!(!selected.contains("simp();"), "{selected}");
    verify_click_theorems(&expanded)
        .expect("the serialized pure theorem certificate should independently reverify");
}

#[test]
fn pure_branch_local_apply_expands_the_retained_proof_object_paths() {
    let source = r#"
        theorem equality_case(x: int32) {
            requires x == 0;
            ensures x == 0 or not (x == 0) by {
                assumption();
            }
        }

        theorem inequality_case(x: int32) {
            requires not (x == 0);
            ensures x == 0 or not (x == 0) by {
                assumption();
            }
        }

        theorem branch_apply(x: int32) {
            ensures x == 0 or not (x == 0) by {
                if x == 0 {
                    apply(equality_case(x));
                    simp();
                } else {
                    apply(inequality_case(x));
                    simp();
                }
            }
        }
    "#;
    let expanded = expand_pure_theorem_source(source, &[], "branch_apply", 0)
        .expect("the checked branch-local theorem paths should expand");
    let selected = &expanded[expanded
        .find("theorem branch_apply")
        .expect("expanded source should retain the selected theorem")..];
    assert!(
        selected.contains("apply(equality_case(x)) using {"),
        "{selected}"
    );
    assert!(
        selected.contains("apply(inequality_case(x)) using {"),
        "{selected}"
    );
    assert!(!selected.contains("simp();"), "{selected}");
    verify_click_theorems(&expanded)
        .expect("the serialized branch-local certificates should independently reverify");
}

#[test]
fn pure_nested_have_branch_apply_expands_the_retained_proof_object_scope() {
    let source = r#"
        theorem equality_case_nested(x: int32) {
            requires x == 0;
            ensures x == 0 or not (x == 0) by {
                assumption();
            }
        }

        theorem inequality_case_nested(x: int32) {
            requires not (x == 0);
            ensures x == 0 or not (x == 0) by {
                assumption();
            }
        }

        theorem nested_branch_apply(x: int32) {
            ensures x == 0 or not (x == 0) by {
                have x == 0 or not (x == 0) by {
                    if x == 0 {
                        apply(equality_case_nested(x));
                        simp();
                    } else {
                        apply(inequality_case_nested(x));
                        simp();
                    }
                }
                assumption();
            }
        }
    "#;
    let expanded = expand_pure_theorem_source(source, &[], "nested_branch_apply", 0)
        .expect("the checked nested branch path should expand");
    let selected = &expanded[expanded
        .find("theorem nested_branch_apply")
        .expect("expanded source should retain the selected theorem")..];
    assert!(
        selected.contains("have x == 0 or") && selected.contains("if x == 0"),
        "{selected}"
    );
    assert!(
        selected.contains("apply(equality_case_nested(x)) using {")
            && selected.contains("apply(inequality_case_nested(x)) using {"),
        "{selected}"
    );
    assert!(
        !selected.contains("apply(equality_case_nested(x));")
            && !selected.contains("apply(inequality_case_nested(x));"),
        "{selected}"
    );
    assert!(!selected.contains("simp();"), "{selected}");
    verify_click_theorems(&expanded)
        .expect("the serialized nested pure branch should independently reverify");
}

/// An `extern` contract is assumed. Its clauses have no proof, so the
/// implicit `auto` of an unproved clause is not a site: `click audit` used to
/// list one per clause and then fail to expand it, reporting that the
/// function `has no verified ensures clause`.
#[test]
fn smart_inventory_skips_assumed_extern_contracts() {
    let c_source = "int32 child(int32 x);\nint32 parent(int32 x) { return child(x); }\n";
    let source = r#"
verifying "calls.c";

extern int32 child(int32 x) {
    requires x >= 0;
    ensures result == x;
}

int32 parent(int32 x) {
    requires x >= 0;
    ensures result == x by auto;
}
"#;
    let c_sources = [("calls.c", c_source)];
    verify_c0_sources(source, &c_sources)
        .expect("the caller verifies against the assumed contract");
    let sites = c0_smart_tactic_source_sites(source, &c_sources).unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.claim_label.as_str())
            .collect::<Vec<_>>(),
        ["parent.ensures_0"]
    );
}

#[test]
fn smart_inventory_does_not_invent_auto_sites_for_kernel_axiom_declarations() {
    let source = r#"
theorem int32_le_antisymmetric(left: int32, right: int32) {
    requires left <= right;
    requires right <= left;
    ensures left == right;
}

theorem ordinary(x: int32) {
    ensures x == x by { simp(); }
}
"#;
    verify_click_theorems_with_c_sources(source, &[]).unwrap();
    let sites = c0_smart_tactic_source_sites(source, &[]).unwrap();
    assert_eq!(sites.len(), 1);
    assert_eq!(sites[0].claim_label, "ordinary.ensures_0");
    assert_eq!(sites[0].tactic_name, "simp");
    assert!(
        verify_click_theorems_with_c_sources(
            &source.replace("ensures left == right", "ensures left != right"),
            &[]
        )
        .is_err(),
        "kernel axiom declarations must still be checked"
    );
}

#[test]
fn smart_inventory_keeps_refinement_proofs_named_like_arithmetic_axioms() {
    let source = r#"
contract int32 Identity(int32 x) { ensures result == x; }
theorem int32_le_antisymmetric() {
    ensures Identity(&identity) by { unfold(Identity); simp(); }
}
"#;
    let sites = c0_smart_tactic_source_sites(source, &[]).unwrap();
    assert_eq!(sites.len(), 1);
    assert_eq!(sites[0].claim_label, "int32_le_antisymmetric.ensures_0");
    assert_eq!(sites[0].tactic_name, "simp");
}

#[test]
fn builtin_nat_integer_laws_expand_and_reject_invalid_conversions() {
    for (parameters, requirements, goal, application) in [
        ("", "", "to_integer(Nat::Zero) == 0", "nat_integer_zero()"),
        (
            "n: Nat",
            "",
            "to_integer(Nat::Succ(n)) == to_integer(n) + 1",
            "nat_integer_succ(n)",
        ),
        (
            "n: Nat",
            "",
            "to_integer(n) >= 0",
            "nat_integer_nonnegative(n)",
        ),
        (
            "n: Nat",
            "",
            "to_nat(to_integer(n)) == n",
            "nat_integer_round_trip(n)",
        ),
        (
            "z: Integer",
            "requires z >= 0;",
            "to_integer(to_nat(z)) == z",
            "integer_nat_round_trip(z)",
        ),
        ("", "", "to_nat(0) == Nat::Zero", "integer_to_nat_zero()"),
    ] {
        let source = format!(
            "theorem client({parameters}) {{ {requirements} ensures {goal} by {{ apply({application}); }} }}"
        );
        verify_c0_sources(&source, &[])
            .unwrap_or_else(|error| panic!("{source}\n{}", error.message()));
        let expanded = expand_c0_claim_source_by_label(&source, &[], "client.ensures_0").unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
    }
    for source in [
        "theorem bad(z: Integer) { ensures to_integer(to_nat(z)) == z by { apply(integer_nat_round_trip(z)); } }",
        "theorem bad() { ensures to_nat(-1) == to_nat(-1) by normalize; }",
        "theorem bad(x: int32) { ensures to_nat(x) == to_nat(x) by normalize; }",
        "theorem bad() { ensures to_integer(Nat::Zero) == 1 by { apply(nat_integer_zero()); } }",
        "theorem bad() { ensures to_nat() == Nat::Zero by normalize; }",
        "theorem bad(z: Integer) { requires z >= 0; ensures to_nat(z, z) == to_nat(z) by normalize; }",
    ] {
        assert!(verify_c0_sources(source, &[]).is_err(), "{source}");
    }
}

#[test]
fn nat_addition_agrees_with_integer_addition_and_rechecks_expansion() {
    let source = "theorem client(a: Nat, b: Nat) { ensures to_integer(nat_add(a, b)) == to_integer(a) + to_integer(b) by { apply(nat_integer_add(a, b)); } }";
    verify_c0_sources(source, &[]).unwrap();
    let expanded = expand_c0_claim_source_by_label(source, &[], "client.ensures_0").unwrap();
    verify_c0_sources(&expanded, &[]).unwrap();
    assert!(
        verify_c0_sources(
            &source.replace("+ to_integer(b)", "+ to_integer(b) + 1"),
            &[]
        )
        .is_err()
    );
}

#[test]
fn signed_to_unsigned_interval_comparisons_expand_and_recheck_both_sides() {
    for goal in ["1u32 <= ((uint32)x)", "((uint32)x) <= 4u32"] {
        let source = format!(
            "theorem cast_bound(x: int32) {{ requires 0 < x; requires x <= 4; ensures {goal} by {{ arithmetic() using {{ 0 < x; x <= 4; }} }} }}"
        );
        verify_c0_sources(&source, &[]).unwrap();
        let expanded =
            expand_c0_claim_source_by_label(&source, &[], "cast_bound.ensures_0").unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
        assert!(verify_c0_sources(&source.replace(goal, "5u32 <= ((uint32)x)"), &[]).is_err());
    }
}

#[test]
fn arithmetic_certificates_accept_checked_mixed_atoms_without_erasing_domains() {
    for (parameters, requirements, term) in [
        ("x: int32", "", "to_integer(x)"),
        ("x: int32", "requires defined(x + 1);", "to_integer(x + 1)"),
        ("x: int32", "requires defined(x + 1);", "f(x + 1)"),
        ("n: Nat", "", "to_integer(n)"),
    ] {
        let source = format!(
            "function f(x: int32) -> Integer {{ to_integer(x) }} theorem client({parameters}) {{ {requirements} ensures {term} == {term} by {{ arithmetic_certificate {{ trivial => {term} == {term}; conclusion 0; }} }} }}"
        );
        verify_c0_sources(&source, &[])
            .unwrap_or_else(|error| panic!("{source}\n{}", error.message()));
        if !requirements.is_empty() {
            assert!(verify_c0_sources(&source.replace(requirements, ""), &[]).is_err());
        }
    }
}

#[test]
fn arithmetic_certificate_mixed_atom_lowering_scales_with_selected_inputs() {
    let mut work = Vec::new();
    for width in [8, 16, 32, 64] {
        let mut parameters = vec!["x: int32".to_string()];
        parameters.extend((0..width).map(|i| format!("unused{i}: int32")));
        let nodes = "trivial => to_integer(x) == to_integer(x);\n".repeat(width);
        let source = format!(
            "theorem selected({}) {{ ensures to_integer(x) == to_integer(x) by {{ arithmetic_certificate {{ {nodes} conclusion 0; }} }} }}",
            parameters.join(", ")
        );
        let (result, measured) =
            crate::instrumentation::measure_deterministic_work(|| verify_c0_sources(&source, &[]));
        result.unwrap();
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= 3 * pair[0],
            "mixed certificate lowering grew superlinearly: {work:?}"
        );
    }
}

/// `source_tactic_width` numbers the tactics inside a proof `cases` and a call
/// `outcomes` block, so the site inventory, the source span list, and the
/// nested-proof test must walk those arms too. Before they did, a smart tactic
/// inside either block was missing from the inventory, and the span list fell
/// out of step with the numbering: `cases` read as two tactics, so every
/// location in or after the block failed to resolve ("source location does
/// not select a smart tactic").
#[test]
fn smart_sites_inside_and_after_cases_and_outcomes_resolve_to_their_source() {
    let source = r#"
theorem pick_nonzero(r: int32) {
    requires r == 18 or r == -1;
    ensures r != 0 by {
        cases {
            r == 18 => {
                have r > 0 by { simp(); }
            }
            r == -1 => {
                have r < 0 by { simp(); }
            }
        }
        simp();
    }
}
"#;
    let sites = c0_smart_tactic_source_sites(source, &[]).expect("cases sites are indexed");
    let indexes = sites
        .iter()
        .map(|site| (site.source_index, site.tactic_name.as_str()))
        .collect::<Vec<_>>();
    assert_eq!(
        indexes,
        vec![(1, "have"), (2, "have"), (3, "simp")],
        "{sites:?}"
    );
    let final_simp = "simp();\n    }\n}";
    for (index, needle) in [(1, "have r > 0"), (2, "have r < 0"), (3, final_simp)] {
        let position = c0_tactic_source_position(source, &[], "pick_nonzero.ensures_0", index)
            .unwrap_or_else(|error| panic!("site {index} has no source position: {error:?}"));
        assert_eq!(
            position,
            position_at_offset(source, source.find(needle).unwrap()),
            "site {index}"
        );
    }
    let after = position_at_offset(source, source.find(final_simp).unwrap());
    let expanded = expand_c0_tactic_source_at(source, &[], after.line, after.column)
        .expect("the smart tactic after `cases` expands");
    verify_c0_sources(&expanded, &[]).expect("the expanded `cases` proof re-verifies");

    let c_source =
        "int32 helper(int32 x) { return x; }\nint32 client(int32 x) { return helper(x); }\n";
    let outcomes = r#"verifying "outcomes_sites.c";
int32 client(int32 x) {
    ensures result == x;
} by {
    step();
    outcomes {
        returned => {
            simp();
        }
        threw => {
            simp();
        }
    }
    simp();
}
"#;
    let c_sources = [("outcomes_sites.c", c_source)];
    let sites =
        c0_smart_tactic_source_sites(outcomes, &c_sources).expect("outcomes sites are indexed");
    let indexes = sites
        .iter()
        .map(|site| (site.source_index, site.tactic_name.as_str()))
        .collect::<Vec<_>>();
    assert_eq!(
        indexes,
        vec![(2, "simp"), (3, "simp"), (4, "simp")],
        "{sites:?}"
    );
    for (index, needle) in [
        (2, "simp();\n        }\n        threw"),
        (3, "simp();\n        }\n    }"),
        (4, "simp();\n}"),
    ] {
        let position = c0_tactic_source_position(outcomes, &c_sources, "client.contract", index)
            .unwrap_or_else(|error| panic!("site {index} has no source position: {error:?}"));
        assert_eq!(
            position,
            position_at_offset(outcomes, outcomes.find(needle).unwrap()),
            "site {index}"
        );
    }
}

#[test]
fn specification_pointer_load_equality_expands_to_checked_normalization() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/egraph_resource_pointer_load_alias.md");
    let fixture = crate::cli::read_mdtest(&path).expect("pointer-load fixture");
    let source = fixture.click_source.as_deref().expect("Click source");
    let sources = crate::cli::source_refs(&fixture.c_sources);
    verify_c0_sources(source, &sources).expect("original specification equality verifies");
    let equality = source
        .find("have p->next == id->next")
        .expect("load equality claim");
    let tactic = equality + source[equality..].find("simp();").expect("equality tactic");
    let position = position_at_offset(source, tactic);
    let expanded = expand_c0_tactic_source_at(source, &sources, position.line, position.column)
        .expect("logical load equality should expand");
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(
        !expanded.contains("MemoryLoad") && !expanded.contains("__click_"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &sources).expect("expanded normalization independently verifies");
}

#[test]
fn recursive_child_alias_fold_expands_and_rechecks_without_load_claims() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/egraph_recursive_child_alias.md");
    let fixture = crate::cli::read_mdtest(&path).expect("recursive child fixture");
    let source = fixture.click_source.as_deref().expect("Click source");
    let sources = crate::cli::source_refs(&fixture.c_sources);
    verify_c0_sources(source, &sources).expect("unfold/refold through an equal address");
    let expanded = expand_c0_claim_source_by_label(source, &sources, "roundtrip.contract")
        .expect("recursive child fold should expand");
    assert!(
        !expanded.contains("MemoryLoad") && !expanded.contains("__click_"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &sources).expect("expanded fold independently verifies");
}

#[test]
fn pointer_read_single_store_normalization_expands_and_rechecks() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/egraph_pointer_read_single_store.md");
    let fixture = crate::cli::read_mdtest(&path).expect("single-store fixture");
    let source = fixture.click_source.as_deref().expect("Click source");
    let sources = crate::cli::source_refs(&fixture.c_sources);
    verify_c0_sources(source, &sources).expect("ordinary pointer claim verifies");
    let expanded = expand_c0_claim_source_by_label(source, &sources, "touch.contract")
        .expect("single-store pointer claim expands");
    verify_c0_sources(&expanded, &sources).expect("expanded claim independently rechecks");
    let mut changed_sources = fixture.c_sources.clone();
    changed_sources[0].1 = changed_sources[0].1.replace("p->tag = 1", "p->left = 0");
    let changed = crate::cli::source_refs(&changed_sources);
    assert!(
        verify_c0_sources(&expanded, &changed).is_err(),
        "a write to the pointer field cannot reuse sibling-write equality"
    );
}

#[test]
fn recursive_child_sibling_write_fold_expands_and_rechecks() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/egraph_recursive_child_sibling_write.md");
    let fixture = crate::cli::read_mdtest(&path).expect("sibling-write fixture");
    let source = fixture.click_source.as_deref().expect("Click source");
    let sources = crate::cli::source_refs(&fixture.c_sources);
    verify_c0_sources(source, &sources).expect("unfold/write/refold verifies");
    let expanded = expand_c0_claim_source_by_label(source, &sources, "roundtrip.contract")
        .expect("sibling-write fold expands");
    verify_c0_sources(&expanded, &sources).expect("expanded sibling-write fold rechecks");
    let mut changed_sources = fixture.c_sources.clone();
    changed_sources[0].1 = changed_sources[0].1.replace("p->tag = 1", "p->left = 0");
    assert!(verify_c0_sources(&expanded, &crate::cli::source_refs(&changed_sources)).is_err());
}

/// A declaration is a name followed by `(` outside every brace. A use of the
/// same name inside a body, even an earlier one, is not the declaration.
#[test]
fn a_declaration_position_skips_uses_inside_bodies() {
    let source = "contract void Shape(int32* p) {\n    owns p[0..1];\n}\n\ntheorem uses() {\n    ensures Shape(&f) by { simp(); }\n}\n\n  int32 f(int32* p) {\n    ensures result == 0;\n}\n";
    let position =
        |name| click_declaration_source_position(source, name).map(|at| (at.line, at.column));
    assert_eq!(position("Shape"), Some((1, 1)));
    assert_eq!(position("uses"), Some((5, 1)));
    assert_eq!(position("f"), Some((9, 3)));
    assert_eq!(position("missing"), None);
}

#[test]
fn trace_source_index_preserves_nested_locations_and_containment() {
    let source = "# αβ UTF-8\nby {\n  have true by { open(resource) { assumption(); } }\n  if true { normalize(); } else { simp(); }\n  cases { true => { step(); } false => { normalize(); } }\n  both { normalize(); } and { simp(); }\n  outcomes { threw => { step(); } returned => { simp(); } }\n  branch ensuring { true } then { step(); } else { simp(); }\n  normalize();\n}\n";
    let index = ProofSourceIndex::new(source).unwrap();
    for line in 1..=10 {
        for position in tactic_starts_on_line(source, line).unwrap() {
            assert_eq!(
                index.line_has_multiple_starts(&position).unwrap(),
                tactic_line_has_multiple_starts(source, &position).unwrap(),
                "{position:?}"
            );
            for target_line in 1..=10 {
                for target in tactic_starts_on_line(source, target_line).unwrap() {
                    assert_eq!(
                        index.arm_containing(&position, &target).unwrap(),
                        tactic_arm_containing_position(source, &position, &target).unwrap()
                    );
                    assert_eq!(
                        index.have_body_contains(&position, &target).unwrap(),
                        tactic_have_body_contains_position(source, &position, &target).unwrap()
                    );
                }
            }
        }
    }
    let have = position_at_offset(source, source.find("have").unwrap());
    assert_eq!(
        index.nested_position(&have, &[0, 0]).unwrap(),
        SourcePosition::new(3, 35)
    );
    for (kind, path) in [
        ("if", vec![1, 0]),
        ("cases", vec![1, 0]),
        ("both", vec![1, 0]),
    ] {
        let outer = position_at_offset(source, source.find(kind).unwrap());
        assert_eq!(
            index.nested_position(&outer, &path).unwrap(),
            nested_tactic_source_position(source, &outer, &path).unwrap()
        );
    }
}

#[test]
fn trace_source_index_scales_with_sites_and_unrelated_source() {
    let mut total = Vec::new();
    let mut query_work = Vec::new();
    for size in [16, 64, 256] {
        let source = format!(
            "{}\nby {{ {} }}",
            "# αβ unrelated\n".repeat(size * 4),
            "have true by { normalize(); } ".repeat(size)
        );
        let positions: Vec<_> = source
            .match_indices("have")
            .map(|(offset, _)| position_at_offset(&source, offset))
            .collect();
        let ((index, locations), build_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                let index = ProofSourceIndex::new(&source).unwrap();
                let locations: Vec<_> = positions
                    .iter()
                    .map(|p| index.nested_position(p, &[0]).unwrap())
                    .collect();
                (index, locations)
            });
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for (have, nested) in positions.iter().zip(&locations) {
                assert!(index.have_body_contains(have, nested).unwrap());
                assert!(index.line_has_multiple_starts(nested).unwrap());
                assert_eq!(index.nested_position(have, &[0]).unwrap(), *nested);
                assert!(index.nested_position(have, &[usize::MAX]).is_err());
                assert_eq!(index.arm_containing(have, nested).unwrap(), None);
            }
        });
        total.push(build_work + work);
        query_work.push(work);
        assert!(
            work <= size * 8,
            "queries must inspect only their paths: {work}"
        );
    }
    for pair in total.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{total:?}");
    }
    for pair in query_work.windows(2) {
        assert!(pair[1] <= pair[0] * 4, "{query_work:?}");
    }
    // A larger immutable container must not increase work per selected site.
    let query = |unrelated| {
        let source = format!(
            "{}by {{ have true by {{ normalize(); }} }}",
            "# unrelated αβ\n".repeat(unrelated)
        );
        let index = ProofSourceIndex::new(&source).unwrap();
        let have = position_at_offset(&source, source.find("have").unwrap());
        crate::instrumentation::measure_deterministic_work(|| {
            let nested = index.nested_position(&have, &[0]).unwrap();
            assert!(index.have_body_contains(&have, &nested).unwrap());
            index.line_has_multiple_starts(&nested).unwrap()
        })
        .1
    };
    assert_eq!(query(16), query(4096));
}

#[test]
fn trace_source_index_skips_nested_subtrees_during_construction() {
    let mut work = Vec::new();
    for depth in [16, 64, 256] {
        let source = format!(
            "by {{ {}normalize();{} }}",
            "have true by { ".repeat(depth),
            " }".repeat(depth)
        );
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            ProofSourceIndex::new(&source).unwrap()
        });
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 5,
            "nested blocks must skip already indexed subtrees: {work:?}"
        );
    }
}

#[test]
fn trace_source_index_preserves_unicode_and_implicit_proof_columns() {
    for source in [
        "/* αβ */ by { have true by normalize(); simp(); }",
        "/* αβ */ by { have true by { normalize(); } simp(); }",
    ] {
        let index = ProofSourceIndex::new(source).unwrap();
        let have = position_at_offset(source, source.find("have").unwrap());
        let child = index.nested_position(&have, &[0]).unwrap();
        assert_eq!(
            child,
            position_at_offset(source, source.find("normalize").unwrap())
        );
        assert_eq!(
            index.have_body_contains(&have, &child).unwrap(),
            tactic_have_body_contains_position(source, &have, &child).unwrap()
        );
        assert_eq!(
            index.line_has_multiple_starts(&have).unwrap(),
            tactic_line_has_multiple_starts(source, &have).unwrap()
        );
        assert_eq!(
            index.line_has_multiple_starts(&child).unwrap(),
            tactic_line_has_multiple_starts(source, &child).unwrap()
        );
    }
}

#[test]
fn trace_source_index_indexes_many_case_arms() {
    for size in [16, 64, 256] {
        let source = format!(
            "by {{ cases {{ {} }} }}",
            "true => { normalize(); } ".repeat(size)
        );
        let index = ProofSourceIndex::new(&source).unwrap();
        let cases = position_at_offset(&source, source.find("cases").unwrap());
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for arm in 0..size {
                let child = index.nested_position(&cases, &[arm, 0]).unwrap();
                assert_eq!(index.arm_containing(&cases, &child).unwrap(), Some(arm));
            }
        });
        assert!(
            work <= size * 12,
            "case targets must use indexed arm intervals: {work}"
        );
    }
}
