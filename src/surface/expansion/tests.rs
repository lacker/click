use super::*;

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
fn nat_to_integer_laws_expand_and_reject_wrong_successor() {
    let source = r#"
theorem nat_to_integer_client(n: Nat) {
    ensures nat_to_integer(Nat::Succ(n)) == nat_to_integer(n) + 1 by {
        apply(nat_to_integer_succ(n));
    }
}
"#;
    verify_c0_sources(source, &[]).expect("Nat conversion law verifies");
    let expanded = expand_c0_claim_source_by_label(source, &[], "nat_to_integer_client.ensures_0")
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
            },
            SmartTacticSourceSite {
                claim_label: "reflexive.ensures_0".to_string(),
                source_index: 2,
                tactic_name: "simp".to_string(),
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
        CProofClaim::Ensure(_) => find_claim_proof_span(&tokens, &function, claim)?,
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
        branch {
            ensuring {
                fact y >= 0;
                fact y < 2147483647;
            }
            then {
                step();
            }
            else {
                step();
            }
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
        branch {
            ensuring {
                fact y >= 0;
                fact y < 2147483647;
            }
            then {
                step();
            }
            else {
                step();
            }
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
        branch {
            then { step(); }
            else { step(); }
        }
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
        branch {
            then {
                step();
                simp();
            }
            else {}
        }
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
        branch {
            ensuring {
                fact y >= 0;
            }
            then {
                branch {
                    ensuring {
                        fact y >= 0;
                    }
                    then { step(); }
                    else { step(); }
                }
            }
            else { step(); }
        }
        step();
        simp();
    }
}
"#;
    let ((((verified, events), certificate_checks), context_exports), flat_units) =
        super::super::proof::count_flat_proof_units(|| {
            {
                super::super::proof::count_execution_context_exports(|| {
                    super::super::proof::count_source_certificate_checks(|| {
                        crate::instrumentation::collect(|| {
                            verify_c0_sources(click_source, &[("nested.c", c_source)])
                        })
                    })
                })
            }
        });
    let verified = verified.expect("nested end-of-arm interfaces should verify through Proof");
    assert_eq!(flat_units, 1, "the nested script should retain one Proof");
    assert_eq!(
        context_exports, 0,
        "nested verification must not export state"
    );
    assert_eq!(
        certificate_checks, 0,
        "nested verification must not check a certificate"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "nested_nonnegative.contract"
                    && name == "generated certificate validation"
        )),
        "nested end-of-arm interfaces must retain their checked Proof successors: {events:#?}"
    );
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
    let ((expanded, expansion_checks), expansion_exports) = {
        super::super::proof::count_execution_context_exports(|| {
            super::super::proof::count_source_certificate_checks(|| {
                expand_c0_tactic_source_at(
                    click_source,
                    &[("nested.c", c_source)],
                    position.line,
                    position.column,
                )
            })
        })
    };
    let expanded = expanded.expect("nested deferred simp should expand");
    assert_eq!(
        expansion_exports, 0,
        "nested expansion must not export state"
    );
    assert_eq!(
        expansion_checks, 0,
        "nested expansion must not check a certificate"
    );

    verify_c0_sources(&expanded, &[("nested.c", c_source)]).unwrap_or_else(|error| {
        panic!("nested deferred expansion should check:\n{error:?}\n{expanded}")
    });

    let inner_offset = click_source
        .find("                branch {")
        .expect("inner branch should exist")
        + 16;
    let inner_position = position_at_offset(click_source, inner_offset);
    let ((inner, inner_checks), inner_exports) = {
        super::super::proof::count_execution_context_exports(|| {
            super::super::proof::count_source_certificate_checks(|| {
                expand_c0_tactic_source_at(
                    click_source,
                    &[("nested.c", c_source)],
                    inner_position.line,
                    inner_position.column,
                )
            })
        })
    };
    let inner = inner.expect("the retained inner branch should expand");
    assert_eq!(
        inner_exports, 0,
        "inner branch expansion must not export state"
    );
    assert_eq!(
        inner_checks, 0,
        "inner branch expansion must not check a certificate"
    );
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

    assert!(expanded.contains("first"), "{expanded}");
    assert!(expanded.contains("second"), "{expanded}");
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
fn selected_tactic_requires_the_complete_function_dependency_closure() {
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

    let error =
        expand_top_level_tactic_for_test(click_source, &sources, "caller", CProofClaim::Grouped, 0)
            .expect_err("capture must reject an invalid callee used later in the proof unit");
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
        memory(object(owner)),
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
    requires loadable(p[0..n]);
    requires has_x: bytes_contains(p, 0, n, 'x');
    ensures bytes_contains(p, 0, n, 'x') by {
        execute();
        unfold(bytes_contains);
        choose(found from requirement has_x);
        witness(k = found);
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

    assert!(expanded.contains("bytes_contains(p, 0, n, 120u8)"));
    verify_c0_sources(&expanded, &[("contains.c", c_source)])
        .expect("printed uint8 literal should parse and re-verify");
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
    requires loadable(p[0..2]);
    consumes p[0..2];
    ensures sorted_pair(p) by {
        execute();
        unfold(sorted_pair);
        simp();
    }
}"#;
    let (expanded_execute, _events) = crate::instrumentation::collect(|| {
        expand_top_level_tactic_for_test(
            click_source,
            &[("compare_swap2.c", c_source)],
            "compare_swap2",
            CProofClaim::Ensure(0),
            0,
        )
    });
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
    let (expanded, _events) = crate::instrumentation::collect(|| {
        expand_c0_tactic_source_at(
            click_source,
            &[("compare_swap2.c", c_source)],
            position.line,
            position.column,
        )
    });
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
    let c_source = "int32 inspect(uint8 p[], int32 len) { return 0; }";
    let click_source = r#"verifying "inspect.c";
int32 inspect(uint8 p[], int32 len) {
    requires loadable(p[0..len + 1]);
    requires exact: cstr_len(p, len);
    ensures 0 <= len by {
        execute();
        apply(cstr_len_nonnegative(p, len));
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

    assert!(expanded.contains("apply(cstr_len_nonnegative(p, len)) using"));
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
    let position = c0_tactic_source_position(click_source, &sources, "set_then_read.ensures_1", 0)
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
    let ((verified, original_fallbacks), original_flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_explicit_linear_fallbacks(|| {
                    verify_c0_sources(click_source, &[("nested.c", c_source)])
                })
            }
        });
    verified.expect("nested source proof should stay on Proof");
    assert_eq!(
        original_flat_units, 1,
        "nested source proof split its Proof"
    );
    assert_eq!(original_fallbacks, 0, "nested source proof fell back");

    let ((expanded, expansion_fallbacks), expansion_flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_explicit_linear_fallbacks(|| {
                    expand_c0_tactic_source_at(
                        click_source,
                        &[("nested.c", c_source)],
                        position.line,
                        position.column,
                    )
                })
            }
        });
    let expanded = expanded.expect("selected nested-branch simp should expand");
    assert_eq!(expansion_flat_units, 1, "nested expansion split its Proof");
    assert_eq!(
        expansion_fallbacks, 0,
        "selected nested-branch expansion fell back from a checked operation"
    );

    assert_eq!(expanded.matches("simp();").count(), 2);
    let ((reverified, reverify_fallbacks), reverify_flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_explicit_linear_fallbacks(|| {
                    verify_c0_sources(&expanded, &[("nested.c", c_source)])
                })
            }
        });
    reverified.expect("sibling proof cases must not steal the deferred capture");
    assert_eq!(
        reverify_flat_units, 1,
        "rewritten nested proof split its Proof"
    );
    assert_eq!(
        reverify_fallbacks, 0,
        "rewritten nested-branch proof fell back from a checked operation"
    );

    let leading = "if x >= 0 {\n            step();";
    let leading_offset = click_source
        .find(leading)
        .map(|start| start + leading.rfind("step").unwrap())
        .expect("outer then leading step should be present");
    let leading_position = position_at_offset(click_source, leading_offset);
    let ((leading_expanded, leading_fallbacks), leading_flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_explicit_linear_fallbacks(|| {
                    expand_c0_tactic_source_at(
                        click_source,
                        &[("nested.c", c_source)],
                        leading_position.line,
                        leading_position.column,
                    )
                })
            }
        });
    let leading_expanded = leading_expanded.expect("leading smart branch step should expand");
    assert_eq!(leading_flat_units, 1, "leading expansion split its Proof");
    assert_eq!(leading_fallbacks, 0, "leading expansion fell back");
    assert!(
        leading_expanded.contains("step();"),
        "leading smart step did not extract its checked operation: {leading_expanded}"
    );
    let ((leading_reverified, leading_reverify_fallbacks), _) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_explicit_linear_fallbacks(|| {
                    verify_c0_sources(&leading_expanded, &[("nested.c", c_source)])
                })
            }
        });
    leading_reverified.expect("expanded leading branch step should reverify");
    assert_eq!(
        leading_reverify_fallbacks, 0,
        "expanded leading branch step fell back"
    );
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
fn tactic_expansion_reports_required_dependency_path() {
    let callee_c = "int32 callee(int32 x) { return x; }";
    let caller_c = "int32 caller(int32 x) { int32 result; result = callee(x); return result; }";
    let click_source = r#"verifying "callee.c";
verifying "caller.c";
int32 callee(int32 x) {
    ensures result == x + 1 by { execute(); simp(); }
}
int32 caller(int32 x) {
    ensures result == x by { execute(); simp(); }
}
"#;
    let sources = [("callee.c", callee_c), ("caller.c", caller_c)];
    let selected = position_at_offset(click_source, click_source.rfind("execute();").unwrap());

    let error = expand_c0_tactic_source_at(click_source, &sources, selected.line, selected.column)
        .expect_err("a broken required dependency must block expansion");

    assert!(
        error.message().contains("caller -> callee"),
        "{}",
        error.message()
    );
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
    let (verified, _events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
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
    assert!(selected.contains("split();"), "{selected}");
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
                left();
            }
        }

        theorem inequality_case(x: int32) {
            requires not (x == 0);
            ensures x == 0 or not (x == 0) by {
                right();
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
                left();
            }
        }

        theorem inequality_case_nested(x: int32) {
            requires not (x == 0);
            ensures x == 0 or not (x == 0) by {
                right();
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
