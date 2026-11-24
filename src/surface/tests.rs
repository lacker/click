use super::diagnostics::describe_contract_expression;
use super::*;
use crate::kernel::{AlgebraicValueType, int32};

// Semantic fixtures cold-check both the original and written output. Reuse the
// original certificate here instead of searching for that same proof again.
fn expand_checked_grouped_claim(
    source: &str,
    verified: &[VerifiedProgramTheorem],
    function: &str,
) -> Result<String, ClickError> {
    // An omitted proof of one claim is that claim's own proof.
    let grouped = expand_verified_function_claim_source_by_label(
        source,
        verified,
        &format!("{function}.contract"),
    )?;
    let single = || {
        expand_verified_function_claim_source_by_label(
            source,
            verified,
            &format!("{function}.ensures_0"),
        )
    };
    match grouped {
        Some(expanded) => Some(expanded),
        None => single()?,
    }
    .ok_or_else(|| {
        ClickError::new(format!(
            "checked claim for `{function}` is not declared in this source"
        ))
    })
}

/// Expands a function's whole proof: its grouped proof, or, when its one
/// claim's proof is omitted, that claim's implicit tail.
fn expand_function_proof_source(
    click_source: &str,
    c_sources: &[(&str, &str)],
    function: &str,
) -> Result<String, ClickError> {
    expand_c_claim_source(
        click_source,
        c_sources,
        function,
        ContractProofClaim::Grouped,
    )
    .or_else(|error| {
        if error.message().contains("has no source `by` clause") {
            // The first written ensure, by its label: an `owns` clause's
            // generated ensure comes first by index. A contract with no
            // written ensure proves that generated one.
            expand_c_claim_source_by_label(
                click_source,
                c_sources,
                &format!("{function}.ensures_0"),
            )
            .or_else(|_| {
                expand_c_claim_source(
                    click_source,
                    c_sources,
                    function,
                    ContractProofClaim::Ensure(0),
                )
            })
        } else {
            Err(error)
        }
    })
}

// Format every claim while its original verification tables are still live.
// The callers can then cold-check each independent output in turn.
fn expand_checked_grouped_claims<'a>(
    source: &str,
    verified: &[VerifiedProgramTheorem],
    functions: impl IntoIterator<Item = &'a str>,
) -> Vec<(&'a str, String)> {
    functions
        .into_iter()
        .map(|function| {
            let expanded = expand_checked_grouped_claim(source, verified, function)
                .unwrap_or_else(|error| panic!("{function}: {}", error.message()));
            (function, expanded)
        })
        .collect()
}

fn expand_checked_function_claim(
    source: &str,
    verified: &[VerifiedProgramTheorem],
    claim: &str,
) -> Result<String, ClickError> {
    expand_verified_function_claim_source_by_label(source, verified, claim)?.ok_or_else(|| {
        ClickError::new(format!(
            "checked function claim `{claim}` is not declared in this source"
        ))
    })
}

#[test]
fn pure_function_returns_check_all_scalar_result_leaves() {
    for source in [
        "function wrong(p: int32*) -> int32 { p }",
        "function wrong() -> int32* { 7 }",
        "function wrong(p: int32*, n: int32) -> int32 { if n == 0 { 0 } else { p } }",
        "spec enum Ptr { At(int32*) } function wrong(m: Ptr) -> int32 { match m { Ptr::At(p) => p, } }",
        "function wrong(p: int32*) -> int32 { let saved = p; saved }",
        "function wrong(p: int32*) -> Integer { p }",
        "spec enum Ptr { At(int32*) } function wrong(m: Ptr) -> Integer { match m { Ptr::At(p) => p, } }",
    ] {
        let error = parser::parse(source).unwrap_err();
        assert!(
            error.message().contains("function `wrong` returns"),
            "{error}"
        );
    }
}

#[test]
fn scalar_returns_keep_constructor_bound_algebraic_types() {
    parser::parse(
        "spec enum Color { Red, Black, } spec enum Tree { Empty, Node(Color, Tree, Tree), } function black(t: Tree) -> int32 { match t { Tree::Empty => 1, Tree::Node(c, l, r) => if c == Color::Black { 1 } else { 0 }, } }",
    ).unwrap();
    let error = parser::parse(
        "spec enum Color { Red, Black, } spec enum Other { Black, } spec enum Tree { Empty, Node(Color, Tree, Tree), } function wrong(t: Tree) -> int32 { match t { Tree::Empty => 1, Tree::Node(c, l, r) => if c == Other::Black { 1 } else { 0 }, } }",
    ).unwrap_err();
    assert!(
        error
            .message()
            .contains("comparison has types Color and Other in function `wrong`"),
        "{error}"
    );
}

#[test]
fn pure_function_returns_keep_null_and_numeric_conversions() {
    parser::parse(
        "function narrow(n: uint64) -> int32 { n as int32 } function null() -> int32* { 0 } function choose(p: int32*, n: int32) -> int32* { if n == 0 { 0 } else { p } } spec enum Ptr { Empty, At(int32*) } function get(m: Ptr) -> int32* { match m { Ptr::Empty => 0, Ptr::At(p) => p, } } function inc(n: Integer) -> Integer { n + 1 } function big() -> Integer { 999999999999999999999999999999 }",
    ).unwrap();
    parser::parse("function id<T>(x: T) -> T { x } function flag(x: Bool) -> Bool { id(x) }")
        .unwrap();
    // A narrowing return is written: it can change the value.
    let error = parser::parse("function narrow(n: uint64) -> int32 { n }").unwrap_err();
    assert!(
        error
            .message()
            .contains("returns int32, but its body can produce `n` of type uint64"),
        "{error}"
    );
}

#[test]
fn pure_function_return_types_cannot_be_forged_by_local_annotations() {
    for source in [
        "function wrong(p: int32*) -> int32 { let saved: int32 = p; saved }",
        "function wrong(p: int32*) -> Integer { let saved: Integer = p; saved }",
    ] {
        let error = parser::parse(source).unwrap_err();
        assert!(
            error.message().contains("let binding `saved` expects"),
            "{error}"
        );
    }
}

const GUARDED_CELL_SOURCE: &str = r#"verifying "read.c";
resource cell(p: int32*) {
    field value: int32;
    if p != 0 { owns p[0..1]; fact p[0] == value; }
}
int32 read(int32* p) {
    owns c: cell(p);
    ensures p == 0 or result == c.value;
    ensures c.value == old(c.value);
} by { BODY }
"#;

const GUARDED_CELL_C: &str = "int32 read(int32* p) { if (p == 0) return 0; return *p; }";

const RECURSIVE_CHILD_SOURCE: &str = r#"verifying "read.c";
spec enum Chain { End, More(int32, int32*, Chain) }
resource chain(p: int32*) {
    field model: Chain;
    match model {
        Chain::End => { fact p == 0; },
        Chain::More(value, next, rest) => {
            owns p[0..1];
            owns tail: chain(next);
            fact p[0] == value;
            fact tail.model == rest;
        },
    }
}
int32 read(int32* p, int32* next, int32 value) {
    owns root: chain(p);
    requires root.model == Chain::More(value, next, Chain::End);
    ensures result == value;
    ensures root.model == old(root.model);
} by { BODY }
"#;

#[test]
fn recursive_child_resources_round_trip_and_expand() {
    let c = [(
        "read.c",
        "int32 read(int32* p, int32* next, int32 value) { return *p; }",
    )];
    for body in [
        "let { tail: t } = unfold(root); unfold(t); step_until(function.exit); let t = fold(chain(next), { model: Chain::End }); let root = fold(chain(p), { model: old(root.model), tail: t }); close();",
        "let { tail: t } = unfold(root); have t.model == Chain::End by { close(); } unfold(t); let t = fold(chain(next), { model: Chain::End }); let root = fold(chain(p), { model: old(root.model), tail: t }); let { tail: t } = unfold(root); step_until(function.exit); let root = fold(chain(p), { model: old(root.model), tail: t }); close();",
    ] {
        let source = RECURSIVE_CHILD_SOURCE.replace("BODY", body);
        let verified = verify_c_sources(&source, &c).unwrap();
        verify_c_sources(
            &source.replace(
                &format!("by {{ {body} }}"),
                &verified[0].expanded_proof_source().unwrap(),
            ),
            &c,
        )
        .unwrap();
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn recursive_child_resources_independent_layers_own_memory_and_recheck() {
    let source = r#"verifying "middle.c";
        spec enum Nonempty { Last(int32), More(int32, int32*, Nonempty) }
        resource chain(p: int32*) {
            field model: Nonempty;
            match model {
                Nonempty::Last(value) => { owns p[0..1]; fact p[0] == value; },
                Nonempty::More(value, next, rest) => {
                    owns p[0..1]; fact p[0] == value;
                    owns tail: chain(next); fact tail.model == rest;
                },
            }
        }
        int32 middle(int32* p, int32* q, int32* r) {
            owns root: chain(p);
            requires root.model == Nonempty::More(7, q, Nonempty::More(8, r, Nonempty::Last(9)));
            ensures result == 8;
            ensures root.model == old(root.model);
        } by { BODY }
    "#;
    let body = "let { tail: t } = unfold(root); let { tail: u } = unfold(t); have u.model == Nonempty::Last(9) by { close(); } unfold(u); step_until(function.exit); let u = fold(chain(r), { model: Nonempty::Last(9) }); let t = fold(chain(q), { model: Nonempty::More(8, r, Nonempty::Last(9)), tail: u }); let root = fold(chain(p), { model: old(root.model), tail: t }); close();";
    let c = [(
        "middle.c",
        "int32 middle(int32* p, int32* q, int32* r) { return *q; }",
    )];
    let source = source.replace("BODY", body);
    let verified = verify_c_sources(&source, &c).unwrap();
    verify_c_sources(
        &source.replace(
            &format!("by {{ {body} }}"),
            &verified[0].expanded_proof_source().unwrap(),
        ),
        &c,
    )
    .unwrap();
    assert!(
        verify_c_sources(
            &source.replace(body, "let { tail: t } = unfold(root); step_until(function.exit); let root = fold(chain(p), { model: old(root.model), tail: t }); close();"),
            &c
        )
        .is_err()
    );
    assert!(verify_c_sources(&source.replace("result == 8", "result == 9"), &c).is_err());
}

#[test]
fn recursive_child_resources_do_not_capture_earlier_function_names() {
    let source = RECURSIVE_CHILD_SOURCE
        .replace(
            "BODY",
            "let { root: t } = unfold(root); unfold(t); step_until(function.exit); let t = fold(chain(next), { model: Chain::End }); let root = fold(chain(p), { model: old(root.model), root: t }); close();",
        )
        .replace("owns tail: chain(next);", "owns root: chain(next);")
        .replace("fact tail.model", "fact root.model");
    let declaration = source.find("resource chain").unwrap();
    let function = source.find("int32 read").unwrap();
    let reordered = format!(
        "{}{}{}",
        &source[..declaration],
        &source[function..],
        &source[declaration..function]
    );
    verify_c_sources(
        &reordered,
        &[(
            "read.c",
            "int32 read(int32* p, int32* next, int32 value) { return *p; }",
        )],
    )
    .unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn recursive_child_resources_reject_bad_lifetimes_and_folds() {
    let c = [(
        "read.c",
        "int32 read(int32* p, int32* next, int32 value) { return *p; }",
    )];
    for body in [
        "unfold(root.tail); step_until(function.exit); close();",
        "unfold(root); unfold(root.tail); step_until(function.exit); fold(root); close();",
        "unfold(root); unfold(root.tail); unfold(root.tail); step_until(function.exit); fold(root.tail); fold(root); close();",
        "unfold(root); step_until(function.exit); fold(root.tail); fold(root); close();",
        "unfold(root); step_until(function.exit); fold(root); unfold(root.tail); close();",
        "unfold(root); unfold(root.missing); step_until(function.exit); fold(root); close();",
        "unfold(root); unfold(root.tail.tail); step_until(function.exit); fold(root); close();",
        "let { tail: t } = unfold(root); unfold(root.tail); step_until(function.exit); close();",
        "let { tail: t } = unfold(root); unfold(root); step_until(function.exit); close();",
        "let { tail: t } = unfold(root); unfold(t); unfold(t); step_until(function.exit); close();",
        "let { tail: t } = unfold(root); unfold(t); step_until(function.exit); let root = fold(chain(p), { model: old(root.model), tail: t }); close();",
        "let { tail: t } = unfold(root); have root.model == old(root.model) by { close(); } step_until(function.exit); let root = fold(chain(p), { model: old(root.model), tail: t }); close();",
    ] {
        let source = RECURSIVE_CHILD_SOURCE.replace("BODY", body);
        assert!(verify_c_sources(&source, &c).is_err(), "accepted {body}");
    }
    let source = RECURSIVE_CHILD_SOURCE.replace("BODY", "let { tail: t } = unfold(root); step_until(function.exit); let root = fold(chain(p), { model: old(root.model), tail: t }); close();");
    verify_c_sources(&source, &c)
        .expect("the ownership proof must work before testing the changed store");
    let changed = [(
        "read.c",
        "int32 read(int32* p, int32* next, int32 value) { *p = 0; return *p; }",
    )];
    assert!(verify_c_sources(&source, &changed).is_err());
}

#[test]
fn recursive_child_resources_reject_nonstructural_definitions() {
    for (from, to) in [
        ("fact tail.model == rest;", ""),
        ("fact tail.model == rest;", "fact tail.model == model;"),
        ("fact tail.model == rest;", "fact tail.model == value;"),
        (
            "fact tail.model == rest;",
            "fact tail.model == Chain::More(value, next, rest);",
        ),
        (
            "owns tail: chain(next);",
            "owns tail: chain(next); owns tail: chain(next);",
        ),
        ("owns tail: chain(next);", "views chain(next);"),
    ] {
        assert!(
            parser::parse(&RECURSIVE_CHILD_SOURCE.replace("BODY", "").replace(from, to)).is_err(),
            "accepted {from} -> {to}"
        );
    }
}

#[test]
fn algebraic_pointer_constructor_accepts_only_null_integer_literal() {
    let source = "spec enum Ptr { At(int32*) } function null_ptr() -> Ptr { Ptr::At(0) }";
    parser::parse(source).expect("literal zero is a typed null constructor field");
    let error = parser::parse(&source.replace("Ptr::At(0)", "Ptr::At(1)")).unwrap_err();
    assert!(
        error.message().contains("expects int32*, got int32"),
        "{}",
        error.message()
    );
}

const MATCH_CELL_SOURCE: &str = r#"verifying "read.c";
spec enum Maybe<T> { None, Some(T) }
resource cell(p: int32*) {
    field model: Maybe<int32>;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p[0..1]; fact p[0] == value; },
    }
}
int32 read(int32* p, int32 expected) {
    owns c: cell(p);
    requires c.model == Maybe<int32>::Some(expected);
    ensures result == expected;
    ensures c.model == old(c.model);
} by { unfold(c); step_until(function.exit); fold(c); close(); }
"#;

fn tree_node_init_fixture() -> (&'static str, Vec<(&'static str, &'static str)>) {
    let fixture = include_str!("../../mdtests/resource_tree_node_init.md");
    let source = fixture
        .split("```click\n")
        .nth(1)
        .unwrap()
        .split("```")
        .next()
        .unwrap();
    let c = fixture
        .split("```c filename=resource_tree_node_init.c\n")
        .nth(1)
        .unwrap()
        .split("```")
        .next()
        .unwrap();
    (source, vec![("resource_tree_node_init.c", c)])
}

#[test]
fn integer_resource_match_binding_verifies_and_expands() {
    let fixture = include_str!("../../mdtests/integer_resource_match_binding.md");
    let source = fixture
        .split("```click\n")
        .nth(1)
        .unwrap()
        .split("```")
        .next()
        .unwrap();
    let c = fixture
        .split("```c filename=integer_resource_match_binding.c\n")
        .nth(1)
        .unwrap()
        .split("```")
        .next()
        .unwrap();
    let sources = [("integer_resource_match_binding.c", c)];

    let verified_for_expansion =
        verify_c_sources(source, &sources).expect("matched Integer resource should verify");
    let expanded = expand_checked_grouped_claim(source, &verified_for_expansion, "keep")
        .expect("matched Integer resource should expand");
    verify_c_sources(&expanded, &sources)
        .expect("expanded matched Integer resource should re-verify");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2s in the parallel gate"]
fn tree_node_init_and_stored_child_links_expand() {
    let (source, c) = tree_node_init_fixture();
    let verified_for_expansion = verify_c_sources(source, &c).unwrap();
    for (_, expanded) in expand_checked_grouped_claims(
        source,
        &verified_for_expansion,
        ["tree_node_init", "read_value", "empty"],
    ) {
        verify_c_sources(&expanded, &c).unwrap();
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.0s in the parallel gate"]
fn tree_node_init_rejects_invalid_models_and_ownership() {
    let (source, c) = tree_node_init_fixture();
    for (from, to) in [
        (
            "model: HeapTree::Node(node, value, l.model, r.model)",
            "model: HeapTree::Node(node, 0, l.model, r.model)",
        ),
        (
            "model: HeapTree::Node(node, value, l.model, r.model)",
            "model: HeapTree::Node(left, value, l.model, r.model)",
        ),
        (
            "model: HeapTree::Node(node, value, l.model, r.model)",
            "model: HeapTree::Node(node, value, r.model, l.model)",
        ),
        ("left: l, right: r\n    });", "left: r, right: l\n    });"),
        ("left: l, right: r\n    });", "left: l, right: l\n    });"),
        ("consumes node->left;", ""),
        ("consumes r: tree_at(right);", ""),
        ("requires p == 0;", ""),
        // A child address may not be read from an unowned stored link.
        ("owns p->left;", ""),
        ("owns p->right;", ""),
        // Child ownership has been consumed into root, so it cannot be reused.
        (
            "left: l, right: r\n    });\n    close();",
            "left: l, right: r\n    });\n    unfold(l);\n    close();",
        ),
    ] {
        assert!(source.contains(from));
        assert!(
            verify_c_sources(&source.replace(from, to), &c).is_err(),
            "accepted {from} -> {to}"
        );
    }
    // Retain the real stores in the positive fixture; these intentionally
    // broken programs ensure the contract catches wrong/missing links.
    for broken in [
        c[0].1.replace("node->left = left;", "node->left = right;"),
        c[0].1.replace("node->right = right;", ""),
        c[0].1.replace("node->value = value;", "node->value = 0;"),
    ] {
        assert!(verify_c_sources(source, &[(c[0].0, broken.as_str())]).is_err());
    }
}

fn independent_children_source() -> &'static str {
    include_str!("../../mdtests/resource_independent_children.md")
        .split("```click\n")
        .nth(1)
        .unwrap()
        .split("```")
        .next()
        .unwrap()
}

const INDEPENDENT_CHILDREN_C: &[(&str, &str)] = &[(
    "resource_independent_children.c",
    "int32 read_left(int32* p, int32* left, int32* right) { return *left; }
     void init(int32* p, int32* left, int32* right, int32 value) { *p = value; }",
)];

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn independent_children_construct_and_expand() {
    let source = independent_children_source();
    let verified_for_expansion = verify_c_sources(source, INDEPENDENT_CHILDREN_C).unwrap();
    for (_, expanded) in
        expand_checked_grouped_claims(source, &verified_for_expansion, ["read_left", "init"])
    {
        verify_c_sources(&expanded, INDEPENDENT_CHILDREN_C).unwrap();
        assert!(expanded.contains("let { left: l, right: r } = unfold(root)"));
    }
}

#[test]
fn independent_children_may_change_roles_in_a_new_model() {
    let source = independent_children_source()
        .split("\nvoid init")
        .next()
        .unwrap()
        .replace(
            "ensures root.model == old(root.model);",
            "ensures root.model == Tree::Branch(1, right, Tree::Leaf(3), left, Tree::Leaf(2));",
        )
        .replace(
            "{ model: old(root.model), left: l, right: r }",
            "{ model: Tree::Branch(1, right, r.model, left, l.model), left: r, right: l }",
        );
    let verified_for_expansion = verify_c_sources(&source, INDEPENDENT_CHILDREN_C).unwrap();
    let expanded =
        expand_checked_grouped_claim(&source, &verified_for_expansion, "read_left").unwrap();
    verify_c_sources(&expanded, INDEPENDENT_CHILDREN_C).unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn independent_children_reject_bad_selection_and_consumed_names() {
    let source = independent_children_source();
    for (from, to) in [
        (
            "let { left: l, right: r } = unfold(root)",
            "let { left: l } = unfold(root)",
        ),
        (
            "let { left: l, right: r } = unfold(root)",
            "let { left: l, wrong: r } = unfold(root)",
        ),
        (
            "let { left: l, right: r } = unfold(root)",
            "let { left: l, right: l } = unfold(root)",
        ),
        (
            "let { left: l, right: r } = unfold(root)",
            "let { left: root, right: r } = unfold(root)",
        ),
        ("model: old(root.model),", "model: root.model,"),
        ("left: l, right: r });", "left: l });"),
        ("left: l, right: r });", "left: l, right: l });"),
        ("left: l, right: r });", "left: r, right: l });"),
        ("let l = fold(tree(left), { model: Tree::Leaf(2) });", ""),
        (
            "let l = fold(tree(left), { model: Tree::Leaf(2) });",
            "let l = fold(tree(right), { model: Tree::Leaf(2) });",
        ),
        ("unfold(l);", "unfold(root); unfold(l);"),
        ("unfold(l);", "unfold(l); unfold(l);"),
        ("consumes r: tree(right);", ""),
    ] {
        assert!(source.contains(from), "missing mutation target {from}");
        assert!(
            verify_c_sources(&source.replace(from, to), INDEPENDENT_CHILDREN_C).is_err(),
            "accepted {from} -> {to}"
        );
    }
    let expanded = expand_c_claim_source(
        source,
        INDEPENDENT_CHILDREN_C,
        "read_left",
        ContractProofClaim::Grouped,
    )
    .unwrap();
    assert!(
        verify_c_sources(
            &expanded.replace("left: l, right: r });", "left: r, right: l });"),
            INDEPENDENT_CHILDREN_C
        )
        .is_err()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn conditional_explicit_folds_update_models_and_expand() {
    let source = r#"verifying "cell.c";
        spec enum Model { Zero, Value(int32) }
        resource cell(p: int32*) {
            field model: Model;
            match model {
                Model::Zero => { owns p[0..1]; fact p[0] == 0; },
                Model::Value(value) => { owns p[0..1]; fact p[0] == value; },
            }
        }
        void set(int32* p, int32 value) {
            owns c: cell(p);
            requires c.model == Model::Zero;
            ensures c.model == Model::Value(value);
            ensures old(c.model) == Model::Zero;
        } by {
            unfold(c);
            step_until(function.exit);
            let c = fold(cell(p), { model: Model::Value(value) });
            close();
        }
    "#;
    let sources = [("cell.c", "void set(int32* p, int32 value) { *p = value; }")];
    let verified_for_expansion = verify_c_sources(source, &sources).unwrap();
    let expanded = expand_checked_grouped_claim(source, &verified_for_expansion, "set").unwrap();
    verify_c_sources(&expanded, &sources).unwrap();
    for (from, to) in [
        ("model: Model::Value(value)", "model: Model::Zero"),
        ("model: Model::Value(value)", "model: Model::Value(0)"),
        ("model: Model::Value(value)", "model: c.model"),
        ("model: Model::Value(value)", "model: old(c.model)"),
        ("unfold(c);", ""),
        (
            "close();",
            "let duplicate = fold(cell(p), { model: Model::Value(value) }); close();",
        ),
    ] {
        assert!(
            verify_c_sources(&source.replace(from, to), &sources).is_err(),
            "accepted {from} -> {to}"
        );
    }
    assert!(
        verify_c_sources(
            &expanded.replace("model: Model::Value(value)", "model: Model::Zero"),
            &sources
        )
        .is_err()
    );
}

#[test]
fn conditional_empty_fold_requires_arm_facts_and_no_live_result() {
    let source = r#"verifying "empty.c";
        spec enum Maybe<T> { None, Some(T) }
        resource cell(p: int32*) {
            field model: Maybe<int32>;
            match model {
                Maybe::None => { fact p == 0; },
                Maybe::Some(value) => { owns p[0..1]; fact p[0] == value; },
            }
        }
        void empty(int32* p) {
            requires p == 0;
            produces c: cell(p);
            ensures c.model == Maybe<int32>::None;
        } by {
            let c = fold(cell(p), { model: Maybe<int32>::None });
            step_until(function.exit); close();
        }
    "#;
    let sources = [("empty.c", "void empty(int32* p) { }")];
    let verified_for_expansion = verify_c_sources(source, &sources).unwrap();
    let expanded = expand_checked_grouped_claim(source, &verified_for_expansion, "empty").unwrap();
    verify_c_sources(&expanded, &sources).unwrap();
    for (from, to) in [
        ("requires p == 0;", ""),
        ("model: Maybe<int32>::None", "model: Maybe<int32>::Some(0)"),
        (
            "step_until(function.exit);",
            "let c = fold(cell(p), { model: Maybe<int32>::None }); step_until(function.exit);",
        ),
    ] {
        assert!(
            verify_c_sources(&source.replace(from, to), &sources).is_err(),
            "accepted {from} -> {to}"
        );
    }
}

#[test]
fn guarded_explicit_folds_check_each_return_path() {
    let source = r#"verifying "cell.c";
        resource cell(p: int32*) {
            field value: int32;
            if p != 0 { owns p[0..1]; fact p[0] == value; }
        }
        void set(int32* p, int32 value) {
            owns c: cell(p);
            ensures c.value == value;
        } by {
            if p == 0 {
                unfold(c); step_until(function.exit);
                let c = fold(cell(p), { value: value }); close();
            } else {
                unfold(c); step_until(function.exit);
                let c = fold(cell(p), { value: value }); close();
            }
        }
    "#;
    let sources = [(
        "cell.c",
        "void set(int32* p, int32 value) { if (p != 0) *p = value; }",
    )];
    let verified_for_expansion = verify_c_sources(source, &sources).unwrap();
    let expanded = expand_checked_grouped_claim(source, &verified_for_expansion, "set").unwrap();
    verify_c_sources(&expanded, &sources).unwrap();
    assert!(verify_c_sources(&source.replace("value: value", "value: 0"), &sources).is_err());
    assert!(
        verify_c_sources(
            &source.replace(
                "unfold(c); step_until(function.exit);",
                "unfold(c); unfold(c); step_until(function.exit);"
            ),
            &sources
        )
        .is_err()
    );
}

#[test]
fn resource_match_expands_and_rechecks() {
    let c = [(
        "read.c",
        "int32 read(int32* p, int32 expected) { return *p; }",
    )];
    let verified = verify_c_sources(MATCH_CELL_SOURCE, &c).unwrap();
    verify_c_sources(
        &MATCH_CELL_SOURCE.replace(
            "by { unfold(c); step_until(function.exit); fold(c); close(); }",
            &verified[0].expanded_proof_source().unwrap(),
        ),
        &c,
    )
    .unwrap();
}

#[test]
fn resource_match_rejects_unknown_cases_missing_memory_and_invalid_folds() {
    let c = [(
        "read.c",
        "int32 read(int32* p, int32 expected) { return *p; }",
    )];
    for (from, to) in [
        ("requires c.model == Maybe<int32>::Some(expected);", ""),
        (
            "requires c.model == Maybe<int32>::Some(expected);",
            "requires c.model == Maybe<int32>::None;",
        ),
        ("unfold(c);", ""),
        ("fold(c); close();", "fold(c); fold(c); close();"),
        ("result == expected", "result == 42"),
    ] {
        assert!(
            verify_c_sources(&MATCH_CELL_SOURCE.replace(from, to), &c).is_err(),
            "accepted {from} -> {to}"
        );
    }
    let changed = [(
        "read.c",
        "int32 read(int32* p, int32 expected) { *p = 0; return *p; }",
    )];
    assert!(verify_c_sources(MATCH_CELL_SOURCE, &changed).is_err());
}

#[test]
fn resource_match_checks_exhaustiveness_and_binding_scope() {
    for (from, to) in [
        ("Maybe::None => { fact p == 0; },", ""),
        (
            "Maybe::None => { fact p == 0; },",
            "Maybe::Some(other) => {},",
        ),
        ("Maybe::Some(value)", "Maybe::Missing(value)"),
        ("Maybe::Some(value)", "Other::Some(value)"),
        ("Maybe::Some(value)", "Maybe::Some(value, extra)"),
        ("Maybe::Some(value)", "Maybe::Some(p)"),
        ("Maybe::Some(value)", "Maybe::Some(model)"),
        ("fact p == 0;", "fact value == 0;"),
        (
            "owns p[0..1];",
            "match model { Maybe::None => {}, Maybe::Some(x) => {} }",
        ),
        ("owns p[0..1];", "field extra: int32;"),
    ] {
        assert!(
            parser::parse(&MATCH_CELL_SOURCE.replace(from, to)).is_err(),
            "accepted {from} -> {to}"
        );
    }
}

#[test]
fn resource_match_binds_pointer_and_nested_algebraic_payloads() {
    let source = r#"verifying "read.c";
        spec enum Boxed<T> { Box(T) }
        resource cell(p: int32*) {
            field model: Boxed<int32*>;
            field nested: Boxed<int32>;
            match model {
                Boxed::Box(address) => { owns address[0..1]; fact address == p; }
            }
        }
        int32 read(int32* p, int32 expected) {
            owns c: cell(p);
            requires c.model == Boxed<int32*>::Box(p);
            ensures c.model == old(c.model);
        } by { unfold(c); step_until(function.exit); let c = fold(cell(p), { model: Boxed<int32*>::Box(p), nested: old(c.nested) }); close(); }
    "#;
    let c = [(
        "read.c",
        "int32 read(int32* p, int32 expected) { return *p; }",
    )];
    verify_c_sources(source, &c).unwrap();
    let nested = source
        .replace(
            "field model: Boxed<int32*>;",
            "field model: Boxed<Boxed<int32>>;",
        )
        .replace(
            "Boxed::Box(address) => { owns address[0..1]; fact address == p; }",
            "Boxed::Box(inner) => { owns p[0..1]; fact inner == nested; }",
        )
        .replace(
            "requires c.model == Boxed<int32*>::Box(p);",
            "requires c.model == Boxed<Boxed<int32>>::Box(c.nested);",
        )
        .replace(
            "model: Boxed<int32*>::Box(p)",
            "model: Boxed<Boxed<int32>>::Box(old(c.nested))",
        );
    verify_c_sources(&nested, &c).unwrap();
    let expanded = expand_function_proof_source(&nested, &c, "read").unwrap();
    verify_c_sources(&expanded, &c).unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn instance_return_folds_follow_distinct_program_results_after_explicit_splits() {
    let source = r#"verifying "read.c";
        resource cell(p: int32*) {
            field value: int32;
            owns p[0..1]; fact p[0] == value;
        }
        int32 read(int32* p, int32 fallback, int32 use_value) {
            owns c: cell(p);
            ensures (use_value == 0 and result == fallback) or (use_value != 0 and result == c.value);
            ensures c.value == old(c.value);
        } by { unfold(c); branch { true => { step(); } false => { } } step_until(function.exit); fold(c); close(); }
    "#;
    let c = [(
        "read.c",
        "int32 read(int32* p, int32 fallback, int32 use_value) { if (use_value == 0) return fallback; return *p; }",
    )];
    let verified = verify_c_sources(source, &c).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    verify_c_sources(
        &source.replace(
            "by { unfold(c); branch { true => { step(); } false => { } } step_until(function.exit); fold(c); close(); }",
            &expanded,
        ),
        &c,
    )
    .unwrap();
    assert!(
        verify_c_sources(
            &source.replace("result == fallback", "result == c.value"),
            &c
        )
        .is_err()
    );
    let body = "by { unfold(c); if use_value == 0 { step_until(function.exit); fold(c); close(); } else { step_until(function.exit); fold(c); close(); } }";
    let branched = source.replace(
        "by { unfold(c); branch { true => { step(); } false => { } } step_until(function.exit); fold(c); close(); }",
        body,
    );
    let verified = verify_c_sources(&branched, &c).unwrap();
    verify_c_sources(
        &branched.replace(body, &verified[0].expanded_proof_source().unwrap()),
        &c,
    )
    .unwrap();
}

#[test]
fn guarded_instance_return_paths_expand_and_recheck() {
    let body = "if p == 0 { unfold(c); step_until(function.exit); fold(c); close(); } else { unfold(c); step_until(function.exit); fold(c); close(); }";
    let source = GUARDED_CELL_SOURCE.replace("BODY", body);
    let c = [("read.c", GUARDED_CELL_C)];
    let verified = verify_c_sources(&source, &c).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    verify_c_sources(&source.replace(&format!("by {{ {body} }}"), &expanded), &c).unwrap();
}

#[test]
fn guarded_instance_return_paths_reject_invalid_folds() {
    for body in [
        "unfold(c); step_until(function.exit); fold(c); close();",
        "if p == 0 { unfold(c); step_until(function.exit); fold(c); fold(c); close(); } else { unfold(c); step_until(function.exit); fold(c); close(); }",
    ] {
        assert!(
            verify_c_sources(
                &GUARDED_CELL_SOURCE.replace("BODY", body),
                &[("read.c", GUARDED_CELL_C)]
            )
            .is_err(),
            "accepted {body}"
        );
    }
    // A body fact exposed only on the nonnull arm cannot justify the null result.
    let body = "if p == 0 { unfold(c); step_until(function.exit); fold(c); close(); } else { unfold(c); step_until(function.exit); fold(c); close(); }";
    let source = GUARDED_CELL_SOURCE.replace("BODY", body);
    assert!(
        verify_c_sources(
            &source.replace("p == 0 or result == c.value", "result == c.value"),
            &[("read.c", GUARDED_CELL_C)]
        )
        .is_err()
    );
    // Only one branch changes memory: the other branch's valid fold cannot
    // certify this return's stale field relation.
    let changed = "int32 read(int32* p) { if (p == 0) return 0; *p = 0; return *p; }";
    assert!(verify_c_sources(&source, &[("read.c", changed)]).is_err());
}

#[test]
fn named_instance_memory_body_round_trip_preserves_fields() {
    let source = r#"verifying "read.c";
        spec enum Mark { Clear, Set }
        resource cell(p: int32*) {
            field value: int32;
            field mark: Mark;
            owns p[0..1];
            fact p[0] == value;
        }
        int32 read(int32* p) {
            owns c: cell(p);
            ensures result == c.value;
            ensures c.value == old(c.value);
            ensures c.mark == old(c.mark);
        } by { unfold(c); step_until(function.exit); fold(c); close(); }
    "#;
    let c = [("read.c", "int32 read(int32* p) { return *p; }")];
    let verified = verify_c_sources(source, &c).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    verify_c_sources(
        &source.replace(
            "by { unfold(c); step_until(function.exit); fold(c); close(); }",
            &expanded,
        ),
        &c,
    )
    .unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn single_cell_adt_initializers_verify_and_expand() {
    let source = r#"verifying "cell.c";
        spec enum Mark { Set(int32) }
        function mark(x: int32) -> Mark { Mark::Set(x) }
        resource cell(p: int32*) {
            field model: Mark;
            owns p[0..1];
            fact model == MODEL;
        }
        void init(int32* p, int32 value) {
            consumes p[0..1];
            produces c: cell(p);
            ensures c.model == INITIALIZER;
        } by {
            step_until(function.exit);
            let c = fold(cell(p), { model: INITIALIZER });
            close();
        }
    "#;
    let sources = [("cell.c", "void init(int32* p, int32 value) { *p = value; }")];
    for (model, initializer) in [
        ("Mark::Set(p[0])", "Mark::Set(value)"),
        ("Mark::Set(p[0])", "Mark::Set(p[0])"),
        ("mark(p[0])", "mark(value)"),
    ] {
        let source = source
            .replace("MODEL", model)
            .replace("INITIALIZER", initializer);
        let verified_for_expansion = verify_c_sources(&source, &sources).unwrap();
        let expanded =
            expand_checked_grouped_claim(&source, &verified_for_expansion, "init").unwrap();
        verify_c_sources(&expanded, &sources).unwrap();
    }
}

#[test]
fn single_cell_adt_initializers_reject_invalid_models() {
    let source = r#"verifying "cell.c";
        spec enum Mark { Set(int32) }
        spec enum Other { Set(int32) }
        resource cell(p: int32*) {
            field model: Mark;
            owns p[0..1];
            fact model == Mark::Set(p[0]);
        }
        void init(int32* p, int32* q, int32 value) {
            consumes p[0..1];
            produces c: cell(p);
        } by {
            step_until(function.exit);
            let c = fold(cell(p), { model: INITIALIZER });
            close();
        }
    "#;
    let sources = [(
        "cell.c",
        "void init(int32* p, int32* q, int32 value) { *p = value; }",
    )];
    for initializer in [
        "Mark::Set(0)",
        "Other::Set(value)",
        "value",
        "Mark::Set(q[0])",
        "Mark::Set(value, value)",
        "Mark::Set()",
        "Mark::Missing",
    ] {
        assert!(
            verify_c_sources(&source.replace("INITIALIZER", initializer), &sources).is_err(),
            "accepted {initializer}"
        );
    }
    let update = source
        .replace(
            "consumes p[0..1];\n            produces c: cell(p);",
            "owns c: cell(p);",
        )
        .replace(
            "step_until(function.exit);",
            "unfold(c); step_until(function.exit);",
        );
    for initializer in ["c.model", "old(c.model)"] {
        assert!(
            verify_c_sources(&update.replace("INITIALIZER", initializer), &sources).is_err(),
            "accepted stale {initializer}"
        );
    }
    // A ghost model can name a total logical read without claiming validity.
    let unconstrained = source.replace("fact model == Mark::Set(p[0]);", "");
    assert!(
        verify_c_sources(
            &unconstrained.replace("INITIALIZER", "Mark::Set(q[0])"),
            &sources
        )
        .is_ok()
    );
    let scalar = unconstrained.replace("field model: Mark;", "field model: int32;");
    assert!(verify_c_sources(&scalar.replace("INITIALIZER", "q[0]"), &sources).is_ok());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn single_cell_adt_initializers_preserve_arbitrary_entry_models() {
    let source = r#"verifying "cell.c";
        spec enum Maybe<T> { None, Some(T) }
        function identity<T>(x: Maybe<T>) -> Maybe<T> { x }
        function passthrough<T>(x: T) -> T { x }
        resource cell(p: int32*) {
            field model: Maybe<int32>;
            owns p[0..1];
        }
        void preserve(int32* p) {
            owns c: cell(p);
            ensures c.model == VALUE;
        } by {
            unfold(c);
            let c = fold(cell(p), { model: VALUE });
            step_until(function.exit);
            close();
        }
    "#;
    let sources = [("cell.c", "void preserve(int32* p) { }")];
    for value in [
        "old(c.model)",
        "identity(old(c.model))",
        "passthrough(old(c.model))",
        "match old(c.model) { Maybe::None => Maybe<int32>::None, Maybe::Some(x) => Maybe<int32>::Some(x), }",
    ] {
        let source = source.replace("VALUE", value);
        verify_c_sources(&source, &sources).unwrap_or_else(|error| panic!("{value}: {error:?}"));
        let expanded =
            expand_c_claim_source(&source, &sources, "preserve", ContractProofClaim::Grouped)
                .unwrap();
        verify_c_sources(&expanded, &sources)
            .unwrap_or_else(|error| panic!("{value}: {error:?}\n{expanded}"));
    }
    let changed = source
        .replace(
            "owns c: cell(p);",
            "owns c: cell(p); requires c.model == Maybe<int32>::None;",
        )
        .replace(
            "ensures c.model == VALUE;",
            "ensures old(c.model) == Maybe<int32>::None;",
        )
        .replace("VALUE", "Maybe<int32>::Some(7)");
    verify_c_sources(&changed, &sources).unwrap();
    let expanded =
        expand_c_claim_source(&changed, &sources, "preserve", ContractProofClaim::Grouped).unwrap();
    verify_c_sources(&expanded, &sources).unwrap();
    assert!(
        verify_c_sources(
            &changed.replace(
                "ensures old(c.model) == Maybe<int32>::None;",
                "ensures old(c.model) == Maybe<int32>::Some(7);"
            ),
            &sources
        )
        .is_err()
    );
}

#[test]
fn single_cell_explicit_fold_constructs_updates_and_expands() {
    let source = r#"verifying "cell.c";
        resource cell(p: int32*) {
            field value: int32;
            owns p[0..1];
            fact p[0] == value;
        }
        void init(int32* p, int32 value) {
            consumes p[0..1];
            produces c: cell(p);
            ensures c.value == value;
        } by {
            step_until(function.exit);
            let c = fold(cell(p), { value: value });
            close();
        }
    "#;
    let sources = [("cell.c", "void init(int32* p, int32 value) { *p = value; }")];
    for source in [
        source.to_string(),
        source
            .replace(
                "consumes p[0..1];\n            produces c: cell(p);",
                "owns c: cell(p);",
            )
            .replace(
                "step_until(function.exit);",
                "unfold(c); step_until(function.exit);",
            ),
    ] {
        let verified_for_expansion = verify_c_sources(&source, &sources).unwrap();
        let expanded =
            expand_checked_grouped_claim(&source, &verified_for_expansion, "init").unwrap();
        assert!(expanded.contains("let c = fold("), "{expanded}");
        verify_c_sources(&expanded, &sources).unwrap();
    }
}

#[test]
fn single_cell_explicit_fold_rejects_missing_wrong_and_duplicate_ownership() {
    let source = r#"verifying "cell.c";
        resource cell(p: int32*) {
            field value: int32;
            owns p[0..1];
            fact p[0] == value;
        }
        void init(int32* p, int32 value) {
            consumes p[0..1];
            produces c: cell(p);
            ensures c.value == value;
        } by { step_until(function.exit); FOLD close(); }
    "#;
    let sources = [("cell.c", "void init(int32* p, int32 value) { *p = value; }")];
    for fold in [
        "let c = fold(cell(p), {});",
        "let c = fold(cell(p), { wrong: value });",
        "let c = fold(cell(p), { value: value, value: value });",
        "let c = fold(cell(p), { value: p });",
        "let c = fold(cell(p), { value: 0 });",
        "let c = fold(cell(p), { value: value }); let c = fold(cell(p), { value: value });",
        "let c = fold(cell(p), { value: value }); let other = fold(cell(p), { value: value });",
    ] {
        assert!(
            verify_c_sources(&source.replace("FOLD", fold), &sources).is_err(),
            "accepted {fold}"
        );
    }
    // Opening the constructed instance preserves its captured field, and the
    // contract closer can refold it from the still-held cells.
    let opened = source.replace(
        "FOLD",
        "let c = fold(cell(p), { value: value }); unfold(c);",
    );
    verify_c_sources(&opened, &sources).unwrap();

    let no_ownership = source
        .replace("consumes p[0..1];", "")
        .replace("step_until(function.exit);", "")
        .replace("FOLD", "let c = fold(cell(p), { value: value });");
    assert!(verify_c_sources(&no_ownership, &sources).is_err());
}

#[test]
fn single_cell_explicit_fold_preserves_entry_fields_and_consumes_names() {
    let source = r#"verifying "cell.c";
        resource cell(p: int32*) {
            field value: int32;
            field revision: int32;
            owns p[0..1];
            fact p[0] == value;
        }
        void set(int32* p, int32 value) {
            owns c: cell(p);
            requires c.value == 7;
            requires c.revision == 1;
            ensures old(c.value) == 7;
            ensures old(c.revision) == 1;
            ensures c.value == value;
            ensures c.revision == 2;
        } by {
            unfold(c);
            step();
            let c = fold(cell(p), { revision: 2, value: value });
            unfold(c);
            let c = fold(cell(p), { value: value, revision: 2 });
            step_until(function.exit);
            close();
        }
    "#;
    let sources = [("cell.c", "void set(int32* p, int32 value) { *p = value; }")];
    let verified_for_expansion = verify_c_sources(source, &sources).unwrap();
    let expanded = expand_checked_grouped_claim(source, &verified_for_expansion, "set").unwrap();
    verify_c_sources(&expanded, &sources).unwrap();
    for stale in [
        source.replace("ensures c.revision == 2;", "ensures c.revision == 1;"),
        source.replace("ensures c.value == value;", "ensures c.value == 7;"),
    ] {
        assert!(
            verify_c_sources(&stale, &sources).is_err(),
            "entry fields must not be reused as current fields after an update"
        );
    }
    let invalid = source.replacen(
        "unfold(c);",
        "unfold(c); have c.value == c.value by { reflexivity(); }",
        1,
    );
    assert!(
        verify_c_sources(&invalid, &sources).is_err(),
        "consumed resource fields are not a live handle"
    );
}

#[test]
fn named_instance_memory_body_rejects_invalid_folds() {
    let source = r#"verifying "read.c";
        resource cell(p: int32*) {
            field value: int32;
            owns p[0..1];
            fact p[0] == value;
        }
        int32 read(int32* p) {
            owns c: cell(p);
            ensures result == c.value;
        } by { BODY }
    "#;
    for (body, c) in [
        (
            "fold(c); step_until(function.exit); close();",
            "int32 read(int32* p) { return *p; }",
        ),
        (
            "unfold(c); unfold(c); step_until(function.exit); fold(c); close();",
            "int32 read(int32* p) { return *p; }",
        ),
        (
            "unfold(c); step_until(function.exit); fold(c); fold(c); close();",
            "int32 read(int32* p) { return *p; }",
        ),
        (
            "step_until(function.exit); close();",
            "int32 read(int32* p) { return *p; }",
        ),
        (
            "unfold(c); step_until(function.exit); fold(c); close();",
            "int32 read(int32* p) { *p = 0; return *p; }",
        ),
    ] {
        let error = verify_c_sources(&source.replace("BODY", body), &[("read.c", c)])
            .err()
            .unwrap_or_else(|| panic!("invalid instance proof accepted: {body}, {c}"));
        if c.contains("*p = 0") {
            assert!(
                error
                    .message
                    .contains("fold requires the instance body facts for the proposed fields"),
                "{error:?}"
            );
        }
    }
}

#[test]
fn checked_original_claim_can_close_after_rewrite_but_unrelated_have_cannot() {
    let source = r#"verifying "identity.c";
        int32 identity(int32 x) {
            requires x == 1;
            ensures result == 1;
        } by {
            step_until(function.exit); rewrite(x, 1);
            have result == 1 by { rewrite(x, 1); normalize(); }
            close();
        }
    "#;
    let c = [("identity.c", "int32 identity(int32 x) { return x; }")];
    verify_c_sources(source, &c).unwrap();
    assert!(
        verify_c_sources(
            &source.replace("ensures result == 1;", "ensures result == 2;"),
            &c
        )
        .is_err()
    );
    assert!(
        verify_c_sources(
            &source.replace("have result == 1 by", "have result == 2 by"),
            &c
        )
        .is_err()
    );
}

#[test]
fn opaque_resource_call_transports_only_the_selected_instance() {
    let source = r#"verifying "invoke.c";
        spec enum Mark { Clear, Set }
        resource marker() { field model: Mark; field revision: int32; }
        contract int32 Touch() {
            owns cell: marker();
            ensures cell.model == old(cell.model);
            ensures cell.revision == 1;
            ensures result == 0;
        }
        int32 invoke(int32 (*callback)()) {
            requires Touch(callback);
            owns first: marker(); owns second: marker();
            ensures first.model == old(first.model);
            ensures first.revision == 1;
            ensures second.model == old(second.model);
            ensures second.revision == old(second.revision);
            ensures result == 0;
        } by { step(Touch, { cell: first }); step_until(function.exit); close(); }
    "#;
    let c = [(
        "invoke.c",
        "int32 invoke(int32 (*callback)()) { return callback(); }",
    )];
    let verified = verify_c_sources(source, &c).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    assert!(expanded.contains("step(Touch, { cell: first });"));
    verify_c_sources(
        &source.replace(
            "by { step(Touch, { cell: first }); step_until(function.exit); close(); }",
            &expanded,
        ),
        &c,
    )
    .unwrap();
    for bad in [
        source.replace(
            "ensures first.revision == 1;",
            "ensures first.revision == old(first.revision);",
        ),
        source.replace("ensures cell.model == old(cell.model);", ""),
        source.replace("{ cell: first }", "{ cell: second }"),
    ] {
        assert!(verify_c_sources(&bad, &c).is_err());
    }
}

#[test]
fn contract_resource_handles_are_named_body_clauses() {
    let file = parser::parse(
        r#"
        resource marker(p: int32*) { field revision: int32; }
        contract int32 Read(int32* p) {
            owns cell: marker(p);
            ensures cell.revision == old(cell.revision);
        }
        contract int32 Plain(int32* p) { ensures result == 0; }
    "#,
    )
    .unwrap();
    let definition = &file.contract_definitions()[0];
    assert_eq!(definition.name(), "Read");
    assert_eq!(definition.proof_parameters().unwrap().len(), 1);
    assert_eq!(
        definition.function_block().signature().parameters().len(),
        1
    );
    assert!(file.contract_definitions()[1].proof_parameters().is_none());
    let header = "resource marker(p: int32*) { field revision: int32; }";
    for (invalid, diagnostic) in [
        (
            "contract C(cell: marker(p)) for int32(int32* p) { owns cell; }",
            "is retired",
        ),
        (
            "contract int32 C(int32* p) { owns cell: marker(p); owns cell: marker(p); }",
            "duplicate resource instance binding `cell`",
        ),
        ("contract int32 C() { owns cell: marker(0); }", ""),
        ("contract int32 C() { owns cell: missing(); }", ""),
        (
            "contract int32 C(int32* p) throws int32 { owns cell: marker(p); }",
            "throwing contracts support borrowed memory",
        ),
    ] {
        let error = parser::parse(&format!("{header} {invalid}"))
            .expect_err(&format!("must reject {invalid}"));
        assert!(error.message().contains(diagnostic), "{}", error.message());
    }
}

#[test]
fn explicit_contract_applications_preserve_arguments_when_printed() {
    let source = r#"
        resource marker() { field revision: int32; }
        contract int32 Touch() { owns cell: marker(); }
        int32 f() { owns first: marker(); owns second: marker(); }
        by { step(Touch, { cell: second }); }
    "#;
    let file = parser::parse(source).unwrap();
    let SourceProof::Script(tactics) = file.function_blocks()[0].grouped_proof().unwrap() else {
        panic!("expected script")
    };
    let printed = printing::format_proof_tactics(tactics).unwrap();
    assert!(
        printed.contains("step(Touch, { cell: second });"),
        "{printed}"
    );
    let ProofTactic::StepCall(application) = &tactics[0] else {
        panic!("expected named call transport")
    };
    assert!(application.is_named_contract());
    assert_eq!(application.binders()[0].binder(), "cell");
    assert_eq!(application.binders()[0].instance(), "second");
    assert!(parser::parse(&source.replace("cell: second", "cell: missing")).is_err());
    let error = parser::parse(&source.replace("Touch, { cell: second }", "Touch(second)"))
        .expect_err("the positional application is retired");
    assert!(
        error.message().contains("`step(Touch(...))` is retired"),
        "{}",
        error.message()
    );
}

#[test]
fn call_binder_transport_prints_and_expands_its_map_unchanged() {
    let printed_source = r#"
        resource Counter() { field revision: int32; }
        void increment(int32* state) {
            owns first: Counter();
            ensures first.revision == 1;
        }
        void caller(int32* state) {
            owns c: Counter();
            ensures c.revision == 1;
        } by { step(increment, { first: c }); }
    "#;
    let file = parser::parse(printed_source).unwrap();
    let SourceProof::Script(tactics) = file.function_blocks()[1].grouped_proof().unwrap() else {
        panic!("expected script")
    };
    let printed = printing::format_proof_tactics(tactics).unwrap();
    assert!(
        printed.contains("step(increment, { first: c });"),
        "{printed}"
    );
    let ProofTactic::StepCall(transport) = &tactics[0] else {
        panic!("expected a call binder transport")
    };
    assert_eq!(transport.callee(), "increment");
    assert_eq!(transport.binders()[0].binder(), "first");
    assert_eq!(transport.binders()[0].instance(), "c");
    assert!(transport.produced().is_empty());

    let source = r#"verifying "increment.c";
        resource Counter() { field revision: int32; }
        void increment(int32* state) {
            owns first: Counter();
            ensures first.revision == 1;
        } by {
            unfold(first);
            step_until(function.exit);
            let first = fold(Counter(), { revision: 1 });
            close();
        }
        void caller(int32* state) {
            owns c: Counter();
            ensures c.revision == 1;
        } by { step(increment, { first: c }); step_until(function.exit); close(); }
    "#;
    let c = [(
        "increment.c",
        "void increment(int32* state) { }\nvoid caller(int32* state) { increment(state); }",
    )];
    let verified = verify_c_sources(source, &c).unwrap();
    let expanded = verified
        .iter()
        .filter_map(|claim| claim.expanded_proof_source().ok())
        .find(|expanded| expanded.contains("step(increment"))
        .unwrap_or_else(|| panic!("no expanded proof kept the call step"));
    assert!(
        expanded.contains("step(increment, { first: c });"),
        "{expanded}"
    );
    verify_c_sources(
        &source.replace(
            "by { step(increment, { first: c }); step_until(function.exit); close(); }",
            &expanded,
        ),
        &c,
    )
    .unwrap();
}

/// Outputs are independent of the optional map. Both input spellings print
/// a named call without a map when it has no entries.
#[test]
fn call_output_binding_omits_an_empty_input_map() {
    let source = r#"
        resource Counter() { field revision: int32; }
        void make(int32* state) {
            produces made: Counter();
        }
        int32 get(int32* state) {
            ensures result == 1;
        }
        int32 mixed(int32* state) {
            produces made: Counter();
            ensures result == 1;
        }
        void caller(int32* state) {
            owns c: Counter();
            ensures c.revision == 1;
        } by {
            let { made: m } = step(make);
            let { result: value } = step(get);
            let { made: another, result: status } = step(mixed);
        }
    "#;
    let file = parser::parse(source).unwrap();
    let SourceProof::Script(tactics) = file.function_blocks()[3].grouped_proof().unwrap() else {
        panic!("expected script")
    };
    let printed = printing::format_proof_tactics(tactics).unwrap();
    assert!(
        printed.contains("let { made: m } = step(make);"),
        "{printed}"
    );
    assert!(
        printed.contains("let { result: value } = step(get);"),
        "{printed}"
    );
    assert!(
        printed.contains("let { result: status, made: another } = step(mixed);"),
        "{printed}"
    );
    let with_empty_map = source.replace("step(make)", "step(make, {})").replace(
        "let { made: another, result: status } = step(mixed);",
        "let { result: status, made: another } = step(mixed);",
    );
    let reparsed = parser::parse(&with_empty_map).unwrap();
    let SourceProof::Script(again) = reparsed.function_blocks()[3].grouped_proof().unwrap() else {
        panic!("expected script")
    };
    assert_eq!(printed, printing::format_proof_tactics(again).unwrap());
}

#[test]
fn named_contract_call_can_bind_a_result_without_an_input_map() {
    let source = r#"verifying "call.c";
        contract int32 Exact(int32 n) { ensures result == n; }
        int32 run(int32 (*cb)(int32), int32 n) {
            requires Exact(cb);
            ensures result == n;
        } by {
            let { result: value } = step(Exact);
            step_until(function.exit);
            close();
        }
    "#;
    let inputs = [(
        "call.c",
        "int32 run(int32 (*cb)(int32), int32 n) { return cb(n); }",
    )];
    let verified = verify_c_sources(source, &inputs).unwrap();
    let expanded = expand_checked_grouped_claim(source, &verified, "run").unwrap();
    assert!(
        expanded.contains("let { result: value } = step(Exact);"),
        "{expanded}"
    );
    crate::surface::proof::without_implicit_solve(|| verify_c_sources(&expanded, &inputs)).unwrap();
}

#[test]
fn call_binder_transport_rejects_a_frontier_call_to_another_function() {
    let source = r#"verifying "increment.c";
        resource Counter() { field revision: int32; }
        void increment(int32* state) {
            owns first: Counter();
            ensures first.revision == 1;
        } by {
            unfold(first);
            step_until(function.exit);
            let first = fold(Counter(), { revision: 1 });
            close();
        }
        void other(int32* state) { ensures 0 == 0; }
        void caller(int32* state) {
            owns c: Counter();
            ensures c.revision == 1;
        } by { step(increment, { first: c }); step_until(function.exit); close(); }
    "#;
    let c = [(
        "increment.c",
        "void increment(int32* state) { }\nvoid other(int32* state) { }\nvoid caller(int32* state) { other(state); increment(state); }",
    )];
    let error = verify_c_sources(source, &c).unwrap_err();
    assert!(
        error
            .message()
            .contains("requires a call to `increment` at the current frontier"),
        "{}",
        error.message()
    );

    let missing = source.replace("step(increment, { first: c })", "step(increment)");
    let error = verify_c_sources(&missing, &c).unwrap_err();
    assert!(
        error
            .message()
            .contains("call map omits `increment` binder `first`"),
        "{error}"
    );
}

#[test]
fn named_function_call_map_prints_as_written_and_retires_the_other_spellings() {
    let source = |proof: &str| {
        format!(
            r#"import click::c::string;
        verifying "measure.c";
        extern uint64 measure(const char* s) {{
            let n: uint64;
            views cstr_at(s, n);
            ensures result == n;
        }}
        uint64 f() {{ ensures result == 0u64; }} by {{ {proof} }}
    "#
        )
    };
    let file = parser::parse(&source("let { result: r } = step(measure, { n: 0u64 });")).unwrap();
    let SourceProof::Script(tactics) = file.function_blocks()[1].grouped_proof().unwrap() else {
        panic!("expected script")
    };
    let ProofTactic::StepCall(transport) = &tactics[0] else {
        panic!("expected a call step")
    };
    assert!(transport.is_frontier());
    assert_eq!(transport.callee(), "measure");
    assert_eq!(transport.result(), Some("r"));
    let printed = printing::format_proof_tactics(tactics).unwrap();
    assert!(
        printed.contains("let { result: r } = step(measure, { n: 0u64 });"),
        "{printed}"
    );

    for (written, refusal) in [
        ("step({ n: 0u64 });", "`step({ ... })` is retired"),
        (
            "step(measure(tmp), { n: 0u64 });",
            "`step(measure(...), { ... })` is retired: write `step(measure, { ... })`",
        ),
    ] {
        let error = parser::parse(&source(written)).unwrap_err();
        assert!(
            error.message().contains(refusal),
            "{written}: {}",
            error.message()
        );
    }
}

#[test]
fn explicit_contract_empty_application_verifies_and_expands() {
    let source = r#"verifying "invoke.c";
        contract int32 Identity(int32 x) { ensures result == x; }
        int32 invoke(int32 (*callback)(int32), int32 x) {
            requires Identity(callback);
            ensures result == x;
        } by { step(Identity); step_until(function.exit); close(); }
    "#;
    let c = [(
        "invoke.c",
        "int32 invoke(int32 (*callback)(int32), int32 x) { return callback(x); }",
    )];
    let verified = verify_c_sources(source, &c).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    assert!(expanded.contains("step(Identity);"), "{expanded}");
    verify_c_sources(
        &source.replace(
            "by { step(Identity); step_until(function.exit); close(); }",
            &expanded,
        ),
        &c,
    )
    .unwrap();
    let error =
        verify_c_sources(&source.replace("step(Identity)", "step(Identity())"), &c).unwrap_err();
    assert!(
        error.message().contains("`step(Identity(...))` is retired"),
        "{}",
        error.message()
    );
}

#[test]
fn contract_application_binds_each_handle_by_name() {
    let source = r#"verifying "invoke.c";
        resource marker() { field revision: int32; }
        resource other() { field revision: int32; }
        contract int32 Touch() { owns cell: marker(); ensures result == 0; }
        int32 invoke(int32 (*callback)()) {
            requires Touch(callback);
            owns first: marker(); owns second: other();
            ensures result == 0;
        } by { step(Touch, { cell: first }); step_until(function.exit); close(); }
    "#;
    // C spells the empty function-pointer parameter list `()`.
    let c = [(
        "invoke.c",
        "int32 invoke(int32 (*callback)()) { return callback(); }",
    )];
    for (application, diagnostic) in [
        (
            "Touch",
            "declares resource handles; write `step(Touch, { cell: ... })`",
        ),
        (
            "Touch, {}",
            "declares resource handles; write `step(Touch, { cell: ... })`",
        ),
        (
            "Touch, { slot: first }",
            "`Touch` declares no resource instance binder `slot`",
        ),
        (
            "Touch, { cell: first, cell: first }",
            "duplicate binder `cell` in the call map",
        ),
        (
            "Touch, { cell: second }",
            "binder `cell` expects resource `marker`, but `second` is `other`",
        ),
    ] {
        let error = verify_c_sources(&source.replace("Touch, { cell: first }", application), &c)
            .unwrap_err();
        assert!(error.message().contains(diagnostic), "{}", error.message());
    }
    verify_c_sources(source, &c).unwrap();
    let duplicate = source
        .replace(
            "owns cell: marker();",
            "owns cell: marker(); owns another: marker();",
        )
        .replace("{ cell: first }", "{ cell: first, another: first }");
    let error = verify_c_sources(&duplicate, &c).unwrap_err();
    assert!(
        error
            .message()
            .contains("resource instance `first` cannot supply two binders of `Touch`"),
        "{}",
        error.message()
    );
    let handle_free = source.replace("owns cell: marker();", "");
    let error = verify_c_sources(&handle_free, &c).unwrap_err();
    assert!(
        error
            .message()
            .contains("`Touch` declares no resource instance binder `cell`"),
        "{}",
        error.message()
    );
}

#[test]
fn opaque_resource_call_checks_actual_c_arguments_and_call_entry_states() {
    let source = r#"verifying "invoke.c";
        resource marker(p: int32*) { field revision: int32; }
        contract int32 Touch(int32* p) {
            owns cell: marker(p);
            ensures cell.revision == 1;
            ensures result == old(cell.revision);
        }
        int32 invoke(int32 (*callback)(int32*), int32* p, int32* q) {
            requires Touch(callback);
            owns first: marker(p); owns second: marker(q);
            ensures first.revision == 1;
            ensures second.revision == old(second.revision);
            ensures result == 1;
        } by { step(Touch, { cell: first }); step(Touch, { cell: first }); step_until(function.exit);
            close(); close(); close(); close();
            rewrite(result, at(region(0).exit, first.revision));
            rewrite(at(region(0).exit, first.revision), 1); close(); }
    "#;
    let c = [(
        "invoke.c",
        "int32 invoke(int32 (*callback)(int32*), int32* p, int32* q) { callback(p); return callback(p); }",
    )];
    let verified = verify_c_sources(source, &c).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    let (contract, _) = source.split_once("} by {").unwrap();
    let expanded_source = format!("{contract}}} {expanded}");
    verify_c_sources(&expanded_source, &c).unwrap();
    let error =
        verify_c_sources(&source.replace("{ cell: first }", "{ cell: second }"), &c).unwrap_err();
    assert!(
        error.message().contains("does not match its contract"),
        "{}",
        error.message()
    );
    assert!(!error.message().contains("AlgebraicSchemas"));
    assert!(!error.message().contains("ResourceFieldSchema"));
    assert!(!error.message().contains("diagnostic truncated"));
    assert!(
        verify_c_sources(
            &source.replace(
                "ensures result == 1;",
                "ensures result == old(first.revision);"
            ),
            &c
        )
        .is_err()
    );
}

#[test]
fn named_resource_bindings_preserve_symbolic_fields_and_recheck_expansion() {
    let source = r#"verifying "identity.c";
        spec enum Mark { Clear, Set }
        resource marked_cell() {
            field model: Mark;
            field revision: int32;
            field contents: List<int32>;
        }
        int32 identity(int32 value) {
            owns cell: marked_cell();
            ensures result == value;
            ensures cell.model == old(cell.model);
            ensures cell.revision == old(cell.revision);
            ensures cell.contents == old(cell.contents);
            ensures list::length(cell.contents) == old(list::length(cell.contents));
        }
    "#;
    let sources = [(
        "identity.c",
        "int32 identity(int32 value) { return value; }",
    )];
    let verified = verify_c_sources(source, &sources).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    let expanded_source =
        source.replacen("by { step_until(function.exit); close(); }", &expanded, 1);
    verify_c_sources(&expanded_source, &sources)
        .expect("expanded resource-field proof must recheck");
    for false_claim in [
        "cell.model == Mark::Clear",
        "cell.revision == 0",
        "cell.contents == List::Nil",
    ] {
        let wrong = source.replace("cell.model == old(cell.model)", false_claim);
        assert!(
            verify_c_sources(&wrong, &sources).is_err(),
            "an arbitrary field cannot prove {false_claim}"
        );
    }
}

#[test]
fn named_resource_bindings_are_scoped_and_have_distinct_state() {
    let header = "spec enum Mark { Clear, Set } resource marked_cell() { field model: Mark; }";
    for body in [
        "int32 f() { owns cell: marked_cell(); owns cell: marked_cell(); }",
        "int32 f(int32 cell) { owns cell: marked_cell(); }",
        "int32 f() { owns cell: marked_cell(); ensures cell.missing == 0; }",
        "int32 f() { owns cell: marked_cell(); ensures cell->model == Mark::Clear; }",
        "abstract resource credit(); int32 f() { owns cell: credit(); }",
    ] {
        assert!(
            parser::parse(&format!("{header} {body}")).is_err(),
            "must reject {body}"
        );
    }
    let out_of_scope = format!(
        r#"verifying "g.c"; {header}
        extern int32 f() {{ owns cell: marked_cell(); }}
        int32 g() {{ ensures cell.model == Mark::Clear; }}"#
    );
    assert!(verify_c_sources(&out_of_scope, &[("g.c", "int32 g(void) { return 0; }")]).is_err());
    let source = format!(
        r#"verifying "f.c"; {header}
        int32 f() {{ owns first: marked_cell(); owns second: marked_cell();
            ensures first.model == second.model;
        }}"#
    );
    assert!(verify_c_sources(&source, &[("f.c", "int32 f(void) { return 0; }")]).is_err());
    let file = parser::parse(&source).unwrap();
    let function = &file.function_blocks()[0];
    let Requirement::Resource(ResourceClause::Named { binding: first, .. }) =
        &function.requires()[0]
    else {
        panic!("missing named binding")
    };
    let Requirement::Resource(ResourceClause::Named {
        binding: second, ..
    }) = &function.requires()[1]
    else {
        panic!("missing named binding")
    };
    assert_ne!(first.identity, second.identity);
    assert_ne!(first.fields, second.fields);
    let Ensure::Resource(ResourceClause::Named {
        binding: returned, ..
    }) = function.ensures()[0].ensure()
    else {
        panic!("missing returned instance")
    };
    assert_eq!(first.identity, returned.identity);
    assert!(
        first
            .fields
            .as_ref()
            .unwrap()
            .shares_storage_with(returned.fields.as_ref().unwrap())
    );
}

#[test]
fn named_resource_field_metadata_is_shared_at_multiple_sizes() {
    for size in [8, 32, 128, 512] {
        let fields = (0..size)
            .map(|i| format!("field f{i}: int32;"))
            .collect::<String>();
        let claims = (0..size)
            .map(|i| format!("ensures cell.f{i} == old(cell.f{i});"))
            .collect::<String>();
        let file = parser::parse(&format!(
            "resource record() {{ {fields} }} int32 f() {{ owns cell: record(); {claims} }}"
        ))
        .unwrap();
        let function = &file.function_blocks()[0];
        let Requirement::Resource(ResourceClause::Named { binding, .. }) = &function.requires()[0]
        else {
            panic!("missing instance")
        };
        let Ensure::Resource(ResourceClause::Named {
            binding: returned, ..
        }) = function.ensures()[0].ensure()
        else {
            panic!("missing returned instance")
        };
        assert_eq!(binding.fields.as_ref().unwrap().len(), size);
        assert!(
            binding
                .fields
                .as_ref()
                .unwrap()
                .shares_storage_with(returned.fields.as_ref().unwrap())
        );
        assert_eq!(function.ensures().len(), size + 1);
        for (i, ensure) in function.ensures()[1..].iter().enumerate() {
            let Ensure::Proposition(ClickProposition::Comparison {
                left: ContractExpression::ResourceField(access),
                ..
            }) = ensure.ensure()
            else {
                panic!("missing projected field")
            };
            assert_eq!(access.field_index, i);
        }
    }
}

/// Holding a resource with fields lets C read the memory its body owns
/// directly, as holding one without fields does. The read does not open the
/// resource: a store is still refused.
#[test]
fn named_resource_binding_grants_reads_of_its_memory_body_and_no_writes() {
    let contract = r#"verifying "cell.c";
        resource cell(p: int32*) { field model: List<int32>; owns p[0..1]; }
        int32 touch(int32* p) {
            owns cell: cell(p);
            ensures cell.model == old(cell.model);
        }
    "#;
    verify_c_sources(
        contract,
        &[("cell.c", "int32 touch(int32* p) { return *p; }")],
    )
    .expect("holding the instance authorizes a read of its body");
    let error = verify_c_sources(
        contract,
        &[("cell.c", "int32 touch(int32* p) { *p = 1; return 0; }")],
    )
    .expect_err("holding the instance folded does not authorize a store");
    assert!(
        error.message().contains("missing resource fact"),
        "{}",
        error.message()
    );
}

/// A call binds a callee's instance binder to the caller's instance without
/// a map when only one binding is possible. Two candidates are not chosen
/// between: the proof writes the map.
#[test]
fn a_call_binds_the_one_possible_instance_and_refuses_to_choose() {
    let c_source = "int32 callee(void); int32 caller(void) { return callee(); }";
    let unique = r#"verifying "calls.c";
        resource marker() { field revision: int32; }
        extern int32 callee() { owns cell: marker(); ensures cell.revision == old(cell.revision); }
        int32 caller() {
            owns cell: marker();
            ensures cell.revision == old(cell.revision);
        }
    "#;
    verify_c_sources(unique, &[("calls.c", c_source)])
        .expect("the caller owns exactly one instance the callee's binder can be");
    let ambiguous = r#"verifying "calls.c";
        resource marker() { field revision: int32; }
        extern int32 callee() { owns cell: marker(); ensures cell.revision == old(cell.revision); }
        int32 caller() {
            owns cell: marker();
            owns other: marker();
            ensures cell.revision == old(cell.revision);
        }
    "#;
    let error = verify_c_sources(ambiguous, &[("calls.c", c_source)]).unwrap_err();
    assert!(
        error.message().contains(
            "`callee` has an unbound instance binder `cell`; bind it in `step(..., { cell: instance })`"
        ),
        "{}",
        error.message()
    );
}

#[test]
fn resource_fields_preserve_checked_types_in_their_lowered_schema() {
    let file = parser::parse(
        r#"
        spec enum Mark { Clear, Set, }
        resource buffer(p: int32*) {
            field contents: List<List<int32>>;
            field mark: Mark;
            field revision: int32;
            field origin: int32*;
            owns p[0..1];
        }
        abstract resource credit();
    "#,
    )
    .unwrap();
    let buffer = &file.resource_definitions()[0];
    assert!(!buffer.is_fieldless());
    assert_eq!(
        buffer.fields().iter().map(|f| f.name()).collect::<Vec<_>>(),
        ["contents", "mark", "revision", "origin"]
    );
    let schema = buffer.field_schema().unwrap();
    assert!(!schema.is_fieldless());
    assert_eq!(schema.fields().len(), 4);
    let crate::kernel::ResourceFieldType::Algebraic(ty) = &schema.fields()[0].1 else {
        panic!("expected List schema")
    };
    assert_eq!(ty.name, "List");
    assert_eq!(
        ty.arguments,
        vec![AlgebraicValueType::Algebraic {
            name: "List".into(),
            arguments: vec![AlgebraicValueType::Program(ProgramType::Int32)],
        }]
    );
    assert_eq!(
        schema.fields()[2].1,
        crate::kernel::ResourceFieldType::Program(ProgramType::Int32)
    );
    assert_eq!(
        schema.fields()[3].1,
        crate::kernel::ResourceFieldType::Program(ProgramType::Int32Pointer)
    );
    assert!(file.resource_definitions()[1].is_fieldless());
    let lowered = composite_resource_definitions(
        &ResourceEnvironment::new(file.resource_definitions()),
        SpecDefinitions::new(
            &PredicateEnvironment::new(&[]),
            &ClickFunctionEnvironment::new(&[]),
        ),
    )
    .unwrap();
    assert_eq!(lowered.len(), 1);
    assert_eq!(
        lowered[0],
        lowered[0]
            .clone()
            .with_instance_schema(Some(schema.clone()))
    );
    assert_ne!(
        lowered[0],
        lowered[0].clone().with_instance_schema(None),
        "field metadata must never be erased from the lowered definition"
    );
}

#[test]
fn resource_fields_reject_counting_and_unimplemented_instance_operations() {
    let declaration = "resource cell(p: int32*) { field model: List<int32>; owns p[0..1]; }";
    // `cell` is not `authorized`, so a count of it is refused before its
    // fields matter; a quantity of a fielded family needs named members.
    let unauthorized = "`count` names `cell`, which is not an authorized family; declare it `authorized resource cell(...)`";
    let quantity = "resource `cell` has fields; quantities require separately named members";
    for expression in ["count(cell(p))", "List::Cons(count(cell(p)), List::Nil)"] {
        let result_type = if expression.starts_with("List") {
            "List<int32>"
        } else {
            "int32"
        };
        let source = format!(
            "function population(p: int32*) -> {result_type} {{ {expression} }} {declaration}"
        );
        assert_eq!(parser::parse(&source).unwrap_err().message(), unauthorized);
    }
    for (clause, expected) in [
        ("requires count(cell(p)) == 1;", unauthorized),
        ("requires count(cell(_)) == 1;", unauthorized),
        ("consumes 2 of cell(p);", quantity),
        ("produces 1 of cell(p);", quantity),
    ] {
        let source = format!("{declaration} int32 f(int32* p) {{ {clause} }}");
        let error = parser::parse(&source).unwrap_err();
        assert_eq!(error.message(), expected, "{clause}");
    }
    let nested = format!(
        "{declaration} abstract resource credit(n: int32); int32 f(int32* p) {{ consumes credit(count(cell(p))); }}"
    );
    assert_eq!(parser::parse(&nested).unwrap_err().message(), unauthorized);
    for tactic in ["apply(law(count(cell(p))));", "witness(count(cell(p)));"].into_iter() {
        let source =
            format!("{declaration} int32 f(int32* p) {{ ensures result == 0 by {{ {tactic} }} }}");
        assert_eq!(parser::parse(&source).unwrap_err().message(), unauthorized);
    }
    for clause in [
        "consumes cell(p);",
        "produces cell(p);",
        "owns cell(p);",
        "views cell(p);",
    ] {
        let source = format!("{declaration} int32 f(int32* p) {{ {clause} }}");
        let error = parser::parse(&source).unwrap_err();
        assert_eq!(
            error.message(),
            "resource `cell` has fields; bind it with `owns name: cell(...);`",
            "{clause}"
        );
    }
    for tactic in ["fold", "unfold", "observe"] {
        let source = format!(
            "{declaration} int32 f(int32* p) {{ ensures result == 0 by {{ {tactic}(cell(p)); }} }}"
        );
        let error = parser::parse(&source).unwrap_err();
        assert_eq!(
            error.message(),
            "resource `cell` has fields; bind it with `owns name: cell(...);`",
            "{tactic}"
        );
    }
}

#[test]
fn resource_fields_reject_invalid_declarations() {
    for (body, expected) in [
        (
            "field x: int32; field x: int32;",
            "duplicates a field or parameter name",
        ),
        ("field p: int32;", "duplicates a field or parameter name"),
        ("field x: Missing;", "unknown algebraic datatype"),
        ("field x: List;", "expects 1 type argument"),
        ("field x: List<Missing>;", "unknown algebraic datatype"),
        (
            "field x: void;",
            "requires an unqualified scalar, pointer, or algebraic Click type",
        ),
        (
            "owns p[0..1]; field x: int32;",
            "resource fields must be declared before body clauses",
        ),
        (
            "if p != 0 { field x: int32; }",
            "resource fields must be declared before body clauses",
        ),
    ] {
        let source = format!("resource cell(p: int32*) {{ {body} }}");
        let error = parser::parse(&source).unwrap_err();
        assert!(
            error.message().contains(expected),
            "{body}: {}",
            error.message()
        );
    }
}

#[test]
fn adt_resource_parameters_report_unsupported_types_without_panicking() {
    for declaration in [
        "resource marked_cell(p: int32*, mark: Mark) { owns p[0..1]; }",
        "abstract resource marked_cell(p: int32*, mark: Mark);",
    ] {
        let source = format!("spec enum Mark {{ Clear, Set, }}\n{declaration}");
        let error = parser::parse(&source).expect_err("ADT resource indices are not supported yet");
        assert_eq!(
            error.message(),
            "resource `marked_cell` parameter `mark` uses an algebraic type; algebraic resource arguments are not supported yet"
        );
    }
}

#[test]
fn modeled_binary_tree_laws_reject_wrong_mirror_and_size() {
    let example = include_str!("../../examples/modeled-binary-tree/modeled_binary_tree.click");
    // This regression is about the generic laws, independent of the C heap
    // resource and initializer contract that now precede them in the example.
    let source = &example[example.find("spec enum Tree<T>").unwrap()..];
    verify_c_sources(source, &[]).expect("generic tree laws should verify");
    for (from, to) in [("right", "left"), ("left", "right")] {
        let wrong_mirror = source.replacen(
            &format!("tree_mirror({from})"),
            &format!("tree_mirror({to})"),
            1,
        );
        assert!(
            verify_c_sources(&wrong_mirror, &[]).is_err(),
            "mirroring must not duplicate the {to} subtree"
        );
    }
    let wrong_size = source.replace(
        "ensures tree_size(tree_mirror(tree)) == tree_size(tree)",
        "ensures tree_size(tree_mirror(tree)) == Nat::Succ(tree_size(tree))",
    );
    assert!(verify_c_sources(&wrong_size, &[]).is_err());

    let client = format!(
        "{source}\n\
         theorem nested_payload(tree: Tree<List<int32>>) {{\n\
             ensures tree_mirror(tree_mirror(tree)) == tree by {{\n\
                 apply(tree_mirror_twice(tree));\n\
             }}\n\
             ensures tree_size(tree_mirror(tree)) == tree_size(tree) by {{\n\
                 apply(tree_mirror_preserves_size(tree));\n\
             }}\n\
         }}"
    );
    verify_c_sources(&client, &[]).expect("tree laws should apply to nested generic payloads");
}

const FILL3_C: &str = r#"
        int32 fill3(int32* p) {
            int32 i;
            i = 0;
            while (i < 3) {
                p[i] = i;
                i = i + 1;
            }
            return p[2];
        }
    "#;

const FILL3_CLICK: &str = r#"
        verifying "fill3.c";

        int32 fill3(int32* p) {
            requires viewable(p[0..3]);
            consumes p[0..3];
            ensures returns_second: result == 2;
        }
    "#;

fn current(expression: ProgramExpression) -> ContractExpression {
    ContractExpression::ProgramExpression(expression)
}

fn current_var(name: &str) -> ContractExpression {
    current(ProgramExpression::Variable((name.to_string()).into()))
}

fn current_int(value: u32) -> ContractExpression {
    ContractExpression::IntegerLiteral(value.to_string())
}

fn current_index(base: &str, index: u32) -> ContractExpression {
    ContractExpression::Index(Box::new(current_var(base)), Box::new(current_int(index)))
}

#[test]
fn contract_substitution_renames_colliding_logical_binders() {
    let proposition = ClickProposition::ForAll {
        click_type: ClickType::Program(InterfaceType::Int32),
        name: "i".to_string().into(),
        written_name: None,
        body: Box::new(ClickProposition::Comparison {
            left: current_var("argument"),
            operator: ComparisonOperator::Equal,
            right: current_var("i"),
        }),
    };
    let substitutions = BTreeMap::from([(String::from("argument"), current_var("i"))]);

    let substituted = lowering::substitute_click_proposition(&proposition, &substitutions)
        .expect("surface substitution should succeed");
    let ClickProposition::ForAll {
        name,
        written_name,
        body,
        ..
    } = substituted
    else {
        panic!("substitution should preserve the logical binder");
    };
    assert_ne!(name, "i");
    assert_eq!(written_name.as_deref(), Some("i"));
    assert_eq!(
        body.as_ref(),
        &ClickProposition::Comparison {
            left: current_var("i"),
            operator: ComparisonOperator::Equal,
            right: name.reference(),
        }
    );
}

#[test]
fn contract_substitution_renames_colliding_range_fold_and_let_binders() {
    let substitutions = BTreeMap::from([(String::from("argument"), current_var("i"))]);
    let fold = ContractExpression::RangeFold {
        start: Box::new(current_int(0)),
        end: Box::new(current_int(3)),
        initial: Box::new(current_int(0)),
        accumulator: "acc".to_string().into(),
        item: "i".to_string().into(),
        body: Box::new(ContractExpression::Add(
            Box::new(current_var("argument")),
            Box::new(current_var("i")),
        )),
    };
    let let_expression = ContractExpression::Let {
        name: "i".to_string().into(),
        click_type: Some(ClickType::Program(InterfaceType::Int32)),
        value: Box::new(current_int(0)),
        body: Box::new(ContractExpression::Add(
            Box::new(current_var("argument")),
            Box::new(current_var("i")),
        )),
    };

    let ContractExpression::RangeFold { item, body, .. } =
        lowering::substitute_contract_expression(&fold, &substitutions)
            .expect("range-fold substitution should succeed")
    else {
        panic!("substitution should preserve the range fold");
    };
    assert_ne!(item, "i");
    assert_eq!(
        body.as_ref(),
        &ContractExpression::Add(Box::new(current_var("i")), Box::new(item.reference()),)
    );

    let ContractExpression::Let { name, body, .. } =
        lowering::substitute_contract_expression(&let_expression, &substitutions)
            .expect("let substitution should succeed")
    else {
        panic!("substitution should preserve the let expression");
    };
    assert_ne!(name, "i");
    assert_eq!(
        body.as_ref(),
        &ContractExpression::Add(Box::new(current_var("i")), Box::new(name.reference()),)
    );
}

#[test]
fn integer_affine_fixed_execution_constant_weakening_expands_and_rechecks() {
    let source = r#"
verifying "integer_affine_fixed_execution.c";

int32 keep(int32 x, int32 y) {
    requires 0 <= to_integer(x) + to_integer(y);
    ensures weakened: -1 <= to_integer(x) + to_integer(y) by {
        step_until(function.exit);
        have -1 <= to_integer(x) + to_integer(y) by {
            close() using {
                0 <= to_integer(x) + to_integer(y);
            }
        }
        close();
    }
}
"#;
    let c_sources = [(
        "integer_affine_fixed_execution.c",
        "int32 keep(int32 x, int32 y) { return x; }",
    )];
    let verified_for_label = verify_c_sources(source, &c_sources)
        .expect("execution-context Integer weakening should verify");
    let expanded = expand_checked_function_claim(source, &verified_for_label, "keep.weakened")
        .expect("Integer weakening should expand to a checked certificate");
    verify_c_sources(&expanded, &c_sources)
        .expect("expanded execution-context Integer weakening should recheck");
}

#[test]
fn integer_affine_two_premise_constant_weakening_expands_and_rechecks() {
    let source = r#"
theorem integer_affine_two_premise_constant_weakening(x: Integer, y: Integer) {
    requires 0 <= x;
    requires 0 <= y;
    ensures -1 <= x + y by {
        close() using {
            0 <= x;
            0 <= y;
        }
    }
}
"#;
    verify_click_theorems(source)
        .expect("two Integer premises should lower through the surface mapper");
    let expanded = expand_c_claim_source_by_label(
        source,
        &[],
        "integer_affine_two_premise_constant_weakening.ensures_0",
    )
    .expect("two-premise Integer weakening should expand");
    verify_click_theorems(&expanded)
        .expect("expanded two-premise Integer weakening should recheck");
}

#[test]
fn integer_affine_fixed_execution_scaled_two_premise_lower_bound_expands_and_rechecks() {
    let source = r#"
verifying "integer_affine_fixed_scaled.c";

int32 fixed_c_params(int32 i, int32 total, int32 value) {
    requires -1000 * to_integer(i) - 1000 <= to_integer(total) + to_integer(value);
    requires to_integer(i) <= 1000;
    ensures bounded: -2147483648 <= to_integer(total) + to_integer(value) by {
        step_until(function.exit);
        have -2147483648 <= to_integer(total) + to_integer(value) by {
            close() using {
                -1000 * to_integer(i) - 1000 <= to_integer(total) + to_integer(value);
                to_integer(i) <= 1000;
            }
        }
        close();
    }
}
"#;
    let c_sources = [(
        "integer_affine_fixed_scaled.c",
        "int32 fixed_c_params(int32 i, int32 total, int32 value) { return total; }",
    )];
    let verified_for_label = verify_c_sources(source, &c_sources)
        .expect("fixed execution scaled lower bound should verify");
    let expanded =
        expand_checked_function_claim(source, &verified_for_label, "fixed_c_params.bounded")
            .expect("fixed execution scaled lower bound should expand");
    assert!(
        expanded.contains("click::integer::add_le"),
        "scaled lower bound expansion should contain ordinary composition: {expanded}"
    );
    verify_c_sources(&expanded, &c_sources)
        .expect("expanded fixed execution scaled lower bound should recheck");
}

fn old_index(base: &str, index: u32) -> ContractExpression {
    ContractExpression::Old(Box::new(current_index(base, index)))
}

fn ensure_comparison(
    left: ContractExpression,
    operator: ComparisonOperator,
    right: ContractExpression,
) -> Ensure {
    Ensure::Proposition(ClickProposition::Comparison {
        left,
        operator,
        right,
    })
}

// nextest starts a process per test, and each process that verifies anything
// parses the Click library first. A batch runs a few tests in one process so
// they share that immutable library syntax; each case runs on a fresh thread,
// which keeps the individual tests' thread-local isolation. Non-fast builds
// keep the original tests. A fast-gate individual case can still be selected
// explicitly with --ignored. See `docs/internals/testing.md`, "Batching short
// tests".
#[cfg(feature = "fast-gate")]
pub(super) fn run_test_batch(cases: &[(&str, fn())]) {
    for &(name, test) in cases {
        eprintln!("batched case {name} started");
        let started = std::time::Instant::now();
        let result = std::thread::Builder::new()
            .name(name.to_owned())
            .stack_size(8 * 1024 * 1024)
            .spawn(test)
            .expect("start batched case")
            .join();
        if let Err(panic) = result {
            eprintln!("batched case {name} FAILED");
            std::panic::resume_unwind(panic);
        }
        eprintln!(
            "batched case {name} passed in {:.3}s",
            started.elapsed().as_secs_f64()
        );
    }
}

/// Declares the batches of one test file. `file` is that file's name and
/// `marker` the text its batched tests carry in
/// `#[cfg_attr(feature = "fast-gate", ignore = "covered by <marker>NN")]`.
#[cfg(feature = "fast-gate")]
macro_rules! test_batches {
    (file: $file:literal, marker: $marker:literal, $($batch:ident: [$($case:ident),+ $(,)?]),+ $(,)?) => {
        $(
            #[test]
            fn $batch() {
                crate::surface::tests::run_test_batch(&[$((stringify!($case), $case)),+]);
            }
        )+

        #[test]
        fn batch_inventory_covers_each_ignored_case_once() {
            let registered = [$($(stringify!($case)),+),+];
            let actual = registered.into_iter().collect::<std::collections::BTreeSet<_>>();
            assert_eq!(actual.len(), registered.len(), "duplicate batched case");
            let annotation = concat!("ignore = \"covered by ", $marker);
            let mut marked = false;
            let mut expected = std::collections::BTreeSet::new();
            for line in include_str!($file).lines() {
                if line.contains(annotation) {
                    assert!(!marked, "batched-case annotation without a function");
                    marked = true;
                }
                if marked && let Some(name) = line.trim().strip_prefix("fn ") {
                    expected.insert(name.split('(').next().unwrap());
                    marked = false;
                }
            }
            assert!(!marked, "batched-case annotation without a function");
            assert_eq!(expected, actual, "batch coverage must match the skipped individual tests");
        }
    };
}

#[cfg(feature = "fast-gate")]
pub(super) use test_batches;

mod authority_private_body_tests;
mod authority_transfer_wrapper_tests;
mod back_edge_tests;
mod contract_closing_tests;
mod contract_tests;
mod diagnostic_tests;
mod execution_tests;
mod expansion_tests;
mod fold_body_tests;
mod loop_tests;
mod project_tests;
mod rust_literals;
mod rust_slice_functions;
#[path = "../scaling_tests/surface/tests/scaling_tests.rs"]
mod scaling_tests;
#[path = "../scaling_tests/surface/tests/step_shape_scaling_tests.rs"]
mod step_shape_scaling_tests;
mod surface_syntax;
mod tactic_call_syntax;
mod tactic_tests;
mod width_uniformity;

#[test]
fn integer_resource_fields_enforce_types_facts_and_states() {
    let c_source = "void change() { }";
    let source = r#"
        verifying "change.c";
        resource account() { field total: Integer; fact total >= 0; }
        void change() {
            owns model: account();
            requires model.total == 18446744073709551616;
            ensures model.total == 18446744073709551617;
            ensures old(model.total) == 18446744073709551616;
        } by {
            unfold(model);
            step_until(function.exit);
            let model = fold(account(), { total: 18446744073709551617 });
            close();
        }
    "#;
    verify_c_sources(source, &[("change.c", c_source)]).unwrap();
    for invalid in [
        source.replace("total: 18446744073709551617", "total: -1"),
        source.replace("total: 18446744073709551617", "total: 1u32"),
        source.replace(
            "ensures old(model.total) == 18446744073709551616",
            "ensures old(model.total) == 18446744073709551617",
        ),
        source.replace(
            "ensures model.total == 18446744073709551617",
            "ensures model.total == 18446744073709551616",
        ),
    ] {
        assert!(
            verify_c_sources(&invalid, &[("change.c", c_source)]).is_err(),
            "{invalid}"
        );
    }
    // Prove that the resource fact itself rejects a negative initializer,
    // independently of the postcondition's exact value.
    let negative = source
        .replace("total: 18446744073709551617", "total: -1")
        .replace("ensures model.total == 18446744073709551617;", "");
    assert!(verify_c_sources(&negative, &[("change.c", c_source)]).is_err());
    let expanded =
        expand_c_claim_source_by_label(source, &[("change.c", c_source)], "change.contract")
            .unwrap();
    verify_c_sources(&expanded, &[("change.c", c_source)]).unwrap();
}

#[test]
fn memory_free_pure_functions_are_classified_memory_independent() {
    let file = parser::parse(
        r#"
        spec enum Tree { Leaf, Node(int32*, Tree) }
        function identity_is(t: Tree, q: int32*) -> int32 {
            match t {
                Tree::Leaf => 1,
                Tree::Node(identity, sub) => if identity == q { 1 } else { 0 },
            }
        }
        function identity_is_twice(t: Tree, q: int32*) -> int32 {
            identity_is(t, q) + identity_is(t, q)
        }
        function head_is(p: int32*, x: int32) -> int32 {
            if p[0] == x { 1 } else { 0 }
        }
        function head_is_twice(p: int32*, x: int32) -> int32 {
            head_is(p, x) + head_is(p, x)
        }
    "#,
    )
    .unwrap();
    let environment = ClickFunctionEnvironment::new(file.click_function_definitions());
    // A predicate over payloads, and its caller, read nothing.
    assert!(environment.is_memory_independent("identity_is"));
    assert!(environment.is_memory_independent("identity_is_twice"));
    // Indexing a parameter reads memory, and so does calling something that does.
    assert!(!environment.is_memory_independent("head_is"));
    assert!(!environment.is_memory_independent("head_is_twice"));
    // An undeclared name is never assumed memory-free.
    assert!(!environment.is_memory_independent("absent"));
}

/// The surface lowering of each declared body is what the kernel's checked
/// read summary validates. Every pattern outside the subset declines the
/// whole definition; only the exact prefix-style folds are summarized.
/// Recursion is not writable here (a recursive pure function takes only
/// int32 parameters); the kernel test declines a recursive call directly.
#[test]
fn fold_read_summaries_are_checked_from_the_lowered_declarations() {
    let file = parser::parse(
        r#"
        function unmarked(v: int32[], lo: int32, hi: int32) -> Integer {
            (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
        }
        function arms(v: int32[], lo: int32, hi: int32) -> Integer {
            (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { v[k] } else { v[k] }) })
        }
        function shifted(v: int32[], lo: int32, hi: int32) -> Integer {
            (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k + 1] == 0 { 1 } else { 0 }) })
        }
        function chased(v: int32[], lo: int32, hi: int32) -> Integer {
            (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[v[k]] == 0 { 1 } else { 0 }) })
        }
        function peek_end(v: int32[], lo: int32, hi: int32) -> Integer {
            (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { v[hi] } else { 0 }) })
        }
        function helper(v: int32[], k: int32) -> Integer {
            to_integer(v[k])
        }
        function helped(v: int32[], lo: int32, hi: int32) -> Integer {
            (lo..hi).fold(0, |acc, k| { acc + helper(v, k) })
        }
        function nested(v: int32[], lo: int32, hi: int32) -> Integer {
            (lo..hi).fold(0, |acc, k| { acc + unmarked(v, lo, k) })
        }
        function read_end(v: int32[], lo: int32, hi: int32) -> Integer {
            (lo..v[0]).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
        }
        function read_initial(v: int32[], lo: int32, hi: int32) -> Integer {
            (lo..hi).fold(to_integer(v[lo]), |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
        }
    "#,
    )
    .unwrap();
    let environment = ClickFunctionEnvironment::new(file.click_function_definitions());
    let _session = crate::kernel::VerificationSession::enter();
    register_kernel_fold_read_definitions(
        SpecDefinitions::new(&PredicateEnvironment::new(&[]), &environment),
        &BTreeMap::new(),
    );
    let summarized = crate::kernel::registered_fold_read_summary;
    assert!(
        summarized("unmarked").is_ok(),
        "{:?}",
        summarized("unmarked")
    );
    assert!(summarized("arms").is_ok(), "{:?}", summarized("arms"));
    for (name, decline) in [
        ("shifted", "ReadOutsideFoldIndex"),
        ("chased", "ReadOutsideFoldIndex"),
        ("peek_end", "ReadOutsideFoldIndex"),
        ("helper", "NotATopLevelInt32Fold"),
        ("helped", "UnsupportedConstruct(\"a function call\")"),
        ("nested", "UnsupportedConstruct(\"a function call\")"),
        ("read_end", "UnsupportedEndpoint"),
        (
            "read_initial",
            "UnsupportedInitialValue(\"it reads the array\")",
        ),
    ] {
        assert_eq!(
            format!("{:?}", summarized(name)),
            format!("Err(Declined({decline}))"),
            "`{name}` must decline its whole definition"
        );
    }
}

#[test]
fn integer_resource_field_observes_unchanged_memory_read() {
    let c_source = "int32 read(int32* p) { return *p; }";
    let source = r#"
        verifying "read.c";
        resource cell(p: int32*) {
            field value: Integer;
            owns p[0..1];
            fact to_integer(p[0]) == value;
        }
        int32 read(int32* p) {
            owns model: cell(p);
            ensures to_integer(result) == model.value;
            ensures model.value == old(model.value);
        } by {
            unfold(model);
            step_until(function.exit);
            let model = fold(cell(p), { value: old(model.value) });
            close();
        }
    "#;
    verify_c_sources(source, &[("read.c", c_source)]).unwrap();
}

#[test]
fn automatic_scope_exit_preserves_expanded_execution() {
    let c = "int32 f(int32 n) { if (n == 0) { int32 a[2]; a[0] = 5; return a[0]; } else { int32 b[2]; b[0] = 5; return b[0]; } }";
    let source = r#"verifying "scope.c"; int32 f(int32 n) { ensures result == 5; } by { if n == 0 { step_until(function.exit); } else { step_until(function.exit); } }"#;
    let inputs = [("scope.c", c)];
    let verified_for_expansion = verify_c_sources(source, &inputs).unwrap();
    let expanded = expand_checked_grouped_claim(source, &verified_for_expansion, "f").unwrap();
    verify_c_sources(&expanded, &inputs).unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn bounded_population_increment_expands_and_checks() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/population_symbolic_increment_bounded.md");
    // The Markdown loader carries its explicit resource semantics through
    // verification, expansion, and certificate verification.
    let loaded = crate::cli::load_target_inputs(&path, None).unwrap();
    let fixture = loaded.mdtest.as_ref().unwrap();
    let project = &loaded.project;
    let inputs = fixture
        .c_sources
        .iter()
        .map(|(name, body)| (name.as_str(), body.as_str()))
        .collect::<Vec<_>>();
    verify_c_project(project, &inputs).unwrap();
    let expanded = expand_project_claim_source_by_label(
        project,
        &ProgramInputs::Bundle(inputs.to_vec()),
        "increment.contract",
    )
    .unwrap();
    verify_c_project(&project.with_entry_source(expanded), &inputs).unwrap();
}

#[test]
fn aggregate_parameter_values_expand_and_check() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/aggregate_parameter_value_fields.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let inputs = fixture
        .c_sources
        .iter()
        .map(|(name, body)| (name.as_str(), body.as_str()))
        .collect::<Vec<_>>();
    let verified_for_expansion = verify_c_sources(source, &inputs).unwrap();
    for (_, expanded) in
        expand_checked_grouped_claims(source, &verified_for_expansion, ["nested", "copy"])
    {
        verify_c_sources(&expanded, &inputs).unwrap();
    }
}

#[test]
fn aggregate_parameter_symbolic_index_expands_and_checks() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/aggregate_parameter_symbolic_index.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let inputs = fixture
        .c_sources
        .iter()
        .map(|(name, body)| (name.as_str(), body.as_str()))
        .collect::<Vec<_>>();
    let verified_for_expansion = verify_c_sources(source, &inputs).unwrap();
    let expanded =
        expand_checked_grouped_claim(source, &verified_for_expansion, "indexed").unwrap();
    verify_c_sources(&expanded, &inputs).unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn resource_contract_regressions_expand_and_check() {
    for (fixture_name, function_name) in [
        ("aggregate_parameter_pointee_contract", "touch"),
        ("aggregate_parameter_pointee_resource", "touch"),
        ("aggregate_parameter_old_pointee", "dispose"),
        ("const_callback_table_abstract", "caller"),
        ("separation_span_bounded_goal", "identity"),
        ("separation_span_assumption", "identity"),
        ("separation_span_call", "caller"),
        ("separation_span_borrowed_call", "caller"),
        ("separation_span_composite_bounds", "length"),
        ("separation_span_composite_split_bounds", "split_length"),
        ("owned_symbolic_separation_certificate", "attach"),
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join(format!("mdtests/{fixture_name}.md"));
        let fixture = crate::cli::read_mdtest(&path).unwrap();
        let source = fixture.click_source.as_deref().unwrap();
        let inputs = fixture
            .c_sources
            .iter()
            .map(|(name, body)| (name.as_str(), body.as_str()))
            .collect::<Vec<_>>();
        let verified_for_expansion = verify_c_sources(source, &inputs).unwrap();
        let expanded =
            expand_checked_grouped_claim(source, &verified_for_expansion, function_name).unwrap();
        verify_c_sources(&expanded, &inputs)
            .unwrap_or_else(|error| panic!("{error:?}\n{expanded}"));
    }
}
#[test]
fn reports_syntax_and_type_failures_separately() {
    let syntax = parser::parse("theorem").unwrap_err();
    assert_eq!(syntax.kind(), ClickErrorKind::Syntax);
    assert!(syntax.report().contains("error kind: syntax error"));

    let type_error = verify_c_sources(
        "verifying \"f.c\"; int32 read(const int32 *p) { ensures result == 0; }",
        &[("f.c", "int32 read(int32 *p) { return p[0]; }")],
    )
    .unwrap_err();
    assert_eq!(type_error.kind(), ClickErrorKind::Type);
    assert!(type_error.report().contains("error kind: type error"));

    let internal = ClickError::new("broken verifier invariant")
        .with_kind(ClickErrorKind::Internal)
        .with_kind(ClickErrorKind::Type);
    assert_eq!(internal.kind(), ClickErrorKind::Internal);
    assert!(internal.report().contains("error kind: internal error"));
    assert_eq!(
        ClickError::new("kernel rejected: internal error while checking a rewrite").kind(),
        ClickErrorKind::Internal
    );
}

#[test]
fn resource_parameters_are_references_separate_from_ownership() {
    let source = r#"
        resource marker(p: int32*) { field revision: int32; }
        resource wrapper(p: int32*, cell: marker(p)) { field stamp: int32; }
        int32 use(int32* p) {
            owns cell: marker(p);
            owns wrapped: wrapper(p, cell);
            ensures result == 0;
        }
    "#;
    let file = parser::parse(source).unwrap();
    let wrapper = &file.resource_definitions()[1];
    assert_eq!(wrapper.parameters().len(), 1);
    assert_eq!(wrapper.resource_parameters().len(), 1);
    assert!(wrapper.composite_body().unwrap().contains().is_empty());
    let ResourceClause::Named {
        binding: formal, ..
    } = &wrapper.resource_parameters()[0]
    else {
        panic!()
    };
    assert_eq!(formal.name, "cell");
    let owns_body = source.replace(
        "field stamp: int32;",
        "field stamp: int32; owns cell; fact cell.revision == stamp;",
    );
    let owned = parser::parse(&owns_body).unwrap();
    let ResourceClause::Named { binding, .. } = &owned.resource_definitions()[1]
        .composite_body()
        .unwrap()
        .contains()[0]
    else {
        panic!()
    };
    assert_eq!(binding.identity, formal.identity);

    for invalid in [
        source.replace(
            "cell: marker(p)) { field stamp",
            "cell: marker(p), n: int32) { field stamp",
        ),
        source.replace(
            "cell: marker(p)) { field stamp",
            "cell: marker(p), cell: marker(p)) { field stamp",
        ),
        source.replace("wrapper(p, cell)", "wrapper(p, missing)"),
        source.replace(
            "cell: marker(p)) { field stamp",
            "p: marker(p)) { field stamp",
        ),
        source.replace("field stamp: int32;", ""),
    ] {
        assert!(parser::parse(&invalid).is_err(), "accepted {invalid}");
    }
}

#[test]
fn mutex_use_accepts_resource_type_without_owned_instance() {
    let source = r#"
        resource counter_state(p: int32*) { field value: int32; }
        void worker(int32* mu, int32* p) {
            owns access: mutex_use(mu, counter_state(p));
        }
    "#;
    let file = parser::parse(source).unwrap();
    let Requirement::Resource(resource) = &file.function_blocks()[0].requires()[0] else {
        panic!()
    };
    assert_eq!(
        crate::surface::validation::describe_resource_clause(resource),
        "access: mutex_use(mu, counter_state(p))"
    );
    let ResourceClause::Named { resource, .. } = resource else {
        panic!()
    };
    let ResourceClause::Declared {
        resource_type_arguments,
        ..
    } = resource.as_ref()
    else {
        panic!()
    };
    let [
        ResourceClause::Declared {
            name,
            type_schema: Some(schema),
            ..
        },
    ] = resource_type_arguments.as_slice()
    else {
        panic!()
    };
    assert_eq!(name, "counter_state");
    assert_eq!(schema.fields().len(), 1);
}

#[test]
fn mutex_use_resource_type_checks_its_dependent_argument() {
    let source = r#"
        resource counter_state(p: int32*) { field value: int32; }
        void worker(int32* mu) {
            owns access: mutex_use(mu, counter_state(1));
        }
    "#;
    let error = parser::parse(source).unwrap_err();
    assert!(
        error.message().contains("counter_state"),
        "{}",
        error.message()
    );
    assert!(
        error.message().contains("argument 0"),
        "{}",
        error.message()
    );
}

mod authority_conditional_release_tests;

#[test]
fn step_output_patterns_reject_ambiguous_and_conflicting_bindings() {
    let source = r#"
        resource Counter() { field value: int32; }
        int32 scalar() { ensures result == 1; }
        int32 make() { produces made: Counter(); ensures result == 1; }
        void caller(int32 occupied) { ensures occupied == occupied; } by { OUTPUT }
    "#;
    for (output, expected) in [
        (
            "let value = step(scalar);",
            "step outputs require named bindings",
        ),
        (
            "let value = step(make);",
            "step outputs require named bindings",
        ),
        ("let value = step();", "step outputs require named bindings"),
        (
            "let { result: a, result: b } = step(scalar);",
            "duplicate output key",
        ),
        (
            "let { result: a, made: a } = step(make);",
            "introduces name `a` twice",
        ),
        (
            "let { result: a } = step(make);",
            "omits produced resource binder",
        ),
        (
            "let { unknown: a } = step(scalar);",
            "does not produce named resource",
        ),
        ("let { made: a } = step();", "only the `result` output"),
    ] {
        let error = parser::parse(&source.replace("OUTPUT", output))
            .expect_err(&format!("{output} should be rejected"));
        assert!(error.message.contains(expected), "{output}: {error:?}");
    }
}

#[test]
fn named_contract_output_patterns_round_trip_and_check_binders() {
    let source = r#"
        resource Dirty(p: int32*) { field value: int32; }
        resource Ready(p: int32*) { field value: int32; }
        contract int32 Repair(int32* p) {
            consumes input: Dirty(p);
            produces output: Ready(p);
            ensures output.value == 1;
            ensures result == 0;
        }
        void caller(int32* q) { consumes dirty: Dirty(q); produces done: Ready(q); }
        by { let { result: status, output: done } = step(Repair, { input: dirty }); }
    "#;
    let file = parser::parse(source).unwrap();
    let SourceProof::Script(tactics) = file.function_blocks()[0].grouped_proof().unwrap() else {
        panic!("expected script")
    };
    let ProofTactic::StepCall(transport) = &tactics[0] else {
        panic!("expected named transport")
    };
    assert!(transport.is_named_contract());
    assert!(transport.arguments().is_empty());
    assert_eq!(transport.result(), Some("status"));
    let printed = printing::format_proof_tactics(tactics).unwrap();
    assert!(printed.contains("step(Repair, { input: dirty })"));
    assert!(
        parser::parse(&format!(
            "{}{}",
            source.split("by {").next().unwrap(),
            printed
        ))
        .is_ok()
    );
    for (old, new) in [
        ("input: dirty", "missing: dirty"),
        ("input: dirty", "input: dirty, input: dirty"),
        ("input: dirty", ""),
        ("output: done", "missing: done"),
        ("result: status, output: done", "result: status"),
        ("result: status, output: done", "output: done, result: done"),
        ("step(Repair,", "step(Unknown,"),
    ] {
        assert!(
            parser::parse(&source.replace(old, new)).is_err(),
            "must reject {new}"
        );
    }
}

mod resource_parameters;

mod preservation;

#[test]
fn solve_folds_returned_instances_and_expands_to_explicit_folds() {
    let match_body = "by { unfold(c); step_until(function.exit); close(); }";
    let guarded_body = "by { if p == 0 { unfold(c); step_until(function.exit); close(); } else { unfold(c); step_until(function.exit); close(); } }";
    for (source, body, c) in [
        (
            MATCH_CELL_SOURCE.replace(
                "by { unfold(c); step_until(function.exit); fold(c); close(); }",
                match_body,
            ),
            match_body,
            "int32 read(int32* p, int32 expected) { return *p; }",
        ),
        (
            GUARDED_CELL_SOURCE.replace("by { BODY }", guarded_body),
            guarded_body,
            GUARDED_CELL_C,
        ),
    ] {
        let sources = [("read.c", c)];
        let verified = verify_c_sources(&source, &sources).unwrap();
        let expanded = verified[0].expanded_proof_source().unwrap();
        assert!(expanded.contains("fold("), "{expanded}");
        crate::surface::proof::without_implicit_solve(|| {
            verify_c_sources(&source.replace(body, &expanded), &sources)
        })
        .unwrap();
    }
}
