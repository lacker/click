use super::diagnostics::describe_contract_expression;
use super::*;
use crate::kernel::{AlgebraicValueType, int32};

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
        "unfold(root); unfold(root.tail); execute(); fold(root.tail); fold(root); simp();",
        "unfold(root); have root.tail.model == Chain::End by { simp(); } unfold(root.tail); fold(root.tail); fold(root); unfold(root); execute(); fold(root); simp();",
    ] {
        let source = RECURSIVE_CHILD_SOURCE.replace("BODY", body);
        let verified = verify_c0_sources(&source, &c).unwrap();
        verify_c0_sources(
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
fn recursive_child_resources_deep_paths_own_memory_and_recheck() {
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
    let body = "unfold(root); unfold(root.tail); unfold(root.tail.tail); have root.tail.tail.model == Nonempty::Last(9) by { simp(); } execute(); fold(root.tail.tail); fold(root.tail); fold(root); simp();";
    let c = [(
        "middle.c",
        "int32 middle(int32* p, int32* q, int32* r) { return *q; }",
    )];
    let source = source.replace("BODY", body);
    let verified = verify_c0_sources(&source, &c).unwrap();
    verify_c0_sources(
        &source.replace(
            &format!("by {{ {body} }}"),
            &verified[0].expanded_proof_source().unwrap(),
        ),
        &c,
    )
    .unwrap();
    assert!(
        verify_c0_sources(
            &source.replace(body, "unfold(root); execute(); fold(root); simp();"),
            &c
        )
        .is_err()
    );
    assert!(verify_c0_sources(&source.replace("result == 8", "result == 9"), &c).is_err());
}

#[test]
fn recursive_child_resources_do_not_capture_earlier_function_names() {
    let source = RECURSIVE_CHILD_SOURCE
        .replace(
            "BODY",
            "unfold(root); unfold(root.root); execute(); fold(root.root); fold(root); simp();",
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
    verify_c0_sources(
        &reordered,
        &[(
            "read.c",
            "int32 read(int32* p, int32* next, int32 value) { return *p; }",
        )],
    )
    .unwrap();
}

#[test]
fn recursive_child_resources_reject_bad_lifetimes_and_folds() {
    let c = [(
        "read.c",
        "int32 read(int32* p, int32* next, int32 value) { return *p; }",
    )];
    for body in [
        "unfold(root.tail); execute(); simp();",
        "unfold(root); unfold(root.tail); execute(); fold(root); simp();",
        "unfold(root); unfold(root.tail); unfold(root.tail); execute(); fold(root.tail); fold(root); simp();",
        "unfold(root); execute(); fold(root.tail); fold(root); simp();",
        "unfold(root); execute(); fold(root); unfold(root.tail); simp();",
        "unfold(root); unfold(root.missing); execute(); fold(root); simp();",
        "unfold(root); unfold(root.tail.tail); execute(); fold(root); simp();",
    ] {
        let source = RECURSIVE_CHILD_SOURCE.replace("BODY", body);
        assert!(verify_c0_sources(&source, &c).is_err(), "accepted {body}");
    }
    let source =
        RECURSIVE_CHILD_SOURCE.replace("BODY", "unfold(root); execute(); fold(root); simp();");
    let changed = [(
        "read.c",
        "int32 read(int32* p, int32* next, int32 value) { *p = 0; return *p; }",
    )];
    assert!(verify_c0_sources(&source, &changed).is_err());
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
fn algebraic_pointer_constructor_null_literal_is_explicitly_unsupported() {
    let error =
        parser::parse("spec enum Ptr { At(int32*) } function null_ptr() -> Ptr { Ptr::At(0) }")
            .unwrap_err();
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
} by { unfold(c); execute(); fold(c); simp(); }
"#;

#[test]
fn resource_match_expands_and_rechecks() {
    let c = [(
        "read.c",
        "int32 read(int32* p, int32 expected) { return *p; }",
    )];
    let verified = verify_c0_sources(MATCH_CELL_SOURCE, &c).unwrap();
    verify_c0_sources(
        &MATCH_CELL_SOURCE.replace(
            "by { unfold(c); execute(); fold(c); simp(); }",
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
        ("fold(c); simp();", "simp();"),
        ("fold(c); simp();", "fold(c); fold(c); simp();"),
        ("result == expected", "result == 42"),
    ] {
        assert!(
            verify_c0_sources(&MATCH_CELL_SOURCE.replace(from, to), &c).is_err(),
            "accepted {from} -> {to}"
        );
    }
    let changed = [(
        "read.c",
        "int32 read(int32* p, int32 expected) { *p = 0; return *p; }",
    )];
    assert!(verify_c0_sources(MATCH_CELL_SOURCE, &changed).is_err());
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
        } by { unfold(c); execute(); fold(c); simp(); }
    "#;
    let c = [(
        "read.c",
        "int32 read(int32* p, int32 expected) { return *p; }",
    )];
    verify_c0_sources(source, &c).unwrap();
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
        );
    let verified = verify_c0_sources(&nested, &c).unwrap();
    verify_c0_sources(
        &nested.replace(
            "by { unfold(c); execute(); fold(c); simp(); }",
            &verified[0].expanded_proof_source().unwrap(),
        ),
        &c,
    )
    .unwrap();
}

#[test]
fn instance_return_folds_follow_distinct_c_results_without_proof_branching() {
    let source = r#"verifying "read.c";
        resource cell(p: int32*) {
            field value: int32;
            owns p[0..1]; fact p[0] == value;
        }
        int32 read(int32* p, int32 fallback, int32 use_value) {
            owns c: cell(p);
            ensures (use_value == 0 and result == fallback) or (use_value != 0 and result == c.value);
            ensures c.value == old(c.value);
        } by { unfold(c); execute(); fold(c); simp(); }
    "#;
    let c = [(
        "read.c",
        "int32 read(int32* p, int32 fallback, int32 use_value) { if (use_value == 0) return fallback; return *p; }",
    )];
    let verified = verify_c0_sources(source, &c).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    verify_c0_sources(
        &source.replace("by { unfold(c); execute(); fold(c); simp(); }", &expanded),
        &c,
    )
    .unwrap();
    assert!(
        verify_c0_sources(
            &source.replace("result == fallback", "result == c.value"),
            &c
        )
        .is_err()
    );
    let body = "by { unfold(c); execute(); if use_value == 0 { fold(c); simp(); } else { fold(c); simp(); } }";
    let branched = source.replace("by { unfold(c); execute(); fold(c); simp(); }", body);
    let verified = verify_c0_sources(&branched, &c).unwrap();
    verify_c0_sources(
        &branched.replace(body, &verified[0].expanded_proof_source().unwrap()),
        &c,
    )
    .unwrap();
}

#[test]
fn guarded_instance_return_paths_expand_and_recheck() {
    let body = "if p == 0 { unfold(c); execute(); fold(c); simp(); } else { unfold(c); execute(); fold(c); simp(); }";
    let source = GUARDED_CELL_SOURCE.replace("BODY", body);
    let c = [("read.c", GUARDED_CELL_C)];
    let verified = verify_c0_sources(&source, &c).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    verify_c0_sources(&source.replace(&format!("by {{ {body} }}"), &expanded), &c).unwrap();
}

#[test]
fn guarded_instance_return_paths_reject_invalid_folds() {
    for body in [
        "unfold(c); execute(); fold(c); simp();",
        "if p == 0 { unfold(c); execute(); simp(); } else { unfold(c); execute(); fold(c); simp(); }",
        "if p == 0 { unfold(c); execute(); fold(c); simp(); } else { unfold(c); execute(); simp(); }",
        "if p == 0 { unfold(c); execute(); fold(c); fold(c); simp(); } else { unfold(c); execute(); fold(c); simp(); }",
    ] {
        assert!(
            verify_c0_sources(
                &GUARDED_CELL_SOURCE.replace("BODY", body),
                &[("read.c", GUARDED_CELL_C)]
            )
            .is_err(),
            "accepted {body}"
        );
    }
    // A body fact exposed only on the nonnull arm cannot justify the null result.
    let body = "if p == 0 { unfold(c); execute(); fold(c); simp(); } else { unfold(c); execute(); fold(c); simp(); }";
    let source = GUARDED_CELL_SOURCE.replace("BODY", body);
    assert!(
        verify_c0_sources(
            &source.replace("p == 0 or result == c.value", "result == c.value"),
            &[("read.c", GUARDED_CELL_C)]
        )
        .is_err()
    );
    // Only one branch changes memory: the other branch's valid fold cannot
    // certify this return's stale field relation.
    let changed = "int32 read(int32* p) { if (p == 0) return 0; *p = 0; return *p; }";
    assert!(verify_c0_sources(&source, &[("read.c", changed)]).is_err());
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
        } by { unfold(c); execute(); fold(c); simp(); }
    "#;
    let c = [("read.c", "int32 read(int32* p) { return *p; }")];
    let verified = verify_c0_sources(source, &c).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    verify_c0_sources(
        &source.replace("by { unfold(c); execute(); fold(c); simp(); }", &expanded),
        &c,
    )
    .unwrap();
}

#[test]
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
            execute();
            let c = fold(cell(p), { model: INITIALIZER });
            simp();
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
        verify_c0_sources(&source, &sources).unwrap();
        let expanded =
            expand_c0_claim_source(&source, &sources, "init", CProofClaim::Grouped).unwrap();
        verify_c0_sources(&expanded, &sources).unwrap();
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
            execute();
            let c = fold(cell(p), { model: INITIALIZER });
            simp();
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
            verify_c0_sources(&source.replace("INITIALIZER", initializer), &sources).is_err(),
            "accepted {initializer}"
        );
    }
    let update = source
        .replace(
            "consumes p[0..1];\n            produces c: cell(p);",
            "owns c: cell(p);",
        )
        .replace("execute();", "unfold(c); execute();");
    for initializer in ["c.model", "old(c.model)"] {
        assert!(
            verify_c0_sources(&update.replace("INITIALIZER", initializer), &sources).is_err(),
            "accepted stale {initializer}"
        );
    }
    // An unconstrained field must not hide an invalid read either.
    let unconstrained = source.replace("fact model == Mark::Set(p[0]);", "");
    assert!(
        verify_c0_sources(
            &unconstrained.replace("INITIALIZER", "Mark::Set(q[0])"),
            &sources
        )
        .is_err()
    );
    let scalar = unconstrained.replace("field model: Mark;", "field model: int32;");
    assert!(verify_c0_sources(&scalar.replace("INITIALIZER", "q[0]"), &sources).is_err());
}

#[test]
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
            execute();
            simp();
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
        verify_c0_sources(&source, &sources).unwrap_or_else(|error| panic!("{value}: {error:?}"));
        let expanded =
            expand_c0_claim_source(&source, &sources, "preserve", CProofClaim::Grouped).unwrap();
        verify_c0_sources(&expanded, &sources)
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
    verify_c0_sources(&changed, &sources).unwrap();
    let expanded =
        expand_c0_claim_source(&changed, &sources, "preserve", CProofClaim::Grouped).unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
    assert!(
        verify_c0_sources(
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
            execute();
            let c = fold(cell(p), { value: value });
            simp();
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
            .replace("execute();", "unfold(c); execute();"),
    ] {
        verify_c0_sources(&source, &sources).unwrap();
        let expanded =
            expand_c0_claim_source(&source, &sources, "init", CProofClaim::Grouped).unwrap();
        assert!(expanded.contains("let c = fold("), "{expanded}");
        verify_c0_sources(&expanded, &sources).unwrap();
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
        } by { execute(); FOLD simp(); }
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
        "let c = fold(cell(p), { value: value }); unfold(c);",
    ] {
        assert!(
            verify_c0_sources(&source.replace("FOLD", fold), &sources).is_err(),
            "accepted {fold}"
        );
    }
    let no_ownership = source
        .replace("consumes p[0..1];", "")
        .replace("execute();", "")
        .replace("FOLD", "let c = fold(cell(p), { value: value });");
    assert!(verify_c0_sources(&no_ownership, &sources).is_err());
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
            execute();
            simp();
        }
    "#;
    let sources = [("cell.c", "void set(int32* p, int32 value) { *p = value; }")];
    verify_c0_sources(source, &sources).unwrap();
    let expanded = expand_c0_claim_source(source, &sources, "set", CProofClaim::Grouped).unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
    for stale in [
        source.replace("ensures c.revision == 2;", "ensures c.revision == 1;"),
        source.replace("ensures c.value == value;", "ensures c.value == 7;"),
    ] {
        assert!(
            verify_c0_sources(&stale, &sources).is_err(),
            "entry fields must not be reused as current fields after an update"
        );
    }
    let invalid = source.replacen(
        "unfold(c);",
        "unfold(c); have c.value == c.value by { reflexivity(); }",
        1,
    );
    assert!(
        verify_c0_sources(&invalid, &sources).is_err(),
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
            "fold(c); execute(); simp();",
            "int32 read(int32* p) { return *p; }",
        ),
        (
            "unfold(c); unfold(c); execute(); fold(c); simp();",
            "int32 read(int32* p) { return *p; }",
        ),
        (
            "unfold(c); execute(); fold(c); fold(c); simp();",
            "int32 read(int32* p) { return *p; }",
        ),
        ("execute(); simp();", "int32 read(int32* p) { return *p; }"),
        (
            "unfold(c); execute(); simp();",
            "int32 read(int32* p) { return *p; }",
        ),
        (
            "unfold(c); execute(); fold(c); simp();",
            "int32 read(int32* p) { *p = 0; return *p; }",
        ),
    ] {
        let error = verify_c0_sources(&source.replace("BODY", body), &[("read.c", c)])
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
            execute(); rewrite(x == 1);
            have result == 1 by { rewrite(x == 1); normalize(); }
            assumption();
        }
    "#;
    let c = [("identity.c", "int32 identity(int32 x) { return x; }")];
    verify_c0_sources(source, &c).unwrap();
    assert!(
        verify_c0_sources(
            &source.replace("ensures result == 1;", "ensures result == 2;"),
            &c
        )
        .is_err()
    );
    assert!(
        verify_c0_sources(
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
        contract Touch(cell: marker()) for int32() {
            owns cell;
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
        } by { step(Touch(first)); execute(); simp(); }
    "#;
    let c = [(
        "invoke.c",
        "int32 invoke(int32 (*callback)()) { return callback(); }",
    )];
    let verified = verify_c0_sources(source, &c).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    assert!(expanded.contains("step(Touch(first));"));
    verify_c0_sources(
        &source.replace("by { step(Touch(first)); execute(); simp(); }", &expanded),
        &c,
    )
    .unwrap();
    for bad in [
        source.replace(
            "ensures first.revision == 1;",
            "ensures first.revision == old(first.revision);",
        ),
        source.replace("ensures cell.model == old(cell.model);", ""),
        source.replace("Touch(first)", "Touch(second)"),
    ] {
        assert!(verify_c0_sources(&bad, &c).is_err());
    }
}

#[test]
fn explicit_contract_parameters_are_declared_not_implicit_ownership() {
    let file = parser::parse(
        r#"
        resource marker(p: int32*) { field revision: int32; }
        contract Read(cell: marker(p)) for int32(int32* p) {
            owns cell;
            ensures cell.revision == old(cell.revision);
        }
        contract Unowned(cell: marker(p)) for int32(int32* p) { ensures result == 0; }
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
    assert!(
        file.contract_definitions()[1]
            .function_block()
            .requires()
            .is_empty()
    );
    let header = "resource marker(p: int32*) { field revision: int32; }";
    for invalid in [
        "contract C(cell: marker(p), cell: marker(p)) for int32(int32* p) {}",
        "contract C(cell: marker(p), cell) for int32(int32* p) {}",
        "contract C(p: marker(p)) for int32(int32* p) {}",
        "contract C(cell: marker(0)) for int32() {}",
        "contract C(cell: missing()) for int32() {}",
        "contract C(cell: marker(p) = other) for int32(int32* p) {}",
        "contract C() for int32(int32* p) { owns hidden: marker(p); }",
        "contract C(cell: marker(p)) for int32(int32* p) { owns cell; owns cell; }",
    ] {
        let invalid = invalid.replace("{}", "{ ensures result == 0; }");
        assert!(
            parser::parse(&format!("{header} {invalid}")).is_err(),
            "must reject {invalid}"
        );
    }
}

#[test]
fn explicit_contract_applications_preserve_arguments_when_printed() {
    let source = r#"
        resource marker() { field revision: int32; }
        contract Touch(cell: marker()) for int32() { owns cell; }
        int32 f() { owns first: marker(); owns second: marker(); }
        by { step(Touch(second)); }
    "#;
    let file = parser::parse(source).unwrap();
    let SourceProof::Script(tactics) = file.function_blocks()[0].grouped_proof().unwrap() else {
        panic!("expected script")
    };
    let printed = printing::format_proof_tactics(tactics).unwrap();
    assert!(printed.contains("step(Touch(second));"));
    let ProofTactic::StepContract(application) = &tactics[0] else {
        panic!("expected application")
    };
    assert_eq!(application.arguments.as_ref().unwrap()[0].name, "second");
    assert!(parser::parse(&source.replace("Touch(second)", "Touch(missing)")).is_err());
}

#[test]
fn explicit_contract_empty_application_verifies_and_expands() {
    let source = r#"verifying "invoke.c";
        contract Identity() for int32(int32 x) { ensures result == x; }
        int32 invoke(int32 (*callback)(int32), int32 x) {
            requires Identity(callback);
            ensures result == x;
        } by { step(Identity()); execute(); simp(); }
    "#;
    let c = [(
        "invoke.c",
        "int32 invoke(int32 (*callback)(int32), int32 x) { return callback(x); }",
    )];
    let verified = verify_c0_sources(source, &c).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    assert!(expanded.contains("step(Identity());"));
    verify_c0_sources(
        &source.replace("by { step(Identity()); execute(); simp(); }", &expanded),
        &c,
    )
    .unwrap();
    let error =
        verify_c0_sources(&source.replace("step(Identity())", "step(Identity)"), &c).unwrap_err();
    assert!(
        error
            .message()
            .contains("requires explicit application syntax"),
        "{}",
        error.message()
    );
}

#[test]
fn explicit_contract_application_checks_arguments_and_ownership() {
    let source = r#"verifying "invoke.c";
        resource marker() { field revision: int32; }
        resource other() { field revision: int32; }
        contract Touch(cell: marker()) for int32() { owns cell; ensures result == 0; }
        int32 invoke(int32 (*callback)()) {
            requires Touch(callback);
            owns first: marker(); owns second: other();
            ensures result == 0;
        } by { step(Touch(first)); execute(); simp(); }
    "#;
    // C0 spells the empty function-pointer parameter list `()`.
    let c = [(
        "invoke.c",
        "int32 invoke(int32 (*callback)()) { return callback(); }",
    )];
    for (application, diagnostic) in [
        ("Touch", "requires explicit application syntax"),
        ("Touch()", "expects 1 proof argument(s), got 0"),
        ("Touch(first, second)", "expects 1 proof argument(s), got 2"),
        ("Touch(second)", "expects resource `marker`, got `other`"),
    ] {
        let error =
            verify_c0_sources(&source.replace("Touch(first)", application), &c).unwrap_err();
        assert!(error.message().contains(diagnostic), "{}", error.message());
    }
    verify_c0_sources(source, &c).unwrap();
    let duplicate = source
        .replace("cell: marker()", "cell: marker(), another: marker()")
        .replace("owns cell;", "owns cell; owns another;")
        .replace("Touch(first)", "Touch(first, first)");
    let error = verify_c0_sources(&duplicate, &c).unwrap_err();
    assert!(
        error
            .message()
            .contains("cannot supply two contract proof parameters"),
        "{}",
        error.message()
    );
    let unowned = source
        .replace("owns cell;", "")
        .replace("step(Touch(first))", "step()");
    let error = verify_c0_sources(&unowned, &c).unwrap_err();
    assert!(
        error
            .message()
            .contains("requires explicit proof arguments"),
        "{}",
        error.message()
    );
}

#[test]
fn opaque_resource_call_checks_actual_c_arguments_and_call_entry_snapshots() {
    let source = r#"verifying "invoke.c";
        resource marker(p: int32*) { field revision: int32; }
        contract Touch(cell: marker(p)) for int32(int32* p) {
            owns cell;
            ensures cell.revision == 1;
            ensures result == old(cell.revision);
        }
        int32 invoke(int32 (*callback)(int32*), int32* p, int32* q) {
            requires Touch(callback);
            owns first: marker(p); owns second: marker(q);
            ensures first.revision == 1;
            ensures second.revision == old(second.revision);
            ensures result == 1;
        } by { step(Touch(first)); step(Touch(first)); execute();
            rewrite(result == at(statement(0).exit, first.revision));
            rewrite(at(statement(0).exit, first.revision) == 1); simp(); }
    "#;
    let c = [(
        "invoke.c",
        "int32 invoke(int32 (*callback)(int32*), int32* p, int32* q) { callback(p); return callback(p); }",
    )];
    let verified = verify_c0_sources(source, &c).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    verify_c0_sources(
        &source.replace(
            "by { step(Touch(first)); step(Touch(first)); execute();\n            rewrite(result == at(statement(0).exit, first.revision));\n            rewrite(at(statement(0).exit, first.revision) == 1); simp(); }",
            &expanded,
        ),
        &c,
    )
    .unwrap();
    let error =
        verify_c0_sources(&source.replace("Touch(first)", "Touch(second)"), &c).unwrap_err();
    assert!(
        error.message().contains("does not match its contract"),
        "{}",
        error.message()
    );
    assert!(!error.message().contains("AlgebraicSchemas"));
    assert!(!error.message().contains("ResourceFieldSchema"));
    assert!(!error.message().contains("diagnostic truncated"));
    assert!(
        verify_c0_sources(
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
            ensures list_length(cell.contents) == old(list_length(cell.contents));
        } by { execute(); simp(); }
    "#;
    let sources = [(
        "identity.c",
        "int32 identity(int32 value) { return value; }",
    )];
    let verified = verify_c0_sources(source, &sources).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    let expanded_source = source.replacen("by { execute(); simp(); }", &expanded, 1);
    verify_c0_sources(&expanded_source, &sources)
        .expect("expanded resource-field proof must recheck");
    for false_claim in [
        "cell.model == Mark::Clear",
        "cell.revision == 0",
        "cell.contents == List::Nil",
    ] {
        let wrong = source.replace("cell.model == old(cell.model)", false_claim);
        assert!(
            verify_c0_sources(&wrong, &sources).is_err(),
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
        int32 g() {{ ensures cell.model == Mark::Clear; }} by {{ execute(); simp(); }}"#
    );
    assert!(verify_c0_sources(&out_of_scope, &[("g.c", "int32 g(void) { return 0; }")]).is_err());
    let source = format!(
        r#"verifying "f.c"; {header}
        int32 f() {{ owns first: marked_cell(); owns second: marked_cell();
            ensures first.model == second.model;
        }} by {{ execute(); simp(); }}"#
    );
    assert!(verify_c0_sources(&source, &[("f.c", "int32 f(void) { return 0; }")]).is_err());
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
    assert!(std::sync::Arc::ptr_eq(
        first.fields.as_ref().unwrap(),
        returned.fields.as_ref().unwrap()
    ));
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
        assert!(std::sync::Arc::ptr_eq(
            binding.fields.as_ref().unwrap(),
            returned.fields.as_ref().unwrap()
        ));
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

#[test]
fn named_resource_binding_does_not_expose_its_memory_body() {
    let source = r#"verifying "read.c";
        resource cell(p: int32*) { field model: List<int32>; owns p[0..1]; }
        int32 read(int32* p) {
            owns cell: cell(p);
            ensures cell.model == old(cell.model);
        } by { execute(); simp(); }
    "#;
    assert!(
        verify_c0_sources(source, &[("read.c", "int32 read(int32* p) { return *p; }")]).is_err(),
        "binding an opaque instance must not grant its unopened memory body"
    );
}

#[test]
fn named_resource_calls_reject_missing_binder_transport() {
    let source = r#"verifying "calls.c";
        resource marker() { field revision: int32; }
        extern int32 callee() { owns cell: marker(); }
        int32 caller() {
            owns cell: marker();
            ensures cell.revision == old(cell.revision);
        } by { execute(); simp(); }
    "#;
    let error = verify_c0_sources(
        source,
        &[(
            "calls.c",
            "int32 callee(void); int32 caller(void) { return callee(); }",
        )],
    )
    .unwrap_err();
    assert!(
        error.message().contains("checked binder transport"),
        "{}",
        error.message()
    );
}

#[test]
fn resource_fields_preserve_checked_types_and_do_not_lower_to_legacy_resources() {
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
    assert!(!buffer.is_countable());
    assert_eq!(
        buffer.fields().iter().map(|f| f.name()).collect::<Vec<_>>(),
        ["contents", "mark", "revision", "origin"]
    );
    let schema = buffer.field_schema().unwrap();
    assert!(!schema.is_countable());
    assert_eq!(schema.fields().len(), 4);
    let crate::kernel::ResourceFieldType::Algebraic(ty) = &schema.fields()[0].1 else {
        panic!("expected List schema")
    };
    assert_eq!(ty.name, "List");
    assert_eq!(
        ty.arguments,
        vec![AlgebraicValueType::Algebraic {
            name: "List".into(),
            arguments: vec![AlgebraicValueType::C(CType::Int32)],
        }]
    );
    assert_eq!(
        schema.fields()[2].1,
        crate::kernel::ResourceFieldType::C(CType::Int32)
    );
    assert_eq!(
        schema.fields()[3].1,
        crate::kernel::ResourceFieldType::C(CType::Int32Pointer)
    );
    assert!(file.resource_definitions()[1].is_countable());
    let lowered = composite_resource_definitions(
        &ResourceEnvironment::new(file.resource_definitions()),
        &PredicateEnvironment::new(&[]),
        &ClickFunctionEnvironment::new(&[]),
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
        "field metadata must never be erased into a legacy composite"
    );
}

#[test]
fn resource_fields_reject_counting_and_unimplemented_instance_operations() {
    let declaration = "resource cell(p: int32*) { field model: List<int32>; owns p[0..1]; }";
    for expression in ["count(cell(p))", "List::Cons(count(cell(p)), List::Nil)"] {
        let result_type = if expression.starts_with("List") {
            "List<int32>"
        } else {
            "int32"
        };
        let source = format!(
            "function population(p: int32*) -> {result_type} {{ {expression} }} {declaration}"
        );
        assert_eq!(
            parser::parse(&source).unwrap_err().message(),
            "resource `cell` has fields and is not countable"
        );
    }
    for clause in [
        "requires count(cell(p)) == 1;",
        "requires count(cell(_)) == 1;",
        "consumes 2 of cell(p);",
        "produces 1 of cell(p);",
    ] {
        let source = format!("{declaration} int32 f(int32* p) {{ {clause} }}");
        let error = parser::parse(&source).unwrap_err();
        assert_eq!(
            error.message(),
            "resource `cell` has fields and is not countable",
            "{clause}"
        );
    }
    let nested = format!(
        "{declaration} abstract resource credit(n: int32); int32 f(int32* p) {{ consumes credit(count(cell(p))); }}"
    );
    assert_eq!(
        parser::parse(&nested).unwrap_err().message(),
        "resource `cell` has fields and is not countable"
    );
    for tactic in [
        "apply(law(count(cell(p))));",
        "witness(x = count(cell(p)));",
    ]
    .into_iter()
    {
        let source =
            format!("{declaration} int32 f(int32* p) {{ ensures result == 0 by {{ {tactic} }} }}");
        assert_eq!(
            parser::parse(&source).unwrap_err().message(),
            "resource `cell` has fields and is not countable"
        );
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
    for tactic in ["fold", "unfold", "observe", "construct"] {
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
    let source = include_str!("../../examples/modeled-binary-tree/modeled_binary_tree.click")
        .replace("verifying \"modeled_binary_tree.c\";", "");
    verify_c0_sources(&source, &[]).expect("generic tree laws should verify");
    for (from, to) in [("right", "left"), ("left", "right")] {
        let wrong_mirror = source.replacen(
            &format!("tree_mirror({from})"),
            &format!("tree_mirror({to})"),
            1,
        );
        assert!(
            verify_c0_sources(&wrong_mirror, &[]).is_err(),
            "mirroring must not duplicate the {to} subtree"
        );
    }
    let wrong_size = source.replace(
        "ensures tree_size(tree_mirror(tree)) == tree_size(tree)",
        "ensures tree_size(tree_mirror(tree)) == Nat::Succ(tree_size(tree))",
    );
    assert!(verify_c0_sources(&wrong_size, &[]).is_err());

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
    verify_c0_sources(&client, &[]).expect("tree laws should apply to nested generic payloads");
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
            requires loadable(p[0..3]);
            consumes p[0..3];
            ensures returns_second: result == 2 by auto;
        }
    "#;

fn current(expression: CExpression) -> ContractExpression {
    ContractExpression::CFragment(expression)
}

fn current_var(name: &str) -> ContractExpression {
    current(CExpression::Variable(name.to_string()))
}

fn current_int(value: u32) -> ContractExpression {
    current(CExpression::Value(int32(value)))
}

fn current_index(base: &str, index: u32) -> ContractExpression {
    ContractExpression::Index(Box::new(current_var(base)), Box::new(current_int(index)))
}

#[test]
fn contract_substitution_renames_colliding_logical_binders() {
    let proposition = ClickProposition::ForAll {
        c_type: C0Type::Int32,
        name: "i".to_string(),
        body: Box::new(ClickProposition::Comparison {
            left: current_var("argument"),
            operator: ComparisonOperator::Equal,
            right: current_var("i"),
        }),
    };
    let substitutions = BTreeMap::from([(String::from("argument"), current_var("i"))]);

    let substituted = lowering::substitute_click_proposition(&proposition, &substitutions)
        .expect("surface substitution should succeed");
    let ClickProposition::ForAll { name, body, .. } = substituted else {
        panic!("substitution should preserve the logical binder");
    };
    assert_ne!(name, "i");
    assert_eq!(
        body.as_ref(),
        &ClickProposition::Comparison {
            left: current_var("i"),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CBinding(name),
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
        accumulator: "acc".to_string(),
        item: "i".to_string(),
        body: Box::new(ContractExpression::Add(
            Box::new(current_var("argument")),
            Box::new(current_var("i")),
        )),
    };
    let let_expression = ContractExpression::Let {
        name: "i".to_string(),
        click_type: Some(ClickType::C(C0Type::Int32)),
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
        &ContractExpression::Add(
            Box::new(current_var("i")),
            Box::new(ContractExpression::CBinding(item.clone())),
        )
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
        &ContractExpression::Add(
            Box::new(current_var("i")),
            Box::new(ContractExpression::CBinding(name)),
        )
    );
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

mod contract_tests;
mod diagnostic_tests;
mod execution_tests;
mod expansion_tests;
mod loop_tests;
mod project_tests;
mod scaling_tests;
mod surface_syntax;
mod tactic_tests;
