use super::*;

const C: &str = "int read(int* p) { return *p; }";
const SOURCE: &str = r#"
verifying "read.c";
spec enum Maybe { None, Some(int) }
resource cell(p: int*) {
    field model: Maybe;
    match model {
        Maybe::None => { owns p[0..1]; fact p[0] == 0; },
        Maybe::Some(value) => { owns p[0..1]; fact p[0] == value; },
    }
}
int read(int* p) {
    owns c: cell(p);
    ensures c.model == old(c.model);
} by {
    match c.model {
        Maybe::None => { unfold(c); execute(); fold(c); simp(); },
        Maybe::Some(value) => {
            unfold(c);
            execute();
            have result == value by { simp(); }
            fold(c);
            simp();
        },
    }
}
"#;

#[test]
fn proof_match_fields_survive_function_unfold_in_have() {
    let source = SOURCE
        .replace("resource cell", "function identity(m: Maybe) -> Maybe { m }\nresource cell")
        .replace("            unfold(c);", "            have identity(Maybe::Some(value)) == Maybe::Some(value) by {\n                unfold(identity(Maybe::Some(value)));\n                normalize();\n            }\n            have Maybe::Some(value) != Maybe::None by {\n                rewrite(Maybe::Some(value) == identity(Maybe::Some(value)));\n                rewrite(identity(Maybe::Some(value)) == Maybe::Some(value));\n                normalize();\n            }\n            unfold(c);");
    let sources = [("read.c", C)];
    for source in [
        source.clone(),
        source
            .replace("Some(int)", "Some(Maybe)")
            .replace("p[0] == value", "p[0] == 0")
            .replace("result == value", "result == 0"),
    ] {
        verify_c0_sources(&source, &sources).unwrap();
        let expanded =
            expand_c0_claim_source(&source, &sources, "read", CProofClaim::Grouped).unwrap();
        verify_c0_sources(&expanded, &sources).unwrap();
        let bad = source.replace("== Maybe::Some(value) by", "== Maybe::None by");
        assert!(verify_c0_sources(&bad, &sources).is_err());
    }
}

#[test]
fn modeled_tree_rotate_left_checks_model_and_ownership() {
    let source = include_str!("../../../../examples/modeled-binary-tree/modeled_binary_tree.click");
    let c = include_str!("../../../../examples/modeled-binary-tree/modeled_binary_tree.c");
    let header = include_str!("../../../../examples/modeled-binary-tree/modeled_binary_tree.h");
    let sources = [
        ("modeled_binary_tree.c", c),
        ("modeled_binary_tree.h", header),
    ];
    verify_c0_sources(source, &sources).unwrap();
    let expanded =
        expand_c0_claim_source(source, &sources, "tree_rotate_left", CProofClaim::Grouped).unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
    for bad in [
        source.replace("    requires heap_right(t.model) != HeapTree::Empty;", ""),
        source.replace(
            "model: HeapTree::Node(node, value, left_model, middle_model)",
            "model: HeapTree::Node(node, pivot_value, left_model, middle_model)",
        ),
        source.replace("{ left: l, right: m }", "{ left: l, right: z }"),
        source.replace("{ left: l, right: m }", "{ left: l, right: l }"),
        source.replace(
            "let rotated = fold(tree_at(result)",
            "let rotated = fold(tree_at(root)",
        ),
    ] {
        assert_ne!(bad, source);
        assert!(verify_c0_sources(&bad, &sources).is_err());
    }
    // The real source stays the positive boundary; broken-store mutants must fail.
    for bad_c in [
        c.replace("root->right = middle;", "root->right = pivot;"),
        c.replace("pivot->left = root;", "pivot->left = middle;"),
    ] {
        assert_ne!(bad_c, c);
        assert!(
            verify_c0_sources(
                source,
                &[
                    ("modeled_binary_tree.c", &bad_c),
                    ("modeled_binary_tree.h", header)
                ]
            )
            .is_err()
        );
    }
}

#[test]
fn proof_match_closes_impossible_constructor_without_executing_c() {
    let source = SOURCE
        .replace(
            "Maybe::None => { owns p[0..1]; fact p[0] == 0; },",
            "Maybe::None => { fact p == 0; },",
        )
        .replace(
            "    ensures c.model",
            "    requires c.model != Maybe::None;\n    ensures c.model",
        )
        .replace(
            "Maybe::None => { unfold(c); execute(); fold(c); simp(); },",
            "Maybe::None => { contradiction(c.model == Maybe::None); },",
        );
    let sources = [("read.c", C)];
    for good in [
        source.clone(),
        source.replace(
            "enum Maybe { None, Some(int) }",
            "enum Maybe { Some(int), None }",
        ),
        source.replace("        Maybe::None => { contradiction(c.model == Maybe::None); },\n", "")
            .replace("        },\n    }\n}\n", "        },\n        Maybe::None => { contradiction(c.model == Maybe::None); },\n    }\n}\n"),
    ] {
        verify_c0_sources(&good, &sources)
            .expect("excluded arm has no memory and does not execute");
        let expanded =
            expand_c0_claim_source(&good, &sources, "read", CProofClaim::Grouped).unwrap();
        verify_c0_sources(&expanded, &sources)
            .unwrap_or_else(|error| panic!("{error:?}\n{expanded}"));
        assert!(expanded.contains("contradiction("));
        // `have` is one selectable C-proof tactic, including its nested proof.
        for offset in [good.find("execute();").unwrap(), good.find("have result").unwrap(), good.rfind("simp();").unwrap()] {
            let position = expansion::position_at_offset(&good, offset);
            let selected =
                expand_c0_tactic_source_at(&good, &sources, position.line, position.column)
                    .unwrap();
            verify_c0_sources(&selected, &sources).expect("selected live arm expansion");
        }
    }
    for bad in [
        source.replace("    requires c.model != Maybe::None;", ""),
        source.replace(
            "contradiction(c.model == Maybe::None)",
            "contradiction(p == 0)",
        ),
        source.replace(
            "contradiction(c.model == Maybe::None)",
            "contradiction(c.model == Maybe::Some(7))",
        ),
        source.replace(
            "Maybe::None => { contradiction(c.model == Maybe::None); },",
            "",
        ),
        source.replace("            fold(c);", ""),
        source.replace("have result == value", "have result == value + 1"),
    ] {
        assert!(
            verify_c0_sources(&bad, &sources).is_err(),
            "invalid exclusion or live proof accepted"
        );
    }
}

#[test]
fn proof_match_nested_impossible_arms_keep_their_scopes() {
    let source = r#"
verifying "id.c";
spec enum Tag { A, B }
resource tag() { field model: Tag; }
int id(int x) {
    owns r: tag();
    requires r.model != Tag::A;
    ensures result == x;
    ensures r.model == old(r.model);
} by {
    match r.model {
        Tag::A => { contradiction(r.model == Tag::A); },
        Tag::B => {
            match r.model {
                Tag::B => { execute(); simp(); },
                Tag::A => { contradiction(r.model == Tag::A); },
            }
        },
    }
}
"#;
    let sources = [("id.c", "int id(int x) { return x; }")];
    verify_c0_sources(source, &sources).expect("nested excluded constructors");
    let expanded = expand_c0_claim_source(source, &sources, "id", CProofClaim::Grouped).unwrap();
    verify_c0_sources(&expanded, &sources).expect("nested exclusion certificate");
}

#[test]
fn proof_match_checks_arbitrary_payload_and_rejects_invalid_arms() {
    verify_c0_sources(SOURCE, &[("read.c", C)])
        .expect("arbitrary scoped field and return-state fold");
    for (label, bad) in [
        (
            "payload",
            SOURCE.replace("have result == value", "have result == value + 1"),
        ),
        (
            "coverage",
            SOURCE.replace(
                "Maybe::None => { unfold(c); execute(); fold(c); simp(); },",
                "",
            ),
        ),
        (
            "duplicate",
            SOURCE.replace(
                "Maybe::None => { unfold(c); execute(); fold(c); simp(); },",
                "Maybe::Some(other) => { unfold(c); execute(); fold(c); simp(); },",
            ),
        ),
        (
            "arity",
            SOURCE.replace(
                "Maybe::Some(value) => {\n            unfold(c)",
                "Maybe::Some() => {\n            unfold(c)",
            ),
        ),
        ("wrong type", SOURCE.replace("match c.model {", "match p {")),
        (
            "shadow",
            SOURCE.replace(
                "Maybe::Some(value) => {\n            unfold(c)",
                "Maybe::Some(p) => {\n            unfold(c)",
            ),
        ),
        (
            "missing unfold",
            SOURCE.replacen("unfold(c); execute(); fold(c)", "execute(); fold(c)", 1),
        ),
        ("missing fold", SOURCE.replace("            fold(c);", "")),
        (
            "sibling scope",
            SOURCE.replace(
                "Maybe::None => { unfold(c);",
                "Maybe::None => { have value == 0 by { simp(); } unfold(c);",
            ),
        ),
    ] {
        assert!(
            verify_c0_sources(&bad, &[("read.c", C)]).is_err(),
            "accepted invalid match: {label}"
        );
    }
}

#[test]
fn proof_match_expands_and_rechecks() {
    let sources = [("read.c", C)];
    verify_c0_sources(SOURCE, &sources).unwrap();
    let expanded = expand_c0_claim_source(SOURCE, &sources, "read", CProofClaim::Grouped).unwrap();
    assert!(expanded.contains("match c.model"), "{expanded}");
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!("expanded constructor proof rechecks: {error:?}\n{expanded}")
    });
    for offset in [
        SOURCE.find("execute();").unwrap(),
        SOURCE.find("simp();").unwrap(),
        SOURCE.rfind("simp();").unwrap(),
    ] {
        let position = expansion::position_at_offset(SOURCE, offset);
        let selected =
            expand_c0_tactic_source_at(SOURCE, &sources, position.line, position.column).unwrap();
        verify_c0_sources(&selected, &sources).expect("selected match-arm expansion rechecks");
    }
}

#[test]
fn proof_match_int64_payloads_are_typed() {
    let source = SOURCE.replace("int", "int64");
    let c = C.replace("int", "int64");
    verify_c0_sources(&source, &[("read.c", c.as_str())]).expect("64-bit constructor witness");
}

#[test]
fn proof_match_compound_scrutinee_expansion_rechecks() {
    let source = r#"
verifying "read.c";
spec enum Maybe { None, Some(int) }
resource model() { field value: Maybe; }
int read(int x) {
    owns c: model();
    ensures result == x;
} by {
    match (match c.value { Maybe::None => Maybe::None, Maybe::Some(v) => Maybe::Some(v) }) {
        Maybe::None => { execute(); simp(); },
        Maybe::Some(value) => { execute(); simp(); },
    }
}
"#;
    let sources = [("read.c", "int read(int x) { return x; }")];
    for source in [
        source.to_owned(),
        source
            .replace("match (match", "match match")
            .replace(" }) {", " } {"),
    ] {
        verify_c0_sources(&source, &sources).expect("compound symbolic scrutinee");
        let offset = source.find("execute();").unwrap();
        let position = expansion::position_at_offset(&source, offset);
        let expanded =
            expand_c0_tactic_source_at(&source, &sources, position.line, position.column).unwrap();
        verify_c0_sources(&expanded, &sources).expect("compound scrutinee expansion");
    }
}

#[test]
fn proof_match_nested_generic_fields_and_repeated_values() {
    let source = r#"
verifying "id.c";
spec enum Items<T> { Nil, Cons(T, Items<T>) }
resource list_model() { field model: Items<int>; }
int id(int x) {
    owns list: list_model();
    ensures result == x;
    ensures list.model == old(list.model);
} by {
    match list.model {
        Items::Nil => { step(); simp(); },
        Items::Cons(head, tail) => {
            match tail {
                Items::Nil => { step(); simp(); },
                Items::Cons(next, rest) => { step(); simp(); },
            }
        },
    }
}
"#;
    let c = [("id.c", "int id(int x) { return x; }")];
    verify_c0_sources(source, &c).expect("nested generic ADT fields stay symbolic");
    verify_c0_sources(&source.replace("match tail {", "match list.model {"), &c)
        .expect("repeated matching gets fresh witnesses, not a second model");
    let expanded = expand_c0_claim_source(source, &c, "id", CProofClaim::Grouped).unwrap();
    verify_c0_sources(&expanded, &c).expect("nested match certificate");
}
