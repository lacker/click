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
        Maybe::None => { unfold(c); step_until(function.exit); fold(c); close(); },
        Maybe::Some(value) => {
            unfold(c);
            step_until(function.exit);
            have result == value by { close(); }
            fold(c);
            close();
        },
    }
}
"#;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn proof_match_fields_survive_function_unfold_in_have() {
    let source = SOURCE
        .replace("resource cell", "function identity(m: Maybe) -> Maybe { m }\nresource cell")
        .replace("            unfold(c);", "            have identity(Maybe::Some(value)) == Maybe::Some(value) by {\n                unfold(identity(Maybe::Some(value)));\n                normalize();\n            }\n            have Maybe::Some(value) != Maybe::None by {\n                rewrite(Maybe::Some(value), identity(Maybe::Some(value)));\n                rewrite(identity(Maybe::Some(value)), Maybe::Some(value));\n                normalize();\n            }\n            unfold(c);");
    let sources = [("read.c", C)];
    for source in [
        source.clone(),
        source
            .replace("Some(int)", "Some(Maybe)")
            .replace("p[0] == value", "p[0] == 0")
            .replace("result == value", "result == 0"),
    ] {
        verify_c_sources(&source, &sources).unwrap();
        let expanded =
            expand_c_claim_source(&source, &sources, "read", ContractProofClaim::Grouped).unwrap();
        verify_c_sources(&expanded, &sources).unwrap();
        let bad = source.replace("== Maybe::Some(value) by", "== Maybe::None by");
        assert!(verify_c_sources(&bad, &sources).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 12s in the parallel gate"]
fn modeled_tree_rotate_left_checks_model_and_ownership() {
    let source = include_str!("../../../../examples/modeled-binary-tree/modeled_binary_tree.click");
    let c = include_str!("../../../../examples/modeled-binary-tree/modeled_binary_tree.c");
    let header = include_str!("../../../../examples/modeled-binary-tree/modeled_binary_tree.h");
    let sources = [
        ("modeled_binary_tree.c", c),
        ("modeled_binary_tree.h", header),
    ];
    verify_c_sources(source, &sources).unwrap();
    let expanded = expand_c_claim_source(
        source,
        &sources,
        "tree_rotate_left",
        ContractProofClaim::Grouped,
    )
    .unwrap();
    super::super::expansion_tests::assert_only_function_proof_changed(
        source,
        &expanded,
        "tree_rotate_left",
    );
    let checked = crate::surface::verify_c_sources_functions(
        &expanded,
        &sources,
        ["tree_rotate_left".to_string()],
    )
    .unwrap();
    assert!(!checked.is_empty());
    assert!(
        checked
            .iter()
            .all(|proof| proof.function_block.signature().name() == "tree_rotate_left")
    );
    // This mutation changes a pure theorem, so retain its full-project check.
    let bad_theorem = source.replace(
        "ensures heap_inorder(heap_rotate_left(tree)) == heap_inorder(tree) by",
        "ensures heap_inorder(heap_rotate_left(tree)) == List<struct tree_node*>::Nil by",
    );
    assert_ne!(bad_theorem, source);
    assert!(verify_c_sources(&bad_theorem, &sources).is_err());
    // Other mutants change only rotation contracts/bodies. Check both complete
    // rotations because their identical postcondition is mutated together.
    let outside_rotations = |text: &str| {
        let mut ranges = ["tree_rotate_left", "tree_rotate_right"].map(|function| {
            let signature = format!(" {function}(");
            assert_eq!(text.matches(&signature).count(), 1);
            let start = text.find(&signature).unwrap();
            let body = start + text[start..].find("} by {").unwrap() + "} by {".len();
            let end = body + text[body..].find("\n}").unwrap() + "\n}".len();
            (start, end)
        });
        ranges.sort_unstable();
        format!(
            "{}{}{}",
            &text[..ranges[0].0],
            &text[ranges[0].1..ranges[1].0],
            &text[ranges[1].1..]
        )
    };
    let outside = outside_rotations(source);
    for bad in [
        source.replace(
            "ensures heap_inorder(rotated.model) == heap_inorder(old(t.model));",
            "ensures heap_inorder(rotated.model) == list::append(heap_inorder(old(t.model)), List<struct tree_node*>::Cons(root, List<struct tree_node*>::Nil));",
        ),
        source.replace("    requires heap_right(t.model) != HeapTree::Empty;", ""),
        source.replace(
            "model: HeapTree::Node(node, value, left_model, middle_model)",
            "model: HeapTree::Node(node, pivot_value, left_model, middle_model)",
        ),
        // Fold the lower node with a wrong right child: the pivot's right
        // child, or the root's own left child.
        source.replace("right: m,", "right: right,"),
        source.replace("right: m,", "right: left,"),
        source.replace(
            "let rotated = fold(tree_at(result)",
            "let rotated = fold(tree_at(root)",
        ),
    ] {
        assert_ne!(bad, source);
        assert_eq!(outside_rotations(&bad), outside);
        assert!(crate::surface::verify_c_sources_functions(
            &bad, &sources, ["tree_rotate_left".to_string(), "tree_rotate_right".to_string()],
        ).is_err());
    }
    // The real source stays the positive boundary; broken-store mutants must fail.
    for bad_c in [
        c.replace("root->right = middle;", "root->right = pivot;"),
        c.replace("pivot->left = root;", "pivot->left = middle;"),
    ] {
        assert_ne!(bad_c, c);
        // Only the left rotation's C body changes. The complete original
        // example was checked above; every other C byte and the full sidecar
        // stay identical, so make the mutated function itself reject.
        let text_span = |text: &str| {
            let signature = "struct tree_node *tree_rotate_left(";
            assert_eq!(text.matches(signature).count(), 1);
            let start = text.find(signature).unwrap();
            let body = start + text[start..].find('{').unwrap() + 1;
            let end = body + text[body..].find("\n}").unwrap() + "\n}".len();
            (body, end)
        };
        let (before_body, before_end) = text_span(c);
        let (after_body, after_end) = text_span(&bad_c);
        assert_eq!(&c[..before_body], &bad_c[..after_body]);
        assert_eq!(&c[before_end..], &bad_c[after_end..]);
        assert!(
            crate::surface::verify_c_sources_functions(
                source,
                &[
                    ("modeled_binary_tree.c", &bad_c),
                    ("modeled_binary_tree.h", header)
                ],
                ["tree_rotate_left".to_string()],
            )
            .is_err()
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
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
            "Maybe::None => { unfold(c); step_until(function.exit); fold(c); close(); },",
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
        verify_c_sources(&good, &sources)
            .expect("excluded arm has no memory and does not execute");
        let expanded =
            expand_c_claim_source(&good, &sources, "read", ContractProofClaim::Grouped).unwrap();
        verify_c_sources(&expanded, &sources)
            .unwrap_or_else(|error| panic!("{error:?}\n{expanded}"));
        assert!(expanded.contains("contradiction("));
        // `have` is one selectable C-proof tactic, including its nested proof.
        for offset in [good.find("step_until(function.exit);").unwrap(), good.find("have result").unwrap(), good.rfind("close();").unwrap()] {
            let position = expansion::position_at_offset(&good, offset);
            let selected =
                expand_c_tactic_source_at(&good, &sources, position.line, position.column)
                    .unwrap();
            verify_c_sources(&selected, &sources).expect("selected live arm expansion");
        }
    }
    // The live arm's solve may reconstruct the omitted resource fold.
    verify_c_sources(&source.replace("            fold(c);", ""), &sources)
        .expect("the live arm may refold implicitly");
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
        source.replace(
            "            fold(c);",
            "            let c = fold(cell(p), { model: Maybe::None });",
        ),
        source.replace("have result == value", "have result == value + 1"),
    ] {
        assert!(
            verify_c_sources(&bad, &sources).is_err(),
            "invalid exclusion or live proof accepted"
        );
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by proof_match_batch_00")]
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
                Tag::B => { step_until(function.exit); close(); },
                Tag::A => { contradiction(r.model == Tag::A); },
            }
        },
    }
}
"#;
    let sources = [("id.c", "int id(int x) { return x; }")];
    verify_c_sources(source, &sources).expect("nested excluded constructors");
    let expanded =
        expand_c_claim_source(source, &sources, "id", ContractProofClaim::Grouped).unwrap();
    verify_c_sources(&expanded, &sources).expect("nested exclusion certificate");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn proof_match_checks_arbitrary_payload_and_rejects_invalid_arms() {
    verify_c_sources(SOURCE, &[("read.c", C)])
        .expect("arbitrary scoped field and return-state fold");
    verify_c_sources(
        &SOURCE.replace("            fold(c);", ""),
        &[("read.c", C)],
    )
    .expect("solve may refold the Some resource from its retained body");
    for (label, bad) in [
        (
            "payload",
            SOURCE.replace("have result == value", "have result == value + 1"),
        ),
        (
            "coverage",
            SOURCE.replace(
                "Maybe::None => { unfold(c); step_until(function.exit); fold(c); close(); },",
                "",
            ),
        ),
        (
            "duplicate",
            SOURCE.replace(
                "Maybe::None => { unfold(c); step_until(function.exit); fold(c); close(); },",
                "Maybe::Some(other) => { unfold(c); step_until(function.exit); fold(c); close(); },",
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
            SOURCE.replacen("unfold(c); step_until(function.exit); fold(c)", "step_until(function.exit); fold(c)", 1),
        ),
        (
            "wrong fold model",
            SOURCE.replace(
                "            fold(c);",
                "            let c = fold(cell(p), { model: Maybe::None });",
            ),
        ),
        (
            "sibling scope",
            SOURCE.replace(
                "Maybe::None => { unfold(c);",
                "Maybe::None => { have value == 0 by { close(); } unfold(c);",
            ),
        ),
    ] {
        assert!(
            verify_c_sources(&bad, &[("read.c", C)]).is_err(),
            "accepted invalid match: {label}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn proof_match_expands_and_rechecks() {
    let sources = [("read.c", C)];
    verify_c_sources(SOURCE, &sources).unwrap();
    let expanded =
        expand_c_claim_source(SOURCE, &sources, "read", ContractProofClaim::Grouped).unwrap();
    assert!(expanded.contains("match c.model"), "{expanded}");
    verify_c_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!("expanded constructor proof rechecks: {error:?}\n{expanded}")
    });
    for offset in [
        SOURCE.find("step_until(function.exit);").unwrap(),
        SOURCE.find("close();").unwrap(),
        SOURCE.rfind("close();").unwrap(),
    ] {
        let position = expansion::position_at_offset(SOURCE, offset);
        let selected =
            expand_c_tactic_source_at(SOURCE, &sources, position.line, position.column).unwrap();
        verify_c_sources(&selected, &sources).expect("selected match-arm expansion rechecks");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by proof_match_batch_00")]
fn proof_match_int64_payloads_are_typed() {
    let source = SOURCE.replace("int", "int64");
    let c = C.replace("int", "int64");
    verify_c_sources(&source, &[("read.c", c.as_str())]).expect("64-bit constructor witness");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by proof_match_batch_00")]
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
        Maybe::None => { step_until(function.exit); close(); },
        Maybe::Some(value) => { step_until(function.exit); close(); },
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
        verify_c_sources(&source, &sources).expect("compound symbolic scrutinee");
        let offset = source.find("step_until(function.exit);").unwrap();
        let position = expansion::position_at_offset(&source, offset);
        let expanded =
            expand_c_tactic_source_at(&source, &sources, position.line, position.column).unwrap();
        verify_c_sources(&expanded, &sources).expect("compound scrutinee expansion");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by proof_match_batch_00")]
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
        Items::Nil => { step(); close(); },
        Items::Cons(head, tail) => {
            match tail {
                Items::Nil => { step(); close(); },
                Items::Cons(next, rest) => { step(); close(); },
            }
        },
    }
}
"#;
    let c = [("id.c", "int id(int x) { return x; }")];
    verify_c_sources(source, &c).expect("nested generic ADT fields stay symbolic");
    verify_c_sources(&source.replace("match tail {", "match list.model {"), &c)
        .expect("repeated matching gets fresh witnesses, not a second model");
    let expanded = expand_c_claim_source(source, &c, "id", ContractProofClaim::Grouped).unwrap();
    verify_c_sources(&expanded, &c).expect("nested match certificate");
}

#[cfg(feature = "fast-gate")]
test_batches! {
    file: "proof_match.rs",
    marker: "proof_match_batch_",
    proof_match_batch_00: [
        proof_match_nested_impossible_arms_keep_their_scopes,
        proof_match_int64_payloads_are_typed,
        proof_match_compound_scrutinee_expansion_rechecks,
        proof_match_nested_generic_fields_and_repeated_values,
    ],
}
