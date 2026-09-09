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
