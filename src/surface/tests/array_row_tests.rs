use super::*;

const ORIGINAL_ROWS: &str = r#"
struct Rows { int values[2][3]; };
int probe(void) {
    struct Rows p = {{{1, 2, 3}, {4, 5, 6}}};
    int *q = &p.values[0][0];
    return q[3];
}
int control(void) {
    struct Rows p = {{{1, 2, 3}, {4, 5, 6}}};
    return p.values[1][0];
}
"#;

#[test]
fn c_array_rows_reject_original_sibling_read_and_recheck_original_control() {
    let positive = r#"verifying "row.c";
        int control() { ensures result == 4; } by { execute(); simp(); }"#;
    let sources = [("row.c", ORIGINAL_ROWS)];
    let verified = verify_c0_sources(positive, &sources).unwrap();
    verified[0]
        .expanded_proof_certificate()
        .expect("the selected row proof retains its checking certificate");
    let expanded =
        expand_c0_claim_source_by_label(positive, &sources, "control.ensures_0").unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
    let (session, _) = C0VerificationSession::new(positive, &sources).unwrap();
    let claim = expansion::position_at_offset(&expanded, expanded.find("ensures").unwrap());
    session
        .verify_at(&expanded, claim.line, claim.column)
        .unwrap();
    let negative = r#"verifying "row.c";
        int probe() { ensures result == 4; } by { execute(); simp(); }"#;
    let error = verify_c0_sources(negative, &sources).unwrap_err();
    assert!(
        error.message().contains("invalid memory access"),
        "{error:?}"
    );
}

#[test]
fn c_array_row_one_past_forms_but_equal_next_row_does_not_widen_access() {
    let c = r#"struct Rows { int values[2][3]; };
        int endpoint(void) {
            struct Rows p = {{{1,2,3},{4,5,6}}};
            int *q = &p.values[0][0];
            return q + 3 == &p.values[1][0];
        }"#;
    let proof = r#"verifying "row.c";
        int endpoint() { ensures result == 1; } by { execute(); simp(); }"#;
    verify_c0_sources(proof, &[("row.c", c)]).unwrap();
    for body in [
        "return q[3];",
        "int *next = q + 3; return *next;",
        "return q + 4 == &p.values[1][1];",
        "int *cast = (int *)(void *)q; return cast[3];",
        "struct Holder { int *pointer; }; struct Holder h = {q}; return h.pointer[3];",
    ] {
        let c = format!(
            "struct Rows {{ int values[2][3]; }}; int endpoint(void) {{ struct Rows p = {{{{1,2,3}},{{4,5,6}}}}; int *q = &p.values[0][0]; {body} }}"
        );
        assert!(
            verify_c0_sources(proof, &[("row.c", c.as_str())]).is_err(),
            "accepted {body}"
        );
    }
}

#[test]
fn c_global_static_nested_rows_and_pointer_recipes_preserve_declared_extent() {
    for prefix in [
        "const int values[2][3] = {{1,2,3},{4,5,6}}; const int *const saved = &values[0][0];",
        "struct Inner { int values[2][3]; }; struct Outer { int tag; struct Inner inner; }; const struct Outer outer = {0, {{{1,2,3},{4,5,6}}}}; const int *const saved = &outer.inner.values[0][0];",
    ] {
        let proof =
            r#"verifying "row.c"; int probe() { ensures result == 4; } by { execute(); simp(); }"#;
        let negative = format!("{prefix} int probe(void) {{ return saved[3]; }}");
        let error = verify_c0_sources(proof, &[("row.c", negative.as_str())]).unwrap_err();
        assert!(
            error.message().contains("invalid memory access"),
            "{error:?}"
        );
        let positive = if prefix.contains("struct Inner") {
            format!("{prefix} int probe(void) {{ return outer.inner.values[1][0]; }}")
        } else {
            format!("{prefix} int probe(void) {{ return values[1][0]; }}")
        };
        verify_c0_sources(proof, &[("row.c", positive.as_str())]).unwrap();
    }
    let proof =
        r#"verifying "row.c"; int probe() { ensures result == 4; } by { execute(); simp(); }"#;
    let positive = "int probe(void) { static const int values[2][3] = {{1,2,3},{4,5,6}}; return values[1][0]; }";
    verify_c0_sources(proof, &[("row.c", positive)]).unwrap();
    let negative = "int probe(void) { static const int values[2][3] = {{1,2,3},{4,5,6}}; static const int *const saved = &values[0][0]; return saved[3]; }";
    let error = verify_c0_sources(proof, &[("row.c", negative)]).unwrap_err();
    assert!(
        error.message().contains("invalid memory access"),
        "{error:?}"
    );
}

#[test]
fn c_array_row_copy_and_modular_pointer_forwarding_keep_the_selected_row() {
    let c = r#"struct Rows { int values[2][3]; };
        int *identity(int *p) { return p; }
        int use(void) {
            struct Rows original = {{{1,2,3},{4,5,6}}};
            struct Rows copy = original;
            int *p = identity(&copy.values[0][0]);
            return p[2] + copy.values[1][0];
        }"#;
    let proof = r#"verifying "row.c";
        int* identity(int* p) { views p[0..3]; ensures result == p; } by { execute(); simp(); }
        int use() { ensures result == 7; } by { execute(); simp(); }"#;
    verify_c0_sources(proof, &[("row.c", c)]).unwrap();
    let expanded =
        expand_c0_claim_source_by_label(proof, &[("row.c", c)], "use.ensures_0").unwrap();
    verify_c0_sources(&expanded, &[("row.c", c)]).unwrap();
    let negative = c.replace("p[2] + copy.values[1][0]", "p[3] + copy.values[1][0]");
    assert!(verify_c0_sources(proof, &[("row.c", negative.as_str())]).is_err());
}

#[test]
fn c_array_row_unsigned_indices_keep_their_native_bounds() {
    let c = "int read(unsigned i) { int values[2][3] = {{7,7,7},{7,7,7}}; return values[i][0]; }";
    let proof = r#"verifying "row.c"; int read(uint32 i) {
        requires i < 2u32; ensures result == 7;
    } by {
        if i == 0u32 { execute(); simp(); }
        else { have i == 1u32 by simp; execute(); simp(); }
    }"#;
    verify_c0_sources(proof, &[("row.c", c)]).unwrap();
    let invalid = proof.replace("i < 2u32", "i == 2u32");
    assert!(verify_c0_sources(&invalid, &[("row.c", c)]).is_err());
}
