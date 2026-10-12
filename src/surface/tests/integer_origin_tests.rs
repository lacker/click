use super::*;

fn verify_round_trip_with_expansion_and_retention(c: &str, result_type: &str, expected: &str) {
    let source = format!(
        "verifying \"origin.c\"; {result_type} probe() {{ ensures result == {expected}; }} by {{ execute(); simp(); }}"
    );
    let sources = [("origin.c", c)];
    let verified = verify_c0_sources(&source, &sources).unwrap();
    verified[0]
        .expanded_proof_certificate()
        .expect("the genuine integer round trip retains checked evidence");
    let expanded = expand_c0_claim_source_by_label(&source, &sources, "probe.ensures_0").unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
    let (session, _) = C0VerificationSession::new(&source, &sources).unwrap();
    let position = expansion::position_at_offset(&expanded, expanded.find("ensures").unwrap());
    session
        .verify_at(&expanded, position.line, position.column)
        .unwrap();
}

fn assert_origin_read_refused(c: &str) {
    let source = r#"verifying "origin.c";
        int probe() { ensures result == 7; } by { execute(); simp(); }"#;
    let error = match verify_c0_sources(source, &[("origin.c", c)]) {
        Err(error) => error,
        Ok(_) => panic!("an invalid pointer-origin read was accepted"),
    };
    assert!(
        error.message().contains("invalid memory access")
            || error.message().contains("integer-to-pointer cast requires"),
        "the original read must refuse its carrier or access, not an unrelated proof step: {error:?}"
    );
}

#[test]
fn integer_origin_genuine_full_width_round_trip_rechecks_expanded_and_retained() {
    let c = r#"int probe(void) {
        int value = 7;
        unsigned long word = (unsigned long)&value;
        int *restored = (int *)word;
        return *restored;
    }"#;
    verify_round_trip_with_expansion_and_retention(c, "int", "7");
}

#[test]
fn integer_origin_signed_word_and_unsigned_conversion_preserve_origin() {
    for declaration in [
        "long word = (long)&value;",
        "unsigned long word = (unsigned long)(long)&value;",
    ] {
        let c =
            format!("int probe(void) {{ int value = 7; {declaration} return *((int *)word); }}");
        verify_round_trip_with_expansion_and_retention(&c, "int", "7");
    }
}

#[test]
fn integer_origin_full_width_word_store_and_load_preserve_the_carrier() {
    let c = r#"struct Word { unsigned long bits; };
        int probe(void) {
            int value = 7;
            struct Word stored = {0};
            stored.bits = (unsigned long)&value;
            unsigned long loaded = stored.bits;
            return *((int *)loaded);
        }"#;
    verify_round_trip_with_expansion_and_retention(c, "int", "7");
}

#[test]
fn integer_origin_low_tag_or_and_add_retain_only_the_genuine_origin() {
    for expression in [
        "((unsigned long)&value | 1UL) & ~1UL",
        "((unsigned long)&value + 1UL) - 1UL",
        "((unsigned long)&value ^ 1UL) ^ 1UL",
    ] {
        let c = format!(
            "unsigned long probe(void) {{ unsigned long value = 7; unsigned long word = {expression}; return *((unsigned long *)word); }}"
        );
        verify_round_trip_with_expansion_and_retention(&c, "uint64", "7u64");
    }
}

#[test]
fn integer_origin_numeric_identity_operations_cannot_recreate_discarded_origin() {
    for expression in ["word * 1UL", "word / 1UL", "word << 0", "word | word"] {
        let c = format!(
            "int probe(void) {{ int value = 7; unsigned long word = (unsigned long)&value; return *((int *)({expression})); }}"
        );
        assert_origin_read_refused(&c);
    }
}

#[test]
fn integer_origin_round_trip_does_not_rebase_an_equal_address_sibling_or_row() {
    for c in [
        // The scalar endpoint equals the next member's address. Restoring the
        // integer retains the first scalar's one-past designation.
        "struct Pair { int first; int second; }; int probe(void) { struct Pair pair = {1,7}; unsigned long word = (unsigned long)(&pair.first + 1); return *((int *)word); }",
        // The first row's endpoint equals the second row's first element,
        // whose initialized value and ownership cannot enlarge the first row.
        "struct Rows { int values[2][3]; }; int probe(void) { struct Rows rows = {{{1,2,3},{7,8,9}}}; unsigned long word = (unsigned long)(&rows.values[0][0] + 3); return *((int *)word); }",
    ] {
        assert_origin_read_refused(c);
    }
}

#[test]
fn integer_origin_one_past_survives_full_width_storage_without_becoming_readable() {
    let c = r#"struct Word { unsigned long bits; };
        int probe(void) {
            int values[1] = {7};
            struct Word stored = {(unsigned long)(values + 1)};
            return *((int *)stored.bits);
        }"#;
    assert_origin_read_refused(c);
}

#[test]
fn integer_origin_numeric_equations_and_forged_words_cannot_supply_a_carrier() {
    // This adds a no-origin scalar control; the existing sibling-equation
    // regression remains unchanged in execution_tests.rs.
    let c = "int probe(unsigned long word, int *p) { return *((int *)word); }";
    let source = r#"verifying "origin.c";
        int probe(uint64 word, int* p) {
            views p[0..1];
            requires word == address(p);
            ensures result == p[0];
        } by { execute(); simp(); }"#;
    let error = verify_c0_sources(source, &[("origin.c", c)]).unwrap_err();
    assert!(
        error.message().contains("invalid memory access")
            || error.message().contains("integer-to-pointer cast requires"),
        "{error:?}"
    );
    assert_origin_read_refused(
        "int probe(void) { unsigned long word = 4096UL; return *((int *)word); }",
    );
}

#[test]
fn integer_origin_partial_same_byte_overwrite_cannot_restore_full_width_evidence() {
    let c = r#"struct Word { unsigned long bits; };
        int probe(void) {
            int value = 7;
            struct Word stored = {(unsigned long)&value};
            unsigned char *bytes = (unsigned char *)(void *)&stored.bits;
            bytes[0] = bytes[0];
            return *((int *)stored.bits);
        }"#;
    assert_origin_read_refused(c);
}

#[test]
fn integer_origin_retains_ended_automatic_lifetime_instead_of_recreating_storage() {
    let c = r#"int probe(void) {
        unsigned long word;
        {
            int value = 7;
            word = (unsigned long)&value;
        }
        return *((int *)word);
    }"#;
    assert_origin_read_refused(c);
}

#[test]
fn lexical_scope_live_access_and_return_recheck_expanded_and_retained() {
    for c in [
        "int probe(void) { int value = 0; { int inner = 7; value = *(&inner); } return value; }",
        "int probe(void) { { int inner = 7; return *(&inner); } }",
    ] {
        verify_round_trip_with_expansion_and_retention(c, "int", "7");
    }
}

#[test]
fn lexical_scope_branch_returns_recheck_expanded_and_retained() {
    let c =
        "int probe(int flag) { { int value = 7; if (flag) return *(&value); return *(&value); } }";
    let source = r#"verifying "origin.c";
        int probe(int flag) { ensures result == 7; } by { execute(); simp(); }"#;
    let sources = [("origin.c", c)];
    let verified = verify_c0_sources(source, &sources).unwrap();
    verified[0].expanded_proof_certificate().unwrap();
    let expanded = expand_c0_claim_source_by_label(source, &sources, "probe.ensures_0").unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
    let (session, _) = C0VerificationSession::new(source, &sources).unwrap();
    let position = expansion::position_at_offset(&expanded, expanded.find("ensures").unwrap());
    session
        .verify_at(&expanded, position.line, position.column)
        .unwrap();
}

#[test]
fn lexical_scope_loop_break_and_continue_keep_outer_locals_live() {
    for c in [
        "int probe(void) { { int outer = 7; while (1) { { int inner = 1; outer += inner - 1; break; } } return *(&outer); } }",
        "int probe(void) { { int outer = 7; int count = 0; while (count < 2) { { int inner = 1; count += inner; continue; } } return *(&outer); } }",
    ] {
        verify_round_trip_with_expansion_and_retention(c, "int", "7");
    }
}

#[test]
fn lexical_scope_forward_goto_rechecks_its_exact_retirement() {
    verify_round_trip_with_expansion_and_retention(
        "int probe(void) { int outer = 7; { int inner = 1; outer += inner - 1; goto done; } done: return *(&outer); }",
        "int",
        "7",
    );
}

#[test]
fn lexical_scope_abrupt_exit_does_not_revive_nested_integer_origin() {
    for c in [
        "int probe(void) { unsigned long word; while (1) { { int inner = 7; word = (unsigned long)&inner; break; } } return *((int *)word); }",
        "int probe(void) { unsigned long word; int count = 0; while (count < 1) { { int inner = 7; word = (unsigned long)&inner; count += 1; continue; } } return *((int *)word); }",
        "int probe(void) { unsigned long word; { int inner = 7; word = (unsigned long)&inner; goto done; } done: return *((int *)word); }",
    ] {
        assert_origin_read_refused(c);
    }
}
